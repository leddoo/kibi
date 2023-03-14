use raqote::{DrawTarget, SolidSource};
use fontdue::Font;
use fontdue::layout::*;
use lru::LruCache;
use ordered_float::NotNan;


pub struct Renderer {
    target: DrawTarget,
    fonts:  [Font; 1],
    glyphs: LruCache<(u16, NotNan<f32>), (fontdue::Metrics, Vec<u8>)>,
}

impl Renderer {
    pub fn new() -> Renderer {
        let font_data = include_bytes!("../res/SourceCodePro-Regular.ttf") as &[u8];
        let font = Font::from_bytes(font_data, Default::default()).unwrap();

        Renderer {
            target: DrawTarget::new(1, 1),
            fonts:  [font],
            glyphs: LruCache::new(128.try_into().unwrap()),
        }
    }

    pub fn data(&self) -> &[u32] {
        self.target.get_data()
    }

    pub fn set_size(&mut self, w: u32, h: u32) {
        self.target = DrawTarget::new(w as i32, h as i32);
    }


    pub fn clear(&mut self, r: u8, g: u8, b: u8) {
        self.target.clear(SolidSource { r, g, b, a: 255 });
    }

    pub fn draw_text(&mut self, text: &str, x: f32, y: f32, size: f32, r: u8, b: u8, g: u8, a: u8) {
        let mut layout = Layout::new(CoordinateSystem::PositiveYDown);
        layout.append(&self.fonts, &TextStyle::new(text, size, 0));

        for glyph in layout.glyphs() {
            let glyph_index = glyph.key.glyph_index;
            let (metrics, coverage) = 
                self.glyphs.get_or_insert((glyph_index, NotNan::new(size).unwrap()), || {
                    self.fonts[0].rasterize_indexed(glyph_index, size)
                });

            let gx = glyph.x as i32;
            let gy = glyph.y as i32;
            let gw = metrics.width;
            let gh = metrics.height;

            let x0 = x as i32 + gx;
            let y0 = y as i32 + gy;
            let x1 = x0 + gw as i32;
            let y1 = y0 + gh as i32;

            let w = self.target.width();
            let h = self.target.height();
            let buf = self.target.get_data_mut();

            let x0c = x0.clamp(0, w);
            let y0c = y0.clamp(0, h);
            let x1c = x1.clamp(0, w);
            let y1c = y1.clamp(0, h);


            // taken from swcomposite, cause i ain't adding an explicit dependency for one function.
            // this is an approximation of true 'over' that does a division by 256 instead
            // of 255. It is the same style of blending that Skia does. It corresponds 
            // to Skia's SKPMSrcOver
            #[inline(always)]
            pub fn over(src: u32, dst: u32) -> u32 {
                let a = src >> 24;
                let a = 256 - a;
                let mask = 0xff00ff;
                let rb = ((dst & 0xff00ff) * a) >> 8;
                let ag = ((dst >> 8) & 0xff00ff) * a;
                src + (rb & mask) | (ag & !mask)
            }

            for y in y0c..y1c {
                for x in x0c..x1c {
                    let cx = (x - x0) as usize;
                    let cy = (y - y0) as usize;
                    let c  = coverage[cy*gw + cx];
                    let a  = (a as u32) * (c as u32) >> 8;
                    let r  = a * (r as u32) >> 8;
                    let g  = a * (g as u32) >> 8;
                    let b  = a * (b as u32) >> 8;
                    let src = a << 24 | r << 16 | g << 8 | b;

                    let value = &mut buf[(y*w + x) as usize];
                    *value = over(src, *value);
                }
            }
        }
    }
}

