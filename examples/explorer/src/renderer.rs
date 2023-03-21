use std::rc::Rc;
use core::cell::RefCell;
use raqote::DrawTarget;
use fontdue::Font;
use lru::LruCache;
use ordered_float::NotNan;


pub struct Renderer {
    target: DrawTarget,
    fonts:  FontCtx,
}

impl Renderer {
    pub fn new(fonts: &FontCtx) -> Renderer {
        Renderer {
            target: DrawTarget::new(1, 1),
            fonts:  fonts.clone(),
        }
    }

    #[allow(dead_code)] // @temp
    #[inline(always)]
    pub fn fonts(&self) -> &FontCtx { &self.fonts }


    #[inline(always)]
    pub fn data(&self) -> &[u32] { self.target.get_data() }

    #[inline(always)]
    pub fn width(&self) -> i32 { self.target.width() }

    #[inline(always)]
    pub fn height(&self) -> i32 { self.target.height() }


    pub fn set_size(&mut self, w: u32, h: u32) {
        if w as i32 != self.target.width() || h as i32 != self.target.height() {
            self.target = DrawTarget::new(w as i32, h as i32);
        }
    }


    pub fn fill_rect_abs_opaque(&mut self, x0: i32, y0: i32, x1: i32, y1: i32, color: u32) {
        let tw = self.target.width();
        let th = self.target.height();

        let x0 = x0.clamp(0, tw) as usize;
        let y0 = y0.clamp(0, th) as usize;
        let x1 = x1.clamp(0, tw) as usize;
        let y1 = y1.clamp(0, th) as usize;

        if x0 == x1 || y0 == y1 { return }

        let buf  = self.target.get_data_mut();
        let base = buf.as_mut_ptr();

        let mut offset = y0 * tw as usize;
        for _ in y0..y1 {
            let mut x = x0;

            let offset_ptr = unsafe { base.add(offset) };

            let x1_8 = x0 + ((x1 - x0) & !(8 - 1));
            while x < x1_8 { unsafe {
                // this is for fast drawing in debug mode.
                // deal with it.
                offset_ptr.add(x + 0).write(color);
                offset_ptr.add(x + 1).write(color);
                offset_ptr.add(x + 2).write(color);
                offset_ptr.add(x + 3).write(color);
                offset_ptr.add(x + 4).write(color);
                offset_ptr.add(x + 5).write(color);
                offset_ptr.add(x + 6).write(color);
                offset_ptr.add(x + 7).write(color);
                x += 8;
            }}
            while x < x1 {
                buf[offset + x] = color;
                x += 1;
            }

            offset += tw as usize;
        }
    }

    #[allow(dead_code)] // @temp
    pub fn fill_rect_abs(&mut self, x0: i32, y0: i32, x1: i32, y1: i32, color: u32) {
        if color_unpack(color).3 == 255 {
            self.fill_rect_abs_opaque(x0, y0, x1, y1, color);
            return;
        }

        let tw = self.target.width();
        let th = self.target.height();

        let x0 = x0.clamp(0, tw) as usize;
        let y0 = y0.clamp(0, th) as usize;
        let x1 = x1.clamp(0, tw) as usize;
        let y1 = y1.clamp(0, th) as usize;

        if x0 == x1 || y0 == y1 { return }

        let buf = self.target.get_data_mut();

        let mut offset = y0 * tw as usize;
        for _ in y0..y1 {
            for x in x0..x1 {
                let dst = &mut buf[offset + x];
                *dst = over(color, *dst);
            }

            offset += tw as usize;
        }
    }

    pub fn clear(&mut self, r: u8, g: u8, b: u8) {
        self.fill_rect_abs_opaque(0, 0, self.width(), self.height(), color_pack_u8(r, g, b, 255));
    }


    pub fn draw_mask_abs(&mut self, x: i32, y: i32, mask: &[u8], mask_w: u32, mask_h: u32, color: u32) {
        let x0 = x;
        let y0 = y;
        let x1 = x0 + mask_w as i32;
        let y1 = y0 + mask_h as i32;

        let tw = self.target.width();
        let th = self.target.height();
        let buf = self.target.get_data_mut();

        let x0c = x0.clamp(0, tw);
        let y0c = y0.clamp(0, th);
        let x1c = x1.clamp(0, tw);
        let y1c = y1.clamp(0, th);

        let (r, g, b, a) = color_unpack(color);

        for y in y0c..y1c {
            for x in x0c..x1c {
                let cx = (x - x0) as usize;
                let cy = (y - y0) as usize;
                let c  = mask[cy * mask_w as usize + cx] as u32;

                let src = color_pack((
                    c*r >> 8,
                    c*g >> 8,
                    c*b >> 8,
                    c*a >> 8));

                let value = &mut buf[(y*tw + x) as usize];
                *value = over(src, *value);
            }
        }
    }

    pub fn draw_text_layout_abs(&mut self, x0: i32, y0: i32, layout: &TextLayout<u32>) {
        let fonts = self.fonts.clone();
        let mut fonts = fonts.inner.borrow_mut();

        let mut y0 = y0 as f32;
        for line in &layout.lines {
            let baseline = (y0 + line.max_ascent) as i32;

            let mut x0 = x0 as f32;
            for span in &layout.spans[line.span_range()] {
                for glyph in &layout.glyphs[span.glyph_range()] {
                    let (metrics, mask) = fonts.glyph_mask(span.face_id, span.font_size, glyph.index);
                    self.draw_mask_abs(
                        x0 as i32 + glyph.dx as i32,
                        baseline  + glyph.dy as i32,
                        &mask, metrics.width as u32, metrics.height as u32,
                        span.effect
                    );
                    x0 += glyph.advance;
                }
            }

            y0 += line.height;
        }
    }
}



#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FaceId(u32);

impl FaceId {
    pub const DEFAULT: FaceId = FaceId(0);

    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }
}

impl Default for FaceId { #[inline(always)] fn default() -> FaceId { FaceId::DEFAULT } }


#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Bold(pub bool);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Italic(pub bool);


#[derive(Clone)]
pub struct FontCtx {
    inner: Rc<RefCell<FontCtxInner>>,
}

struct FontCtxInner {
    families: Vec<Family>,
    faces: Vec<Face>,

    glyph_cache: LruCache<(FaceId, NotNan<f32>, u16), (fontdue::Metrics, Vec<u8>)>,
}

struct Family {
    name:  String,
    faces: Vec<FaceInfo>,
}

#[derive(Clone, Copy, Debug)]
struct FaceInfo {
    id:     FaceId,
    bold:   Bold,
    italic: Italic,
}

struct Face {
    font: Font,
    #[allow(dead_code)] // @temp
    info: FaceInfo,
}

impl FontCtx {
    pub fn new() -> FontCtx {
        FontCtx {
            inner: Rc::new(RefCell::new(FontCtxInner {
                families: vec![],
                faces:    vec![],

                glyph_cache: LruCache::new(128.try_into().unwrap()),
            })),
        }
    }

    #[allow(dead_code)] // @temp
    pub fn find_face(&self, family: &str, bold: Bold, italic: Italic) -> FaceId {
        let this = self.inner.borrow();

        let family = this.families.iter().find(|f| f.name == family);
        if let Some(family) = family {
            return family.find_face_exact(bold, italic)
                .unwrap_or_else(|| family.faces[0].id);
        }
        FaceId::DEFAULT
    }

    pub fn add_face(&self, family: &str, bold: Bold, italic: Italic, data: &[u8]) -> FaceId {
        let mut this = self.inner.borrow_mut();

        // create face.
        let id = FaceId(this.faces.len() as u32);
        let info = FaceInfo { id, bold, italic };
        let font = Font::from_bytes(data, Default::default()).unwrap();
        this.faces.push(Face { info, font });

        // add to family.
        let fam = this.families.iter_mut().find(|f| f.name == family);
        if let Some(family) = fam {
            assert!(family.find_face_exact(bold, italic).is_none());
            family.faces.push(info);
        }
        else {
            this.families.push(Family { name: family.into(), faces: vec![info] });
        }

        id
    }
}

impl FontCtxInner {
    fn glyph_mask(&mut self, face: FaceId, size: NotNan<f32>, glyph: u16) -> &(fontdue::Metrics, Vec<u8>) {
        self.glyph_cache.get_or_insert((face, size, glyph), || {
            self.faces[face.usize()].font.rasterize_indexed(glyph, *size)
        })
    }
}

impl Family {
    fn find_face_exact(&self, bold: Bold, italic: Italic) -> Option<FaceId> {
        for info in &self.faces {
            if info.bold == bold && info.italic == italic {
                return Some(info.id);
            }
        }
        None
    }
}


pub struct TextLayout<E> {
    fonts:  FontCtx,
    text:   String,
    lines:  Vec<Line>,
    spans:  Vec<Span<E>>,
    glyphs: Vec<Glyph>,
}

#[derive(Clone, Copy, Debug)]
struct Glyph {
    index: u16,
    advance: f32,
    dx: f32,
    dy: f32,
}

struct Line {
    text_begin:  u32,
    text_end:    u32,
    span_begin: u32,
    span_end: u32,

    width:  f32,
    max_ascent:  f32,
    max_descent: f32,
    max_gap:     f32,
    height:      f32,
}

struct Span<E> {
    text_begin:  u32,
    text_end:    u32,
    glyph_begin: u32,
    glyph_end:   u32,

    width: f32,

    face_id:   FaceId,
    font_size: NotNan<f32>,
    effect:    E,
}


impl Line {
    #[inline(always)]
    fn new(text_begin: u32, span_begin: u32) -> Line {
        Line {
            text_begin,  text_end:  text_begin,
            span_begin,  span_end:  span_begin,
            width: 0.0,
            max_ascent:  0.0,
            max_descent: 0.0,
            max_gap:     0.0,
            height:      0.0,
        }
    }

    #[inline(always)]
    fn span_range(&self) -> core::ops::Range<usize> {
        self.span_begin as usize .. self.span_end as usize
    }
}

impl<E> Span<E> {
    #[inline(always)]
    fn glyph_range(&self) -> core::ops::Range<usize> {
        self.glyph_begin as usize .. self.glyph_end as usize
    }
}


impl<E> TextLayout<E> {
    pub fn new(fonts: &FontCtx) -> Self {
        TextLayout {
            fonts:  fonts.clone(),
            text:   "".into(),
            lines:  vec![Line::new(0, 0)],
            spans:  vec![],
            glyphs: vec![],
        }
    }

    #[inline(always)]
    pub fn text(&self) -> &str { &self.text }

    pub fn clear(&mut self) {
        self.text.clear();
        self.lines.clear();
        self.spans.clear();
        self.glyphs.clear();
        self.lines.push(Line::new(0, 0));
    }

    pub fn append_ex(&mut self, text: &str, face_id: FaceId, font_size: f32, effect: E) where E: Copy {
        let font_size = NotNan::new(font_size).unwrap();

        let mut current_line = self.lines.last_mut().unwrap();
        let mut pos_cursor   = current_line.width;

        let mut text_cursor = self.text.len() as u32;
        self.text.push_str(text);

        let fonts = self.fonts.clone();
        let fonts = fonts.inner.borrow();
        let face  = &fonts.faces[face_id.usize()];

        let font_metrics = face.font.horizontal_line_metrics(*font_size).unwrap();
        current_line.max_ascent  = current_line.max_ascent.max(font_metrics.ascent);
        current_line.max_descent = current_line.max_descent.max(-font_metrics.descent);
        current_line.max_gap     = current_line.max_gap.max(font_metrics.line_gap);
        current_line.height = current_line.max_ascent + current_line.max_descent + current_line.max_gap;

        let mut text = text;
        while text.len() > 0 {
            let (segment_end, is_line) =
                text.find('\n').map(|index| (index, true))
                .unwrap_or((text.len(), false));

            let pos_begin = pos_cursor;

            // add glyphs.
            // assume one glyph per char.
            let glyph_begin = self.glyphs.len() as u32;
            for c in text[..segment_end].chars() {
                // @todo: kern.
                let glyph_index = face.font.lookup_glyph_index(c);
                let metrics     = face.font.metrics_indexed(glyph_index, *font_size);

                self.glyphs.push(Glyph {
                    index: glyph_index,
                    advance: metrics.advance_width,
                    dx: metrics.bounds.xmin,
                    dy: -metrics.bounds.height - metrics.bounds.ymin,
                });

                pos_cursor += metrics.advance_width;
            }
            assert_eq!(self.glyphs.len(), glyph_begin as usize + segment_end);
            let glyph_end = self.glyphs.len() as u32;

            // add span.
            self.spans.push(Span {
                text_begin: text_cursor,
                text_end:   text_cursor + segment_end as u32,
                glyph_begin, glyph_end,
                width: pos_cursor - pos_begin,
                face_id, font_size, effect,
            });


            // update line.
            let line_end = text_cursor + segment_end as u32;
            current_line.text_end  = line_end;
            current_line.span_end += 1;
            current_line.width     = pos_cursor;

            if is_line {
                // line ranges are weird. they don't include the `\n`.
                // so the next line starts after the current line's `\n`.
                let text_begin = line_end + 1;
                let span_begin = self.spans.len()  as u32;

                let max_ascent  = font_metrics.ascent;
                let max_descent = -font_metrics.descent;
                let max_gap     = font_metrics.line_gap;

                self.lines.push(Line {
                    text_begin, text_end: text_begin,
                    span_begin, span_end: span_begin,
                    width: 0.0,
                    max_ascent, max_descent, max_gap,
                    height: max_ascent+ max_descent + max_gap,
                });

                current_line = self.lines.last_mut().unwrap();
                pos_cursor   = 0.0;
            }

            let text_advance = segment_end + is_line as usize;
            text_cursor += text_advance as u32;
            text = &text[text_advance..];
        }
    }

    pub fn width(&self) -> f32 {
        let mut width = 0f32;
        for line in &self.lines {
            width = width.max(line.width);
        }
        width
    }

    pub fn height(&self) -> f32 {
        let mut height = 0.0;
        for line in &self.lines {
            height += line.height;
        }
        height
    }
}


#[derive(Clone, Copy, Debug)]
pub struct RangeMetrics {
    pub x0: f32,
    pub x1: f32,
    pub y: f32,
    // @todo: baseline.
    pub line_height: f32,
    pub line_index:  u32,
}

impl<E> TextLayout<E> {
    #[allow(dead_code)] // @temp
    pub fn hit_test_text_pos(&self, pos: u32) -> RangeMetrics {
        let pos = pos.min(self.text.len() as u32);

        let mut y = 0.0;
        for (line_index, line) in self.lines.iter().enumerate() {
            let line_index  = line_index as u32;
            let line_height = line.height;

            let mut x = 0.0;
            if pos >= line.text_begin && pos <= line.text_end {
                for span in &self.spans[line.span_range()] {
                    // in current span.
                    if pos >= span.text_begin
                    && pos <  span.text_end {
                        let offset = (pos - span.text_begin) as usize;
                        let glyph_begin = span.glyph_begin as usize;

                        for i in 0..offset {
                            x += self.glyphs[glyph_begin + i].advance;
                        }

                        let advance = self.glyphs[glyph_begin + offset].advance;
                        return RangeMetrics {
                            x0: x,
                            x1: x + advance,
                            y,
                            line_height, line_index,
                        };
                    }

                    x += span.width;
                }

                // end of line.
                let x = line.width;
                return RangeMetrics {
                    x0: x,
                    x1: x,
                    y,
                    line_height, line_index,
                };
            }

            y += line_height;
        }

        assert_eq!(self.text.len(), 0);
        return RangeMetrics { x0: 0.0, x1: 0.0, y: 0.0, line_height: 0.0, line_index: 0 };
    }
}


impl<E> TextLayout<E> {
    pub fn hit_test_text_ranges<F: FnMut(&RangeMetrics)>(&self, begin: u32, end: u32, mut f: F) {
        let begin = begin.min(self.text.len() as u32);
        let end   = end.min(self.text.len() as u32);
        if begin >= end { return }
        
        let mut target   = begin;
        let mut in_range = false;

        let mut y = 0.0;

        for (line_index, line) in self.lines.iter().enumerate() {
            let line_index  = line_index as u32;
            let line_height = line.height;

            let f = &mut f;
            let mut f = |x0: f32, x1: f32| {
                if x0 < x1 {
                    f(&RangeMetrics {
                        x0, x1, y,
                        line_height, line_index,
                    });
                }
            };

            let mut x = 0.0;
            if target >= line.text_begin && target <= line.text_end {
                for span in &self.spans[line.span_range()] {
                    // in current span.
                    if target >= span.text_begin
                    && target <  span.text_end {
                        let offset = (target - span.text_begin) as usize;
                        let glyph_begin = span.glyph_begin as usize;

                        let span_x = x;
                        let mut target_x = x;
                        for i in 0..offset {
                            target_x += self.glyphs[glyph_begin + i].advance;
                        }

                        if in_range {
                            f(span_x, target_x);
                            return;
                        }
                        else {
                            in_range = true;
                            target   = end;

                            if target < span.text_end {
                                let mut end_x = target_x;
                                let end_offset = (target - span.text_begin) as usize;
                                for i in offset..end_offset {
                                    end_x += self.glyphs[glyph_begin + i].advance;
                                }

                                f(target_x, end_x);
                                return;
                            }
                            else {
                                f(target_x, x + span.width);
                            }
                        }
                    }
                    else if in_range {
                        f(x, x + span.width);
                    }

                    x += span.width;
                }

                if target == line.text_end {
                    if in_range {
                        return;
                    }
                    else {
                        in_range = true;
                        target   = end;
                    }
                }
            }
            else if in_range {
                f(0., line.width);
            }

            y += line_height;
        }

        unreachable!()
    }
}


#[derive(Clone, Copy, Debug)]
pub struct HitMetrics {
    pub text_pos_left:  u32,
    pub text_pos_right: u32,

    pub fraction: f32,
    pub out_of_bounds: [bool; 2],
}

impl<E> TextLayout<E> {
    pub fn hit_test_line(&self, line_index: u32, x: f32) -> HitMetrics {
        let line = &self.lines[line_index as usize];

        if x < 0.0 {
            return HitMetrics {
                text_pos_left:  line.text_begin,
                text_pos_right: line.text_begin,
                fraction: 0.0,
                out_of_bounds: [true, false],
            };
        }

        let mut cursor = 0.0;
        for span in &self.spans[line.span_range()] {
            for glyph in span.glyph_range() {
                let new_cursor = cursor + self.glyphs[glyph].advance;

                if x >= cursor && x < new_cursor {
                    let fraction = (x - cursor) / (new_cursor - cursor);

                    let offset = glyph as u32 - span.glyph_begin;
                    return HitMetrics {
                        text_pos_left:  span.text_begin + offset,
                        text_pos_right: span.text_begin + offset + 1,
                        fraction,
                        out_of_bounds: [false, false],
                    }
                }

                cursor = new_cursor;
            }
        }

        return HitMetrics {
            text_pos_left:  line.text_end,
            text_pos_right: line.text_end,
            fraction: 0.0,
            out_of_bounds: [true, false],
        };
    }

    pub fn hit_test_pos(&self, x: f32, y: f32) -> HitMetrics {
        if self.lines.len() == 0 {
            return HitMetrics {
                text_pos_left:  0,
                text_pos_right: 0,
                fraction: 0.0,
                out_of_bounds: [true, true],
            }
        }

        // above.
        if y < 0.0 {
            let mut result = self.hit_test_line(0, x);
            result.out_of_bounds[1] = true;
            return result;
        }

        let mut line_y = 0.0;
        for (line_index, line) in self.lines.iter().enumerate() {
            let new_line_y = line_y + line.height;

            if y >= line_y && y < new_line_y {
                return self.hit_test_line(line_index as u32, x);
            }

            line_y = new_line_y;
        }

        // below.
        let mut result = self.hit_test_line(self.lines.len() as u32 - 1, x);
        result.out_of_bounds[1] = true;
        return result;
    }
}



#[inline(always)]
pub fn color_from_unmult_rgba((r, g, b, a): (u32, u32, u32, u32)) -> u32 {
    color_pack((muldiv255(r, a), muldiv255(g, a), muldiv255(b, a), a))
}

#[inline(always)]
pub fn color_pack((r, g, b, a): (u32, u32, u32, u32)) -> u32 {
    a << 24 | r << 16 | g << 8 | b
}

#[inline(always)]
pub fn color_pack_u8(r: u8, g: u8, b: u8, a: u8) -> u32 {
    color_pack((r as u32, g as u32, b as u32, a as u32))
}

#[inline(always)]
pub fn color_unpack(c: u32) -> (u32, u32, u32, u32) {
    ((c >> 16) & 0xff, (c >>  8) & 0xff, (c >>  0) & 0xff, (c >> 24) & 0xff)
}

#[inline(always)]
pub fn color_pre_multiply(c: u32) -> u32 {
    color_from_unmult_rgba(color_unpack(c))
}


// function's down here are taken from swcomposite,
// cause i ain't adding an explicit dependency for one function.

// this is an approximation of true 'over' that does a division by 256 instead
// of 255. It is the same style of blending that Skia does. It corresponds 
// to Skia's SKPMSrcOver
#[inline(always)]
pub fn over(src: u32, dst: u32) -> u32 {
    let a = src >> 24;
    let a = 256 - a;
    let mask = 0xff00ff;
    let rb = ((dst & mask) * a) >> 8;
    let ag = ((dst >> 8) & mask) * a;
    src + ((rb & mask) | (ag & !mask))
}

// Calculates floor(a*b/255 + 0.5)
#[inline(always)]
pub fn muldiv255(x: u32, y: u32) -> u32 {
    // The deriviation for this formula can be
    // found in "Three Wrongs Make a Right" by Jim Blinn.
    let tmp = x * y + 128;
    (tmp + (tmp >> 8)) >> 8
}

// end of sw-composite functions.

