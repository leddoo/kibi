use minifb::{Window, WindowOptions};


mod renderer;
use renderer::*;


struct CodeInfo<'a> {
    tokens: Vec<kibi::Token<'a>>,
}

impl<'a> CodeInfo<'a> {
    pub fn new(source: &'a str) -> CodeInfo<'a> {
        let tokens = kibi::Tokenizer::tokenize(source.as_bytes(), true).unwrap();

        CodeInfo {
            tokens,
        }
    }
}

struct CodeView {
    text: String,
    info: CodeInfo<'static>,
    layout: TextLayout<u32>,
}

impl CodeView {
    pub fn new(fonts: &FontCtx) -> CodeView {
        CodeView {
            text:   "".into(),
            info:   CodeInfo::new(""),
            layout: TextLayout::new(fonts),
        }
    }

    pub fn set_text(&mut self, text: &str) {
        self.text.clear();
        self.text.push_str(text);

        let info = CodeInfo::new(&self.text);
        self.info = unsafe { core::mem::transmute(info) };

        self.layout.clear();
        self.layout.append_ex(text, FaceId::DEFAULT, 24., 0xffffffff);
    }

    pub fn draw(&mut self, r: &mut Renderer) {
        r.draw_text_layout_abs(50, 50, &self.layout);
    }
}


struct Explorer {
    window:   Window,
    renderer: Renderer,
    code:     CodeView,
}

impl Explorer {
    pub fn new() -> Explorer {
        let mut window = Window::new("kibi explorer", 800, 600, WindowOptions {
            resize: true,
            ..Default::default()
        }).unwrap();

        window.limit_update_rate(Some(std::time::Duration::from_millis(6)));

        let fonts = FontCtx::new();
        fonts.add_face("Source Code Pro", Bold(false), Italic(false), include_bytes!("../res/SourceCodePro-Regular.ttf"));

        Explorer {
            window,
            renderer: Renderer::new(&fonts),
            code:     CodeView::new(&fonts),
        }
    }

    pub fn run(&mut self) {
        while self.window.is_open() {
            let size = self.window.get_size();

            let r = &mut self.renderer;
            r.set_size(size.0 as u32, size.1 as u32);

            r.clear(13, 16, 23);

            self.code.draw(r);

            self.window.update_with_buffer(r.data(), size.0, size.1).unwrap();
        }
    }
}


fn main() {
    let mut e = Explorer::new();
    e.code.set_text(include_str!("../../fib.kb"));
    e.run();
}

