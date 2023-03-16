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


struct Decoration {
    text_begin: u32,
    text_end:   u32,
    data: DecorationData,
}

enum DecorationData {
    Style  { color: u32 },
    Insert { text: String, color: u32 },
}


#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TokenClass {
    Default,
    Keyword,
    Comment,
    Label,
    Operator,
    Literal,
    String,
}

impl TokenClass {
    fn from_data(data: kibi::TokenData) -> TokenClass {
        use kibi::TokenData::*;
        match data {
            Ident (_) => TokenClass::Default,

            Number (_) |
            Bool (_) |
            Nil => TokenClass::Literal,

            QuotedString (_) => TokenClass::String,

            Label (_) => TokenClass::Label,

            LParen |
            RParen |
            LBracket |
            RBracket |
            LCurly |
            RCurly |
            Dot |
            Comma |
            Colon |
            Semicolon |
            FatArrow |
            ColonEq => TokenClass::Default,

            KwLet | KwVar |
            KwDo | KwIf | KwElif | KwElse | KwWhile |
            KwFor | KwIn |
            KwBreak | KwContinue | KwReturn |
            KwEnd |
            KwFn |
            KwAnd | KwOr | KwNot |
            KwEnv => TokenClass::Keyword,

            OpAdd |
            OpAddAssign |
            OpMinus |
            OpMinusAssign |
            OpMul |
            OpMulAssign |
            OpDiv |
            OpDivAssign |
            OpFloorDiv |
            OpFloorDivAssign |
            OpRem |
            OpRemAssign |
            OpAssign |
            OpEq |
            OpNe |
            OpLe |
            OpLt |
            OpGe |
            OpGt |
            OpOptChain |
            OpOrElse |
            OpOrElseAssign => TokenClass::Operator,
        }
    }

    fn color(self) -> u32 {
        match self {
            TokenClass::Default  => 0xffbfbdb6,
            TokenClass::Keyword  => 0xffff8f40,
            TokenClass::Comment  => 0x8cacb6bf,
            TokenClass::Label    => 0xffff8f40,
            TokenClass::Operator => 0xfff29668,
            TokenClass::Literal  => 0xffd2a6ff,
            TokenClass::String   => 0xffaad94c,
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

        // @todo: looks like offset based source positions are more useful (here).
        let mut line_begins = vec![];
        for line in text.lines() {
            line_begins.push(line.as_ptr() as usize - text.as_ptr() as usize);
        }
        let line_to_offset = |line: u32| {
            line_begins[line as usize - 1] as u32
        };

        let mut decos = vec![];
        for token in &info.tokens {
            // inserted semicolons.
            if token.source.begin == token.source.end {
                if let kibi::TokenData::Semicolon = token.data {
                    let begin = token.source.begin;
                    let text_begin = line_to_offset(begin.line) + begin.column - 1;
                    decos.push(Decoration {
                        text_begin,
                        text_end: text_begin,
                        data: DecorationData::Insert { text: ";".to_string(), color: TokenClass::Comment.color() },
                    });
                }
            }
            // syntax highlighting.
            else {
                let begin = token.source.begin;
                let end   = token.source.end;
                let text_begin = line_to_offset(begin.line) + begin.column - 1;
                let text_end   = line_to_offset(end.line)   + end.column - 1;
                let class = TokenClass::from_data(token.data);
                decos.push(Decoration { text_begin, text_end,
                    data: DecorationData::Style { color: class.color() }
                });
            }
        }
        // decos are already sorted.

        self.info = unsafe { core::mem::transmute(info) };

        self.layout.clear();
        {
            let font_size = 24.;

            let mut deco_cursor = 0;
            let mut text_cursor = 0;
            while text_cursor < text.len() {
                if let Some(next_deco) = decos.get(deco_cursor) {
                    let deco_begin = next_deco.text_begin as usize;
                    let deco_end   = next_deco.text_end   as usize;

                    if text_cursor < deco_begin {
                        self.layout.append_ex(&text[text_cursor..deco_begin], FaceId::DEFAULT, font_size, TokenClass::Default.color());
                    }

                    match &next_deco.data {
                        DecorationData::Style { color } => {
                            self.layout.append_ex(&text[deco_begin..deco_end], FaceId::DEFAULT, font_size, *color);
                        }

                        DecorationData::Insert { text, color } => {
                            self.layout.append_ex(text, FaceId::DEFAULT, font_size, *color);
                        }
                    }

                    deco_cursor += 1;
                    text_cursor  = deco_end;
                }
                else {
                    self.layout.append_ex(&text[text_cursor..], FaceId::DEFAULT, font_size, TokenClass::Default.color());
                    text_cursor = text.len();
                }
            }
        }
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

