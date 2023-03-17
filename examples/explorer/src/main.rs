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
    Style   { color: u32 },
    Replace { text: String, color: u32 },
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


#[derive(Clone, Copy, Debug)]
struct TextMap {
    source_begin: u32,
    source_end:   u32,
    data: TextMapData,
}

#[allow(dead_code)] // @temp: text_end not used.
#[derive(Clone, Copy, Debug)]
enum TextMapData {
    None,
    TextRange { text_begin: u32, text_end: u32 },
}

#[derive(Clone, Copy, Debug)]
struct SourceMap {
    text_begin: u32,
    text_end:   u32,
    data: SourceMapData,
}

#[allow(dead_code)] // @temp: source_end not used.
#[derive(Clone, Copy, Debug)]
enum SourceMapData {
    None,
    SourceRange { source_begin: u32, source_end: u32 },
}


struct CodeView {
    text: String,
    info: CodeInfo<'static>,
    layout: TextLayout<u32>,
    line_begins: Vec<u32>,
    text_map:    Vec<TextMap>,
    source_map:  Vec<SourceMap>,
}

impl CodeView {
    pub fn new(fonts: &FontCtx) -> CodeView {
        CodeView {
            text:   "".into(),
            info:   CodeInfo::new(""),
            layout: TextLayout::new(fonts),
            line_begins: vec![],
            text_map:    vec![],
            source_map:  vec![],
        }
    }

    pub fn source_pos_to_offset(&self, pos: kibi::SourcePos) -> u32 {
        self.line_begins[pos.line as usize - 1] + pos.column - 1
    }

    pub fn set_text(&mut self, text: &str) {
        self.text.clear();
        self.text.push_str(text);

        let info = CodeInfo::new(&self.text);

        // @todo: looks like offset based source positions are more useful (here).
        self.line_begins.clear();
        for line in text.lines() {
            self.line_begins.push((line.as_ptr() as usize - text.as_ptr() as usize) as u32);
        }

        let mut decos = vec![];
        for token in &info.tokens {
            // inserted semicolons.
            if token.source.begin == token.source.end {
                if let kibi::TokenData::Semicolon = token.data {
                    let text_begin = self.source_pos_to_offset(token.source.begin);
                    decos.push(Decoration {
                        text_begin,
                        text_end: text_begin,
                        data: DecorationData::Replace {
                            text: ";".to_string(),
                            color: TokenClass::Comment.color(),
                        },
                    });
                }
            }
            // syntax highlighting.
            else {
                let text_begin = self.source_pos_to_offset(token.source.begin);
                let text_end   = self.source_pos_to_offset(token.source.end);
                let class = TokenClass::from_data(token.data);
                decos.push(Decoration { text_begin, text_end,
                    data: DecorationData::Style { color: class.color() }
                });
            }
        }
        // decos are already sorted.

        self.info = unsafe { core::mem::transmute(info) };

        self.layout.clear();
        self.text_map.clear();
        self.source_map.clear();
        {
            let font_size = 24.;

            let mut deco_cursor = 0;
            let mut text_cursor = 0;
            while text_cursor < text.len() {
                if let Some(next_deco) = decos.get(deco_cursor) {
                    let deco_begin = next_deco.text_begin as usize;
                    let deco_end   = next_deco.text_end   as usize;

                    if text_cursor < deco_begin {
                        let source_begin = text_cursor as u32;
                        let source_end   = deco_begin  as u32;

                        let text_begin = self.layout.text().len() as u32;
                        self.layout.append_ex(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, TokenClass::Default.color());
                        let text_end = self.layout.text().len() as u32;

                        self.text_map.push(TextMap {
                            source_begin,
                            source_end,
                            data: TextMapData::TextRange { text_begin, text_end },
                        });
                        self.source_map.push(SourceMap {
                            text_begin,
                            text_end,
                            data: SourceMapData::SourceRange { source_begin, source_end },
                        });
                    }

                    match &next_deco.data {
                        DecorationData::Style { color } => {
                            let source_begin = deco_begin as u32;
                            let source_end   = deco_end   as u32;

                            let text_begin = self.layout.text().len() as u32;
                            self.layout.append_ex(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, *color);
                            let text_end = self.layout.text().len() as u32;

                            self.text_map.push(TextMap {
                                source_begin,
                                source_end,
                                data: TextMapData::TextRange { text_begin, text_end },
                            });
                            self.source_map.push(SourceMap {
                                text_begin,
                                text_end,
                                data: SourceMapData::SourceRange { source_begin, source_end },
                            });
                        }

                        DecorationData::Replace { text, color } => {
                            let source_begin = deco_begin as u32;
                            let source_end   = deco_end   as u32;

                            let text_begin = self.layout.text().len() as u32;
                            self.layout.append_ex(text, FaceId::DEFAULT, font_size, *color);
                            let text_end = self.layout.text().len() as u32;

                            self.text_map.push(TextMap {
                                source_begin,
                                source_end,
                                data: TextMapData::None,
                            });
                            self.source_map.push(SourceMap {
                                text_begin,
                                text_end,
                                data: SourceMapData::None,
                            });
                        }
                    }

                    deco_cursor += 1;
                    text_cursor  = deco_end;
                }
                else {
                    let source_begin = text_cursor as u32;
                    let source_end   = text.len()  as u32;

                    let text_begin = self.layout.text().len() as u32;
                    self.layout.append_ex(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, TokenClass::Default.color());
                    let text_end = self.layout.text().len() as u32;

                    self.text_map.push(TextMap {
                        source_begin,
                        source_end,
                        data: TextMapData::TextRange { text_begin, text_end },
                    });
                    self.source_map.push(SourceMap {
                        text_begin,
                        text_end,
                        data: SourceMapData::SourceRange { source_begin, source_end },
                    });

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

            if let Some((x, y)) = self.window.get_mouse_pos(minifb::MouseMode::Pass) {
                let metrics = self.code.layout.hit_test_pos(x - 50., y - 30.);
                let pos = metrics.text_pos_left;

                if !metrics.out_of_bounds[0] && !metrics.out_of_bounds[1] {
                    for mapping in &self.code.source_map {
                        if pos >= mapping.text_begin && pos < mapping.text_end {
                            let offset = pos - mapping.text_begin;
                            if let SourceMapData::SourceRange { source_begin, source_end: _ } = mapping.data {
                                let source_pos = source_begin + offset;

                                for token in &self.code.info.tokens {
                                    let tok_begin = self.code.source_pos_to_offset(token.source.begin);
                                    let tok_end   = self.code.source_pos_to_offset(token.source.end);
                                    if source_pos >= tok_begin && source_pos < tok_end {
                                        let text_begin = self.code.text_map.iter()
                                            .find(|map| tok_begin >= map.source_begin && tok_begin < map.source_end)
                                            .and_then(|map|
                                                if let TextMapData::TextRange { text_begin, text_end: _ } = map.data {
                                                    Some(text_begin + (tok_begin - map.source_begin))
                                                }
                                                else { None });

                                        let tok_last = tok_end - 1;
                                        let text_last = self.code.text_map.iter()
                                            .find(|map| tok_last >= map.source_begin && tok_last < map.source_end)
                                            .and_then(|map|
                                                if let TextMapData::TextRange { text_begin, text_end: _ } = map.data {
                                                    Some(text_begin + (tok_last - map.source_begin))
                                                }
                                                else { None });

                                        if let (Some(text_begin), Some(text_last)) = (text_begin, text_last) {
                                            self.code.layout.hit_test_text_ranges(text_begin, text_last + 1, |range| {
                                                r.fill_rect(
                                                    50. + range.x, 30. + range.y,
                                                    range.width, range.line_height,
                                                    &raqote::Source::Solid(raqote::SolidSource::from_unpremultiplied_argb(255, 50, 55, 60)),
                                                    &Default::default());
                                            });

                                            let begin = self.code.layout.hit_test_text_pos(text_begin);
                                            let dump = format!("{:#?}", token);
                                            let mut temp_layout = TextLayout::new(r.fonts());
                                            temp_layout.append_ex(&dump, FaceId::DEFAULT, 16., TokenClass::Default.color());
                                            r.draw_text_layout_abs(500, 30 + begin.y as i32, &temp_layout);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

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

