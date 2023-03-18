use minifb::{Window, WindowOptions};
use kibi::index_vec::*;
use kibi::ast::*;


mod renderer;
use renderer::*;


struct ItemInfo {
    item_id: ItemId,
    node_id: NodeId,
    #[allow(dead_code)] // @temp.
    source_range: SourceRange,
}

enum NodeRef<'a> {
    None,
    Stmt(&'a Stmt<'a>),
    Expr(&'a Expr<'a>),
}

struct NodeInfo<'a> {
    #[allow(dead_code)] // @temp.
    parent:  OptNodeId,
    node_id: NodeId,
    node_ref: NodeRef<'a>,
    source_range: SourceRange,
}

struct AstInfo<'a> {
    items: IndexVec<kibi::ItemId, ItemInfo>,
    nodes: IndexVec<kibi::NodeId, NodeInfo<'a>>,
}


impl<'a> AstInfo<'a> {
    fn new() -> Self {
        AstInfo { items: IndexVec::new(), nodes: IndexVec::new() }
    }

    fn add_item_info(&mut self, info: ItemInfo) {
        assert_eq!(self.items.len(), info.item_id.usize());
        self.items.push(info);
    }

    fn add_node_info(&mut self, info: NodeInfo<'a>) {
        assert_eq!(self.nodes.len(), info.node_id.usize());
        self.nodes.push(info);
    }

    fn collect(&mut self, module: &'a item::Module<'a>) {
        self.add_item_info(ItemInfo { item_id: ItemId::ZERO, node_id: NodeId::ZERO, source_range: SourceRange::null() });
        self.add_node_info(NodeInfo { parent: None.into(), node_id: NodeId::ZERO, node_ref: NodeRef::None, source_range: SourceRange::null() });
        self.collect_block(&module.block.stmts, NodeId::ZERO.some());
    }

    fn collect_stmt(&mut self, stmt: &'a Stmt<'a>, parent: OptNodeId) {
        self.add_node_info(NodeInfo {
            parent,
            node_id: stmt.id,
            node_ref: NodeRef::Stmt(stmt),
            source_range: stmt.source,
        });
        let stmt_id = stmt.id.some();

        match &stmt.data {
            StmtData::Item (item) => {
                self.add_item_info(ItemInfo {
                    item_id: item.id,
                    node_id: stmt.id,
                    source_range: item.source,
                });

                match &item.data {
                    ItemData::Module(module) => {
                        let _ = module;
                        unimplemented!()
                    }

                    ItemData::Func(func) => {
                        self.collect_block(&func.body, stmt_id);
                    }
                }
            }

            StmtData::Local (local) => {
                if let Some(value) = &local.value {
                    self.collect_expr(value, stmt_id);
                }
            }

            StmtData::Expr (expr) => { self.collect_expr(expr, stmt_id); }

            StmtData::Empty => (),
        }
    }

    fn collect_expr(&mut self, expr: &'a Expr<'a>, parent: OptNodeId) {
        self.add_node_info(NodeInfo {
            parent,
            node_id: expr.id,
            node_ref: NodeRef::Expr(expr),
            source_range: expr.source,
        });
        let expr_id = expr.id.some();

        match &expr.data {
            ExprData::Nil |
            ExprData::Bool (_) |
            ExprData::Number (_) |
            ExprData::QuotedString (_) |
            ExprData::Ident (_) => {}


            ExprData::Tuple (tuple) => {
                for value in &tuple.values {
                    self.collect_expr(value, expr_id);
                }
            }

            ExprData::List (list) => {
                for value in &list.values {
                    self.collect_expr(value, expr_id);
                }
            }

            ExprData::Do (doo) => {
                self.collect_block(&doo.stmts, expr_id);
            }

            ExprData::SubExpr (sub_expr) => {
                self.collect_expr(sub_expr, expr_id);
            }

            ExprData::Op1 (op1) => {
                self.collect_expr(&op1.child, expr_id);
            }

            ExprData::Op2 (op2) => {
                self.collect_expr(&op2.children[0], expr_id);
                self.collect_expr(&op2.children[1], expr_id);
            }

            ExprData::Field (field) => {
                self.collect_expr(&field.base, expr_id);
            }

            ExprData::Index (index) => {
                self.collect_expr(&index.base, expr_id);
                self.collect_expr(&index.index, expr_id);
            }

            ExprData::Call (call) => {
                self.collect_expr(&call.func, expr_id);
                for arg in &call.args {
                    self.collect_expr(arg, expr_id);
                }
            }

            ExprData::If (iff) => {
                self.collect_expr(&iff.condition, expr_id);
                self.collect_block(&iff.on_true.stmts, expr_id);
                if let Some(on_false) = &iff.on_false {
                    self.collect_block(&on_false.stmts, expr_id);
                }
            }

            ExprData::While (whilee) => {
                self.collect_expr(&whilee.condition, expr_id);
                self.collect_block(&whilee.body, expr_id);
            }

            ExprData::Break (brk) => {
                if let Some(value) = &brk.value {
                    self.collect_expr(value, expr_id);
                }
            }

            ExprData::Continue (_) => {}

            ExprData::Return (ret) => {
                if let Some(value) = &ret.value {
                    self.collect_expr(value, expr_id);
                }
            }

            ExprData::Env => {}
        }
    }

    fn collect_block(&mut self, block: &'a [Stmt<'a>], parent: OptNodeId) {
        for stmt in block.iter() {
            self.collect_stmt(stmt, parent);
        }
    }
}


struct CodeInfo<'a> {
    tokens: Vec<kibi::Token<'a>>,
    #[allow(dead_code)] // used by the `NodeRef`s in ast_info.
    ast: Box<kibi::ast::item::Module<'a>>,
    ast_info: AstInfo<'a>,
}

impl<'a> CodeInfo<'a> {
    pub fn new(source: &'a str) -> CodeInfo<'a> {
        let tokens = kibi::Tokenizer::tokenize(source.as_bytes(), true).unwrap();

        let mut p = kibi::Parser::new(&tokens);
        let mut ast = Box::new(p.parse_module(kibi::SourcePos { line: 1, column: 1 }).unwrap());

        let mut i = kibi::infer::Infer::new();
        i.assign_ids(&mut ast);
        i.infer(&mut ast);

        let mut ast_info = AstInfo::new();
        ast_info.collect(&ast);

        let ast_info = unsafe { core::mem::transmute(ast_info) };

        return CodeInfo {
            tokens,
            ast,
            ast_info,
        };
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
struct SourceSpan {
    source_begin: u32,
    source_end:   u32,
    data: SourceSpanData,
}

#[derive(Clone, Copy, Debug)]
enum SourceSpanData {
    None,
    TextRange { text_begin: u32 },
}

#[derive(Clone, Copy, Debug)]
struct TextSpan {
    text_begin: u32,
    text_end:   u32,
    data: TextSpanData,
}

#[derive(Clone, Copy, Debug)]
enum TextSpanData {
    None,
    SourceRange { source_begin: u32 },
}

struct SourceMap {
    line_begins:  Vec<u32>,
    source_spans: Vec<SourceSpan>,
    text_spans:   Vec<TextSpan>,
}

impl SourceMap {
    pub fn source_pos_to_offset(&self, pos: SourcePos) -> u32 {
        if pos.line < 1 {
            return 0;
        }

        self.line_begins[pos.line as usize - 1] + pos.column - 1
    }

    pub fn text_to_source(&self, pos: u32) -> Option<u32> {
        for span in &self.text_spans {
            if pos >= span.text_begin && pos < span.text_end {
                let offset = pos - span.text_begin;
                if let TextSpanData::SourceRange { source_begin } = span.data {
                    return Some(source_begin + offset);
                }
            }
        }
        None
    }

    pub fn source_to_text(&self, pos: u32) -> Option<u32> {
        for span in &self.source_spans {
            if pos >= span.source_begin && pos < span.source_end {
                let offset = pos - span.source_begin;
                if let SourceSpanData::TextRange { text_begin } = span.data {
                    return Some(text_begin + offset);
                }
            }
        }
        None
    }
}


struct CodeView {
    pos: (f32, f32),
    text: String,
    info: CodeInfo<'static>,
    layout: TextLayout<u32>,
    source_map:  SourceMap,
}

impl CodeView {
    pub fn new(fonts: &FontCtx) -> CodeView {
        CodeView {
            pos:    (150., 50.),
            text:   "".into(),
            info:   CodeInfo::new(""),
            layout: TextLayout::new(fonts),
            source_map: SourceMap { line_begins: vec![], source_spans: vec![], text_spans: vec![] },
        }
    }

    pub fn set_text(&mut self, text: &str) {
        self.text.clear();
        self.text.push_str(text);

        let info = CodeInfo::new(&self.text);

        // @todo: looks like offset based source positions are more useful (here).
        self.source_map.line_begins.clear();
        for line in text.lines() {
            self.source_map.line_begins.push((line.as_ptr() as usize - text.as_ptr() as usize) as u32);
        }

        let mut decos = vec![];
        for token in &info.tokens {
            // inserted semicolons.
            if token.source.begin == token.source.end {
                if let kibi::TokenData::Semicolon = token.data {
                    let text_begin = self.source_map.source_pos_to_offset(token.source.begin);
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
                let text_begin = self.source_map.source_pos_to_offset(token.source.begin);
                let text_end   = self.source_map.source_pos_to_offset(token.source.end);
                let class = TokenClass::from_data(token.data);
                decos.push(Decoration { text_begin, text_end,
                    data: DecorationData::Style { color: class.color() }
                });
            }
        }
        // decos are already sorted.

        self.info = unsafe { core::mem::transmute(info) };

        // update text layout & mappings.
        self.layout.clear();
        self.source_map.source_spans.clear();
        self.source_map.text_spans.clear();
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

                        self.source_map.source_spans.push(SourceSpan {
                            source_begin,
                            source_end,
                            data: SourceSpanData::TextRange { text_begin },
                        });
                        self.source_map.text_spans.push(TextSpan {
                            text_begin,
                            text_end,
                            data: TextSpanData::SourceRange { source_begin },
                        });
                    }

                    match &next_deco.data {
                        DecorationData::Style { color } => {
                            let source_begin = deco_begin as u32;
                            let source_end   = deco_end   as u32;

                            let text_begin = self.layout.text().len() as u32;
                            self.layout.append_ex(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, *color);
                            let text_end = self.layout.text().len() as u32;

                            self.source_map.source_spans.push(SourceSpan {
                                source_begin,
                                source_end,
                                data: SourceSpanData::TextRange { text_begin },
                            });
                            self.source_map.text_spans.push(TextSpan {
                                text_begin,
                                text_end,
                                data: TextSpanData::SourceRange { source_begin },
                            });
                        }

                        DecorationData::Replace { text, color } => {
                            let source_begin = deco_begin as u32;
                            let source_end   = deco_end   as u32;

                            let text_begin = self.layout.text().len() as u32;
                            self.layout.append_ex(text, FaceId::DEFAULT, font_size, *color);
                            let text_end = self.layout.text().len() as u32;

                            self.source_map.source_spans.push(SourceSpan {
                                source_begin,
                                source_end,
                                data: SourceSpanData::None,
                            });
                            self.source_map.text_spans.push(TextSpan {
                                text_begin,
                                text_end,
                                data: TextSpanData::None,
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

                    self.source_map.source_spans.push(SourceSpan {
                        source_begin,
                        source_end,
                        data: SourceSpanData::TextRange { text_begin },
                    });
                    self.source_map.text_spans.push(TextSpan {
                        text_begin,
                        text_end,
                        data: TextSpanData::SourceRange { source_begin },
                    });

                    text_cursor = text.len();
                }
            }
        }
    }

    pub fn update(&mut self, window: &Window, offset: (f32, f32), r: &mut Renderer) {
        let (mx, my) = window.get_mouse_pos(minifb::MouseMode::Pass).unwrap();
        let mx = mx + offset.0;
        let my = my + offset.1;
        let mhit = self.layout.hit_test_pos(mx - self.pos.0, my - self.pos.1);

        let mut hover     = None;
        let mut highlight = None;

        'foo: {
            if mhit.out_of_bounds[0] || mhit.out_of_bounds[1] { break 'foo }

            let Some(source_pos) = self.source_map.text_to_source(mhit.text_pos_left) else { break 'foo };

            for info in self.info.ast_info.nodes.iter().rev() {
                let begin = self.source_map.source_pos_to_offset(info.source_range.begin);
                let end   = self.source_map.source_pos_to_offset(info.source_range.end);

                if source_pos < begin || source_pos >= end { continue }

                let Some(text_first) = self.source_map.source_to_text(begin)   else { continue };
                let Some(text_last)  = self.source_map.source_to_text(end - 1) else { continue };

                hover = Some((text_first, text_last, info));

                if let NodeRef::Expr(expr) = info.node_ref {
                    if let ExprData::Ident(ident) = &expr.data {
                        let info = ident.info.unwrap();
                        match info.target {
                            expr::IdentTarget::Item(item) => {
                                let item_info = &self.info.ast_info.items[item];
                                let node_info = &self.info.ast_info.nodes[item_info.node_id];
                                let begin = self.source_map.source_pos_to_offset(node_info.source_range.begin);
                                let end   = self.source_map.source_pos_to_offset(node_info.source_range.end);
                                if let (Some(text_first), Some(text_last)) = (
                                    self.source_map.source_to_text(begin),
                                    self.source_map.source_to_text(end - 1))
                                {
                                    highlight = Some((text_first, text_last));
                                }
                            }

                            expr::IdentTarget::Local { node, local: _ } => {
                                let node_info = &self.info.ast_info.nodes[node];
                                let begin = self.source_map.source_pos_to_offset(node_info.source_range.begin);
                                let end   = self.source_map.source_pos_to_offset(node_info.source_range.end);
                                if let (Some(text_first), Some(text_last)) = (
                                    self.source_map.source_to_text(begin),
                                    self.source_map.source_to_text(end - 1))
                                {
                                    highlight = Some((text_first, text_last));
                                }
                            }

                            expr::IdentTarget::Dynamic => {
                                highlight = Some((text_first, text_last));
                            }
                        }
                    }
                    else if let ExprData::Continue(cont) = &expr.data {
                        let info = cont.info.unwrap();
                        if let Some(info) = info {
                            let node_info = &self.info.ast_info.nodes[info.node];
                            let begin = self.source_map.source_pos_to_offset(node_info.source_range.begin);
                            let end   = self.source_map.source_pos_to_offset(node_info.source_range.end);
                            if let (Some(text_first), Some(text_last)) = (
                                self.source_map.source_to_text(begin),
                                self.source_map.source_to_text(end - 1))
                            {
                                highlight = Some((text_first, text_last));
                            }
                        }
                    }
                    else if let ExprData::Break(bkr) = &expr.data {
                        let info = bkr.info.unwrap();
                        if let Some(info) = info {
                            let node_info = &self.info.ast_info.nodes[info.node];
                            let begin = self.source_map.source_pos_to_offset(node_info.source_range.begin);
                            let end   = self.source_map.source_pos_to_offset(node_info.source_range.end);
                            if let (Some(text_first), Some(text_last)) = (
                                self.source_map.source_to_text(begin),
                                self.source_map.source_to_text(end - 1))
                            {
                                highlight = Some((text_first, text_last));
                            }
                        }
                    }
                }

                break;
            }
        }


        let view_x0 = self.pos.0 - offset.0;
        let view_y0 = self.pos.1 - offset.1;
        let view_x0i = view_x0.floor() as i32;
        let view_y0i = view_y0.floor() as i32;

        r.fill_rect(
            view_x0, view_y0,
            self.layout.width(), self.layout.height(),
            &raqote::Source::Solid(raqote::SolidSource::from_unpremultiplied_argb(255, 30, 35, 40)),
            &Default::default());

        if let Some((first, last, info)) = hover {
            self.layout.hit_test_text_ranges(first, last + 1, |range| {
                let x0 = (view_x0 + range.x0).floor();
                let x1 = (view_x0 + range.x1).floor();
                let y0 = (view_y0 + range.y).floor();
                let y1 = (view_y0 + range.y + range.line_height).floor();
                r.fill_rect(
                    x0, y0,
                    x1 - x0, y1 - y0,
                    &raqote::Source::Solid(raqote::SolidSource::from_unpremultiplied_argb(255, 50, 55, 60)),
                    &Default::default());
            });

            let m = self.layout.hit_test_text_pos(first);
            let dump = format!("{:?}", info.node_id);
            let mut temp_layout = TextLayout::new(r.fonts());
            temp_layout.append_ex(&dump, FaceId::DEFAULT, 16., TokenClass::Default.color());
            r.draw_text_layout_abs(view_x0i - 125, view_y0i + m.y as i32, &temp_layout);
        }

        if let Some((first, last)) = highlight {
            self.layout.hit_test_text_ranges(first, last + 1, |range| {
                let x0 = (view_x0 + range.x0).floor();
                let x1 = (view_x0 + range.x1).floor();
                let y0 = (view_y0 + range.y).floor();
                let y1 = (view_y0 + range.y + range.line_height).floor();
                r.fill_rect(
                    x0, y0,
                    x1 - x0, y1 - y0,
                    &raqote::Source::Solid(raqote::SolidSource::from_unpremultiplied_argb(255, 64, 73, 91)),
                    &Default::default());
            });
        }

        r.draw_text_layout_abs(view_x0i, view_y0i, &self.layout);
    }
}


struct Explorer {
    window:   Window,
    renderer: Renderer,
    offset:     (f32, f32),
    last_mouse: (f32, f32),
    code:     CodeView,
}

impl Explorer {
    pub fn new() -> Explorer {
        let mut window = Window::new("kibi explorer", 800, 600, WindowOptions {
            resize: true,
            ..Default::default()
        }).unwrap();

        window.limit_update_rate(Some(std::time::Duration::from_millis(5)));

        let fonts = FontCtx::new();
        fonts.add_face("Source Code Pro", Bold(false), Italic(false), include_bytes!("../res/SourceCodePro-Regular.ttf"));

        Explorer {
            window,
            renderer: Renderer::new(&fonts),
            offset:     (0., 0.),
            last_mouse: (0., 0.),
            code:     CodeView::new(&fonts),
        }
    }

    pub fn run(&mut self) {
        while self.window.is_open() {
            let size = self.window.get_size();

            let (mx, my) = self.window.get_mouse_pos(minifb::MouseMode::Pass).unwrap();
            let mdx = mx - self.last_mouse.0;
            let mdy = my - self.last_mouse.1;
            if self.window.get_mouse_down(minifb::MouseButton::Right) {
                self.offset.0 -= mdx;
                self.offset.1 -= mdy;
            }
            self.last_mouse = (mx, my);

            let r = &mut self.renderer;
            r.set_size(size.0 as u32, size.1 as u32);

            r.clear(13, 16, 23);

            self.code.update(&self.window, self.offset, r);

            self.window.update_with_buffer(r.data(), size.0, size.1).unwrap();
        }
    }
}


fn main() {
    #[cfg(target_os="windows")] {
        // otherwise `Sleep` resolution is 16 ms.
        // at least on my machine.
        // and that feels horrible.
        // we of course wanna do vsync eventually.
        unsafe { windows_sys::Win32::Media::timeBeginPeriod(1); }
    }

    let mut e = Explorer::new();
    e.code.set_text(include_str!("../../fib.kb"));
    e.run();
}

