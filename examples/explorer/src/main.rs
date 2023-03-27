use minifb::{Window, WindowOptions};
use kibi::index_vec::*;
use kibi::ast::*;

// @temp
#[allow(dead_code)]


mod renderer;
use renderer::*;

mod gui;
use gui::{*, Key};


struct ItemInfo {
    item_id: ItemId,
    #[allow(dead_code)] // @temp.
    node_id: NodeId,
    #[allow(dead_code)] // @temp.
    source_range: SourceRange,
}

#[derive(Debug)]
enum NodeRef<'a> {
    None,
    Stmt(&'a Stmt<'a>),
    Expr(&'a Expr<'a>),
}

#[derive(Debug)]
struct NodeInfo<'a> {
    #[allow(dead_code)] // @temp.
    parent:  OptNodeId,
    node_id: NodeId,
    #[allow(dead_code)] // @temp.
    node_ref: NodeRef<'a>,
    #[allow(dead_code)] // @temp.
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

    #[allow(dead_code)] // @important: used by the `NodeRef`s in ast_info.
    ast: Box<kibi::ast::item::Module<'a>>,
    ast_info: AstInfo<'a>,

    funcs: IndexVec<kibi::FunctionId, kibi::FuncDesc>,
    items: IndexVec<ItemId, kibi::bbir::Item>,
    #[allow(dead_code)] // @temp.
    debug_info: IndexVec<kibi::FunctionId, kibi::FunctionDebugInfo>,
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

        let mut builder = kibi::bbir_builder::Builder::new();
        builder.build(&ast);
        let (funcs, items, debug_info) = builder.krate.build();

        return CodeInfo {
            tokens,
            ast,
            ast_info,
            funcs,
            items,
            debug_info,
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
            TokenClass::Default  => color_pre_multiply(0xffbfbdb6),
            TokenClass::Keyword  => color_pre_multiply(0xffff8f40),
            TokenClass::Comment  => color_pre_multiply(0x8cacb6bf),
            TokenClass::Label    => color_pre_multiply(0xffff8f40),
            TokenClass::Operator => color_pre_multiply(0xfff29668),
            TokenClass::Literal  => color_pre_multiply(0xffd2a6ff),
            TokenClass::String   => color_pre_multiply(0xffaad94c),
        }
    }
}


struct CodeView {
    #[allow(dead_code)] // @temp
    pos: (f32, f32),

    font_size: f32,
    inserted_semicolons: bool,
    syntax_highlighting: bool,

    text:  String,
    lines: Vec<u32>,
    info:  CodeInfo<'static>,

    decos: Vec<Decoration>,
}

impl CodeView {
    pub fn new() -> CodeView {
        CodeView {
            pos: (150., 50.),

            font_size: 24.0,
            inserted_semicolons: false,
            syntax_highlighting: true,

            text:   "".into(),
            lines:  vec![],
            info:   CodeInfo::new(""),

            decos: vec![],
        }
    }

    fn source_pos_to_offset(&self, pos: SourcePos) -> u32 {
        if pos.line < 1 { return 0 }

        self.lines[pos.line as usize - 1] + pos.column - 1
    }

    pub fn set_text(&mut self, text: &str) {
        self.text.clear();
        self.text.push_str(text);

        let info = CodeInfo::new(&self.text);
        self.info = unsafe { core::mem::transmute(info) };

        // @todo: looks like offset based source positions are more useful (here).
        self.lines.clear();
        for line in text.lines() {
            self.lines.push((line.as_ptr() as usize - text.as_ptr() as usize) as u32);
        }
        self.lines.push(text.len() as u32);

        self.update_decos();
    }

    fn update_decos(&mut self) {
        self.decos.clear();

        for token in &self.info.tokens {
            // inserted semicolons.
            if token.source.begin == token.source.end {
                assert!(token.data.is_semicolon());

                if self.inserted_semicolons {
                    let text_begin = self.source_pos_to_offset(token.source.begin);
                    self.decos.push(Decoration {
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
                if self.syntax_highlighting {
                    let text_begin = self.source_pos_to_offset(token.source.begin);
                    let text_end   = self.source_pos_to_offset(token.source.end);
                    let class = TokenClass::from_data(token.data);
                    self.decos.push(Decoration { text_begin, text_end,
                        data: DecorationData::Style { color: class.color() }
                    });
                }
            }
        }
        // decos are already sorted.
    }

    pub fn render(&mut self, gui: &mut Gui) -> bool {
        let mut changed = false;
        let mut new_semis  = self.inserted_semicolons;
        let mut new_syntax = self.syntax_highlighting;
        let mut new_font_size = self.font_size;

        fn quote_button_endquote(gui: &mut Gui, title: String) -> WidgetEvents {
            gui.widget_box(Key::Counter, Props::new().with_pointer_events(), |gui| {
                gui.widget_text(Key::Counter, Props::new(), title);
            })
        }

        let mut window_props = Props::new();
        window_props.layout = Layout::Flex(FlexLayout {
            direction: FlexDirection::Column,
            justify:   FlexJustify::Begin,
            align:     FlexAlign::Begin,
        });
        window_props.pos = [Some(self.pos.0), Some(self.pos.1)];

        gui.widget_box(Key::U64(69), window_props, |gui| {
            if quote_button_endquote(gui, format!("inserted semicolons: {}", self.inserted_semicolons)).clicked() {
                new_semis = !self.inserted_semicolons;
                changed = true;
            }

            if quote_button_endquote(gui, format!("syntax highlighting: {}", self.syntax_highlighting)).clicked() {
                new_syntax = !self.syntax_highlighting;
                changed = true;
            }

            if let Some(value) = Slider::render(gui, self.font_size, 12.0, 32.0) {
                new_font_size = value;
                changed = true;
            }

            let mut r = CodeViewRenderer {
                deco_index: 0,
                line_begin: 0,
                line_index: 1,
            };
            r.render(self, gui);
        });

        self.inserted_semicolons = new_semis;
        self.syntax_highlighting = new_syntax;
        self.font_size = new_font_size;
        if changed {
            self.update_decos();
        }

        changed
    }
}


// @temp: put on theme gui context whatever thing.
struct Slider {
}

impl Slider {
    pub fn render(gui: &mut Gui, value: f32, min: f32, max: f32) -> Option<f32> {
        let mut new_value = value;

        let width  = 100.0;
        let height =  24.0;

        let mut slider_props = Props::new().with_pointer_events().with_fill(0xff2A2E37);
        slider_props.size = [Some(width), Some(height)];
        slider_props.layout = Layout::None;

        gui.widget_box(Key::Counter, slider_props, |gui| {
            let t = (value - min) / (max - min);
            let head_size = 20.0;

            let mut head_props = Props::new().with_pointer_events().with_fill(0xffd0d0d0);
            head_props.pos  = [Some(t * (width - head_size)), Some((height - head_size)/2.0)];
            head_props.size = [Some(head_size), Some(head_size)];

            let events = gui.widget_box(Key::Counter, head_props, |_| {});
            if events.active_begin() {
                gui.capture_mouse(&events);
            }
            if gui.has_mouse_capture(&events) && events.mouse_moved() {
                let offset_target = gui.mouse_capture_pos()[0];
                let offset = events.local_mouse_pos()[0];

                let dx = offset - offset_target;
                let dv = dx / (width - head_size) * (max - min);

                new_value = (value + dv).clamp(min, max);
            }

            let props = gui.edit_props_no_render(&events);
            if events.active {
                props.fill_color = 0xffa0a0a0;
            }
            else if events.hovered {
                props.fill_color = 0xffffffff;
            }
            if events.hover_changed() || events.active_changed() {
                gui.mark_for_render(&events);
            }
        });

        (new_value != value).then_some(new_value)
    }
}


struct CodeViewRenderer {
    deco_index: usize,
    line_begin: usize,
    line_index: usize,
}

impl CodeViewRenderer {
    fn render_line(&mut self, line_begin: usize, line_end: usize, view: &CodeView, gui: &mut Gui) {
        let mut text_cursor = line_begin;
        while text_cursor < line_end {
            let next_deco =
                view.decos.get(self.deco_index)
                .filter(|deco| deco.text_begin as usize <= line_end);

            if let Some(next_deco) = next_deco {
                let deco_begin = (next_deco.text_begin as usize).max(line_begin);
                let deco_end   = (next_deco.text_end   as usize).min(line_end);
                debug_assert!(deco_begin <= deco_end);

                if text_cursor < deco_begin {
                    let source_begin = text_cursor as u32;
                    let source_end   = deco_begin  as u32;
                    gui.widget_text(Key::Counter,
                        Props {
                            font_face: FaceId::DEFAULT,
                            font_size: view.font_size,
                            text_color: TokenClass::Default.color(),
                            ..Default::default()
                        },
                        view.text[source_begin as usize .. source_end as usize].to_string());
                }

                match &next_deco.data {
                    DecorationData::Style { color } => {
                        let source_begin = deco_begin as u32;
                        let source_end   = deco_end   as u32;
                        gui.widget_text(Key::Counter,
                            Props {
                                font_face: FaceId::DEFAULT,
                                font_size: view.font_size,
                                text_color: *color,
                                ..Default::default()
                            },
                            view.text[source_begin as usize .. source_end as usize].to_string());
                    }

                    DecorationData::Replace { text, color } => {
                        gui.widget_text(Key::Counter,
                            Props {
                                font_face: FaceId::DEFAULT,
                                font_size: view.font_size,
                                text_color: *color,
                                ..Default::default()
                            },
                            text.to_string());
                    }
                }

                if next_deco.text_end as usize <= line_end {
                    self.deco_index += 1;
                }
                text_cursor = deco_end;
            }
            else {
                let source_begin = text_cursor as u32;
                let source_end   = line_end    as u32;
                gui.widget_text(Key::Counter,
                    Props {
                        font_face: FaceId::DEFAULT,
                        font_size: view.font_size,
                        text_color: TokenClass::Default.color(),
                        ..Default::default()
                    },
                    view.text[source_begin as usize .. source_end as usize].to_string());

                text_cursor = line_end;
            }
        }
    }

    fn render_reg(&mut self, func: kibi::FunctionId, pc: u16, reg: u8, view: &CodeView, gui: &mut Gui) {
        let _ = (func, pc);

        let events = gui.widget_text(Key::Counter,
            Props {
                font_face: FaceId::DEFAULT,
                font_size: view.font_size,
                text_color: TokenClass::Default.color(),
                pointer_events: true,
                ..Default::default()
            },
            format!("r{reg}"));

        if let Some((dx, dy)) = events.mouse_delta() { println!("{func}.{pc}.{reg} mouse moved by {dx} {dy}") }
        if events.mouse_went_down(MouseButton::Left) { println!("{func}.{pc}.{reg} left down") }
        if events.mouse_went_up(MouseButton::Left)   { println!("{func}.{pc}.{reg} left up") }
    }

    fn render_instr(&mut self, instr: &kibi::bytecode::Instr, func_id: kibi::FunctionId, view: &CodeView, gui: &mut Gui) {
        fn text(text: String, color: u32, view: &CodeView, gui: &mut Gui) {
            gui.widget_text(Key::Counter,
                Props {
                    font_face: FaceId::DEFAULT,
                    font_size: view.font_size,
                    text_color: color,
                    ..Default::default()
                },
                text);
        }

        let name = instr.name();

        gui.widget_box(Key::Counter, Props::new(), |gui| {
            gui.widget_text(Key::Counter,
                Props {
                    font_face: FaceId::DEFAULT,
                    font_size: view.font_size,
                    text_color: TokenClass::Comment.color(),
                    ..Default::default()
                },
                format!("{:03} ", instr.pc));

            gui.widget_text(Key::Counter,
                Props {
                    font_face: FaceId::DEFAULT,
                    font_size: view.font_size,
                    text_color: TokenClass::Default.color(),
                    ..Default::default()
                },
                format!("{:11} ", name));

            use kibi::bytecode::InstrData::*;
            match &instr.data {
                Nop => (),
                Unreachable => (),

                LoadNil  { dst } |
                LoadEnv  { dst } |
                LoadUnit { dst } |
                MapNew   { dst } => {
                    self.render_reg(func_id, instr.pc + 1, *dst, view, gui);
                }

                Swap { dst, src } => {
                    self.render_reg(func_id, instr.pc, *dst, view, gui);
                    text(format!(", "), TokenClass::Default.color(), view, gui);
                    self.render_reg(func_id, instr.pc, *src, view, gui);
                }

                Copy { dst, src } |
                Op1  { dst, src } => {
                    self.render_reg(func_id, instr.pc + 1, *dst, view, gui);
                    text(format!(", "), TokenClass::Default.color(), view, gui);
                    self.render_reg(func_id, instr.pc, *src, view, gui);
                }

                Op2 { dst, src1, src2 } => {
                    self.render_reg(func_id, instr.pc + 1, *dst, view, gui);
                    text(format!(", "), TokenClass::Default.color(), view, gui);
                    self.render_reg(func_id, instr.pc, *src1, view, gui);
                    text(format!(", "), TokenClass::Default.color(), view, gui);
                    self.render_reg(func_id, instr.pc, *src2, view, gui);
                }


                LoadBool { dst, value } => {
                    self.render_reg(func_id, instr.pc + 1, *dst, view, gui);
                    text(format!(", "), TokenClass::Default.color(), view, gui);
                    text(format!("{value}"), TokenClass::from_data(kibi::TokenData::Bool(false)).color(), view, gui);
                }

                LoadInt   { dst, value } |
                AddInt    { dst, value } => {
                    self.render_reg(func_id, instr.pc + 1, *dst, view, gui);
                    text(format!(", "), TokenClass::Default.color(), view, gui);
                    text(format!("#{value}"), TokenClass::from_data(kibi::TokenData::Number("")).color(), view, gui);
                }

                LoadConst { dst, index } => {
                    self.render_reg(func_id, instr.pc + 1, *dst, view, gui);
                    text(format!(", "), TokenClass::Default.color(), view, gui);
                    // @todo: render the const's value.
                    text(format!("c{index}"), TokenClass::Default.color(), view, gui);
                }

                ListNew  { dst, values } |
                TupleNew { dst, values } => {
                    let _ = (dst, values);
                    text(format!("..."), TokenClass::Comment.color(), view, gui);
                }


                ReadPath { dst, base, keys } => {
                    let _ = (dst, base, keys);
                    text(format!("..."), TokenClass::Comment.color(), view, gui);
                }

                WritePath { base, keys, value } => {
                    let _ = (base, keys, value);
                    text(format!("..."), TokenClass::Comment.color(), view, gui);
                }


                Jump { target } => {
                    text(format!("{target}"), TokenClass::Default.color(), view, gui);
                }

                JumpC1 { target, src } => {
                    self.render_reg(func_id, instr.pc, *src, view, gui);
                    text(format!(", {target}"), TokenClass::Default.color(), view, gui);
                }

                Call { dst, func, args } => {
                    let _ = (dst, func, args);
                    text(format!("..."), TokenClass::Comment.color(), view, gui);
                }

                Ret { src } => {
                    self.render_reg(func_id, instr.pc, *src, view, gui);
                }
            }
            text(format!("\n"), TokenClass::Default.color(), view, gui);
        });
    }

    fn render(&mut self, view: &CodeView, gui: &mut Gui) {
        let mut codes = vec![];
        // module code.
        codes.push(kibi::bytecode::ByteCodeDecoder::decode({
            let code = &view.info.funcs.inner()[0].code;
            let kibi::FuncCode::ByteCode(code) = code else { unreachable!() };
            code
        }).unwrap());

        let mut func_queue_rev = {
            let items = &view.info.ast_info.items;

            // functions sorted by line begin.
            let mut queue = Vec::with_capacity(items.len());
            for item in items {
                let info = &view.info.items[item.item_id].data;
                if let kibi::bbir::ItemData::Func(func) = *info {
                    let code = &view.info.funcs[func].code;
                    let kibi::FuncCode::ByteCode(code) = code else { unreachable!() };

                    let code_index = codes.len();
                    codes.push(kibi::bytecode::ByteCodeDecoder::decode(code).unwrap());

                    queue.push((func, code_index, item.source_range.begin.line, item.source_range.end.line));
                }
            }
            queue.sort_by(|(_, _, l1, _), (_, _, l2, _)| l2.cmp(l1));

            // add module function.
            queue.push((kibi::FunctionId::new_unck(0), 0, 0, view.lines.len() as u32));

            queue
        };

        let mut func_stack = vec![];

        while self.line_index < view.lines.len() {
            // add beginning funcs.
            while let Some((func, code, line_begin, line_end)) = func_queue_rev.last().copied() {
                if line_begin as usize <= self.line_index {
                    func_stack.push((func, code, 0, line_end));
                    func_queue_rev.pop();
                }
                else { break }
            }


            // code line.
            let line_begin = self.line_begin;
            let line_end = view.lines[self.line_index] as usize;
            gui.widget_box(Key::Counter, Props::new(), |gui| {
                self.render_line(line_begin, line_end, view, gui);
            });
            self.line_begin = line_end;
            self.line_index += 1;

            // bytecode instructions.
            if let Some((func_id, code, ic, _)) = func_stack.last_mut() {
                let pc_to_node = &view.info.debug_info[*func_id].pc_to_node;

                let code = &codes[*code];

                while *ic < code.len() {
                    let instr = &code[*ic];
                    let node_id = pc_to_node[instr.pc as usize];

                    // stop if instr is associated with next line.
                    if let Some(node_id) = node_id.to_option() {
                        let range = view.info.ast_info.nodes[node_id].source_range;
                        if range.begin.line as usize >= self.line_index {
                            break;
                        }
                    }

                    self.render_instr(instr, *func_id, view, gui);
                    *ic += 1;
                }
            }

            // remove ending funcs.
            while let Some((_, code, ic, line_end)) = func_stack.last().copied() {
                if line_end as usize <= self.line_index {
                    assert_eq!(ic, codes[code].len());
                    func_stack.pop();
                }
                else { break }
            }
        }

        assert_eq!(func_stack.len(), 0);
    }
}


struct Explorer {
    window:   Window,
    renderer: Renderer,
    gui: Gui,
    code: CodeView,
    offset: [f32; 2],
    down_offset: [f32; 2],
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
            gui: Gui::new(&fonts),
            code: CodeView::new(),
            offset: [0.0; 2],
            down_offset: [0.0; 2],
        }
    }

    pub fn run(&mut self) {
        let mut never_updated = true;

        while self.window.is_open() {
            let size = self.window.get_size();

            let (mx, my) = self.window.get_mouse_pos(minifb::MouseMode::Pass).unwrap();

            let mdown_left   = self.window.get_mouse_down(minifb::MouseButton::Left);
            let mdown_middle = self.window.get_mouse_down(minifb::MouseButton::Middle);
            let mdown_right  = self.window.get_mouse_down(minifb::MouseButton::Right);


            let gui = &mut self.gui;

            let root_size = [size.0 as f32, size.1 as f32];

            let mut changed = never_updated;
            let mut render  = changed;
            for _ in 0..10 {
                let size_changed = gui.root_size(root_size);
                render = render | size_changed;

                if !size_changed
                && !gui.mouse_move(mx, my)
                && !gui.mouse_down(mdown_left,   gui::MouseButton::Left)
                && !gui.mouse_down(mdown_middle, gui::MouseButton::Middle)
                && !gui.mouse_down(mdown_right,  gui::MouseButton::Right)
                && !changed {
                    break;
                }

                let root_props = Props::new();

                changed = gui.update(root_props, |gui| {
                    let mut changed = false;

                    let mut canvas_props = Props::new().with_pointer_events();
                    canvas_props.layout = Layout::None;
                    canvas_props.size = [Some(root_size[0]),  Some(root_size[1])];

                    let events = gui.widget_box(Key::Counter, canvas_props, |gui| {
                        let mut body_props = Props::new();
                        body_props.layout = Layout::None;
                        body_props.pos    = [Some(-self.offset[0]), Some(-self.offset[1])];

                        gui.widget_box(Key::Counter, body_props, |gui| {
                            changed = self.code.render(gui);
                        });
                    });

                    if events.mouse_went_down(MouseButton::Right) {
                        gui.capture_mouse(&events);
                        self.down_offset = self.offset;
                    }
                    if gui.has_mouse_capture(&events) && events.mouse_moved() {
                        let pos_target = gui.mouse_capture_pos();
                        let pos = events.local_mouse_pos();
                        self.offset[0] = self.down_offset[0] + (pos_target[0] - pos[0]);
                        self.offset[1] = self.down_offset[1] + (pos_target[1] - pos[1]);
                        changed = true;
                    }

                    changed
                });

                render = render | changed | gui.needs_render();
                never_updated = false;
            }

            let r = &mut self.renderer;
            if render {
                r.set_size(size.0 as u32, size.1 as u32);

                r.clear(13, 16, 23);

                gui.draw(r);
            }
            // we love to burn cpu cycles, don't we.
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

    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 {
        assert_eq!(args.len(), 2);

        let path = &args[1];
        let source = std::fs::read_to_string(path).unwrap();
        e.code.set_text(&source);
    }
    else {
        let source = include_str!("../../fib.kb");
        e.code.set_text(source);
    }

    e.run();
}

