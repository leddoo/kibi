use core::cell::Cell;
use minifb::{Window, WindowOptions};
use kibi::index_vec::*;
use kibi::ast::*;

// @temp
#[allow(dead_code)]


mod renderer;
use renderer::*;

mod gui;
use gui::{*, Key};


// @temp

mod builtin {
    use kibi::*;

    pub(crate) fn print(vm: &mut Vm) -> VmResult<NativeFuncReturn> {
        vm.generic_print(0);
        return Ok(NativeFuncReturn::Unit);
    }
    pub(crate) const PRINT: FuncDesc = FuncDesc {
        code: FuncCode::Native(NativeFuncPtrEx(print)),
        constants: vec![],
        num_params: 1,
        stack_size: 1,
    };

    pub(crate) fn println(vm: &mut Vm) -> VmResult<NativeFuncReturn> {
        vm.generic_print(0);
        println!();
        return Ok(NativeFuncReturn::Unit);
    }
    pub(crate) const PRINTLN: FuncDesc = FuncDesc {
        code: FuncCode::Native(NativeFuncPtrEx(println)),
        constants: vec![],
        num_params: 1,
        stack_size: 1,
    };

}



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
    TextColor { color: u32 },
    FillColor { color: u32 },
    Insert    { text: String, color: u32 },
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


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TriState {
    Default,
    False,
    True,
}


struct VisualLine {
    spans: Vec<VisualSpan>,

    indent: u32,
    number: u32,

    instrs_begin: u32,
    instrs_end:   u32,
    instrs_gap:   Option<u32>,

    show_instrs: Cell<TriState>,
    instrs_visible: bool,
}

struct VisualSpan {
    text: String,
    face: FaceId,
    color: u32,
    fill:  Option<u32>,
}

struct VisualInstr {
    func: kibi::FunctionId,
    node: OptNodeId,
    line_begin: Option<u32>,
    data: kibi::bytecode::Instr,
}


struct CodeView {
    #[allow(dead_code)] // @temp
    pos: (f32, f32),

    font_size:    f32,
    font_size_bc: f32,
    inserted_semicolons: bool,
    syntax_highlighting: bool,

    show_instrs: TriState,
    show_instrs_dirty: Cell<bool>,

    // source range highlighting.
    hl_instr_node: Cell<OptNodeId>,

    text: String,
    line_ends: Vec<u32>,
    info: CodeInfo<'static>,
    instrs: Vec<VisualInstr>,

    decos: Vec<Decoration>,
    vlines: Vec<VisualLine>,

    vm: kibi::Vm,
}

impl CodeView {
    pub fn new() -> CodeView {
        CodeView {
            pos: (150., 50.),

            font_size: 24.0,
            font_size_bc: 0.0,
            inserted_semicolons: false,
            syntax_highlighting: true,

            show_instrs: TriState::Default,
            show_instrs_dirty: Cell::new(false),

            hl_instr_node: Cell::new(None.into()),

            text:   "".into(),
            line_ends:  vec![],
            info:   CodeInfo::new(""),

            decos: vec![],
            instrs: vec![],
            vlines: vec![],

            vm: kibi::Vm::new(),
        }
    }

    fn source_pos_to_offset(&self, pos: SourcePos) -> u32 {
        if pos.line < 1 { return 0 }

        self.line_ends[pos.line as usize - 1] + pos.column - 1
    }

    pub fn set_text(&mut self, text: &str) {
        self.text.clear();
        self.text.push_str(text);

        let info = CodeInfo::new(&self.text);
        self.info = unsafe { core::mem::transmute(info) };

        self.vm = kibi::Vm::new();
        self.vm.add_func("print", builtin::PRINT);
        self.vm.add_func("println", builtin::PRINTLN);
        self.vm.load_crate(0, &self.info.funcs.inner(), &self.info.items.inner());
        self.vm.set_instr_limit(0);
        self.vm.call(0, 0, &[]).unwrap();

        self.update_instrs();

        // @todo: looks like offset based source positions are more useful (here).
        self.line_ends.clear();
        for line in text.lines() {
            self.line_ends.push((line.as_ptr() as usize - text.as_ptr() as usize) as u32);
        }
        self.line_ends.push(text.len() as u32);

        self.update_decos();
        self.update_vlines();
        self.update_show_instrs();
    }

    fn update_instrs(&mut self) {
        let items = &self.info.ast_info.items;

        // functions sorted by line begin.
        let mut funcs = Vec::with_capacity(items.len());
        for item in &items.inner()[1..] {
            let info = &self.info.items[item.item_id].data;
            if let kibi::bbir::ItemData::Func(func) = *info {
                let source = item.source_range;
                funcs.push((func, source.begin.line));
            }
        }
        // add module function.
        funcs.sort_by(|(_, l1), (_, l2)| l1.cmp(l2));

        self.instrs.clear();

        fn collect_instrs(func: kibi::FunctionId, funcs: &mut &[(kibi::FunctionId, u32)], info: &CodeInfo, instrs: &mut Vec<VisualInstr>) {
            let code = &info.funcs[func].code;
            let kibi::FuncCode::ByteCode(code) = code else { unreachable!() };
            let code = kibi::bytecode::ByteCodeDecoder::decode(code).unwrap();

            let pc_to_node = &info.debug_info[func].pc_to_node;

            for instr in code {
                let node = pc_to_node[instr.pc as usize];

                let line_begin = node.to_option().map(|node_id|
                    info.ast_info.nodes[node_id].source_range.begin.line);

                while let Some(line) = line_begin {
                    if let Some(((func, begin), rest)) = funcs.split_first() {
                        if *begin < line {
                            *funcs = rest;
                            collect_instrs(*func, funcs, info, instrs);
                            continue;
                        }
                    }
                    break;
                }

                instrs.push(VisualInstr { func, node, line_begin, data: instr });
            }
        }

        let mut funcs = funcs.as_slice();
        collect_instrs(kibi::FunctionId::new_unck(0), &mut funcs, &self.info, &mut self.instrs);

        while let Some(((func, _), rest)) = funcs.split_first() {
            funcs = rest;
            collect_instrs(*func, &mut funcs, &self.info, &mut self.instrs);
        }
    }

    fn update_decos(&mut self) {
        self.decos.clear();

        // syntax highlighting & inserted semicolons.
        for token in &self.info.tokens {
            if token.source.begin == token.source.end {
                assert!(token.data.is_semicolon());

                if self.inserted_semicolons {
                    let text_begin = self.source_pos_to_offset(token.source.begin);
                    self.decos.push(Decoration {
                        text_begin,
                        text_end: text_begin,
                        data: DecorationData::Insert {
                            text: ";".to_string(),
                            color: TokenClass::Comment.color(),
                        },
                    });
                }
            }
            else {
                if self.syntax_highlighting {
                    let text_begin = self.source_pos_to_offset(token.source.begin);
                    let text_end   = self.source_pos_to_offset(token.source.end);
                    let class = TokenClass::from_data(token.data);
                    self.decos.push(Decoration { text_begin, text_end,
                        data: DecorationData::TextColor { color: class.color() }
                    });
                }
            }
        }

        // highlights.
        if let Some(node) = self.hl_instr_node.get().to_option() {
            let source = self.info.ast_info.nodes[node].source_range;
            let text_begin = self.source_pos_to_offset(source.begin);
            let text_end   = self.source_pos_to_offset(source.end);
            self.decos.push(Decoration {
                text_begin,
                text_end,
                data: DecorationData::FillColor { color: 0xff414752 },
            });
        }

        self.decos.sort_by(|d1, d2| d1.text_begin.cmp(&d2.text_begin));
    }

    fn update_vlines(&mut self) {
        let mut prev_line_end = 0;
        let mut deco_cursor   = 0;
        let mut instr_cursor  = 0;

        let mut active_decos: Vec<(usize, u32)> = vec![];

        let prev_show_instrs: Vec<_> = self.vlines.iter().map(|line| line.show_instrs.get()).collect();

        self.vlines.clear();
        for line_index in 1..self.line_ends.len() {
            let line_begin = prev_line_end;
            let line_end   = self.line_ends[line_index];
            prev_line_end = line_end;

            let line_number = line_index as u32;

            // build spans.
            let spans = {
                let mut spans = vec![];

                let mut text_cursor = line_begin;
                while text_cursor < line_end {
                    let next_begin =
                        if deco_cursor < self.decos.len() {
                            let begin = self.decos[deco_cursor].text_begin;
                            begin.min(line_end)
                        }
                        else { line_end };

                    let next_end = {
                        let mut min_end = next_begin + 1;
                        for (_, end) in active_decos.iter().copied() {
                            min_end = min_end.min(end);
                        }
                        min_end
                    };

                    let source_begin = text_cursor;
                    let source_end   = next_end.min(next_begin);
                    if source_begin != source_end {
                        let mut span = VisualSpan {
                            text:  self.text[source_begin as usize .. source_end as usize].to_string(),
                            face:  FaceId::DEFAULT,
                            color: TokenClass::Default.color(),
                            fill:  None,
                        };

                        for (deco, _) in active_decos.iter().copied() {
                            match self.decos[deco].data {
                                DecorationData::TextColor { color } => span.color = color,
                                DecorationData::FillColor { color } => span.fill  = Some(color),
                                DecorationData::Insert { text: _, color: _ } => unreachable!(),
                            }
                        }

                        spans.push(span);
                    }

                    if next_end <= source_end {
                        active_decos.retain(|(_, end)| *end > source_end);
                    }
                    else if next_begin < line_end {
                        let deco = &self.decos[deco_cursor];
                        if let DecorationData::Insert { text, color } = &deco.data {
                            spans.push(VisualSpan {
                                text:  text.to_string(),
                                face:  FaceId::DEFAULT,
                                color: *color,
                                fill:  None,
                            });
                        }
                        else {
                            active_decos.push((deco_cursor, deco.text_end));
                        }
                        deco_cursor += 1;
                    }

                    text_cursor = source_end;
                }

                spans
            };

            // bytecode instructions.
            let instrs_begin   = instr_cursor;
            let mut instrs_gap = None;
            while instr_cursor < self.instrs.len() {
                let instr = &self.instrs[instr_cursor];

                let mut is_for_current_line = false;
                if let Some(line) = instr.line_begin {
                    let line = line as usize;

                    is_for_current_line = line == line_index;
                    if line > line_index {
                        break;
                    }
                }

                if !is_for_current_line && instr_cursor > instrs_begin && instrs_gap.is_none() {
                    instrs_gap = Some(instr_cursor as u32);
                }

                instr_cursor += 1;
            }

            let indent =
                self.text[line_begin as usize .. line_end as usize].char_indices()
                .find(|(_, ch)| !ch.is_ascii_whitespace())
                .map(|(indent, _)| indent)
                .unwrap_or(0) as u32;

            let show_instrs = prev_show_instrs.get(self.vlines.len()).copied().unwrap_or(TriState::Default);

            self.vlines.push(VisualLine {
                spans,
                indent,
                number: line_number,
                instrs_begin: instrs_begin as u32,
                instrs_end:   instr_cursor as u32,
                instrs_gap,
                show_instrs: Cell::new(show_instrs),
                instrs_visible: false,
            });
        }
    }

    fn update_show_instrs(&mut self) {
        let global_hide = self.show_instrs == TriState::False;
        let global_show = self.show_instrs == TriState::True;

        for line in &mut self.vlines {
            let hide = line.show_instrs.get() == TriState::False;
            let show = line.show_instrs.get() == TriState::True;
            line.instrs_visible = global_show && !hide || show && !global_hide;
        }
    }

    pub fn render(&mut self, gui: &mut Gui) -> bool {
        let mut changed = false;
        let mut new_semis  = self.inserted_semicolons;
        let mut new_syntax = self.syntax_highlighting;
        let mut new_font_size = self.font_size;

        let prev_hl_instr_node = self.hl_instr_node.get();
        self.hl_instr_node.set(None.into());

        self.font_size_bc = 0.75 * self.font_size;

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
        // @temp.
        window_props.size[0] = Some(800.0);
        window_props.size[1] = Some(500.0);
        window_props.overflow[0] = Overflow::AutoScroll;
        window_props.overflow[1] = Overflow::AutoScroll;
        window_props.fill = true;
        window_props.fill_color = 0xff20242C;
        window_props.padding = [[24.0; 2]; 2];
        window_props.pointer_events = true;

        gui.widget_box(Key::U64(69), window_props, |gui| {
            if quote_button_endquote(gui, format!("inserted semicolons: {}", self.inserted_semicolons)).clicked() {
                new_semis = !self.inserted_semicolons;
                changed = true;
            }

            if quote_button_endquote(gui, format!("syntax highlighting: {}", self.syntax_highlighting)).clicked() {
                new_syntax = !self.syntax_highlighting;
                changed = true;
            }

            let show_instrs = match self.show_instrs {
                TriState::Default => "per line",
                TriState::False   => "hide",
                TriState::True    => "show",
            };
            if quote_button_endquote(gui, format!("show bytecode: {show_instrs}")).clicked() {
                self.show_instrs = match self.show_instrs {
                    TriState::Default => TriState::False,
                    TriState::False   => TriState::True,
                    TriState::True    => TriState::Default,
                };
                self.show_instrs_dirty.set(true);
                changed = true;
            }

            if let Some(value) = Slider::render(gui, self.font_size, 12.0, 32.0) {
                new_font_size = value;
                changed = true;
            }

            gui.widget_box(Key::Counter, Props::new(), |gui| {
                let mut stack = String::new();
                self.vm.call_stack(|frame| {
                    use core::fmt::Write;
                    write!(&mut stack, "{:?}\n", frame).unwrap();
                });
                if stack.len() == 0 {
                    stack.push_str("<empty>");
                }

                gui.widget_text(Key::Counter, Props::new(), stack);

                if quote_button_endquote(gui, format!("step")).clicked() {
                    self.vm.set_instr_limit(1);
                    self.vm.set_debug_hook(|_: &mut kibi::Vm| Ok(kibi::DebugHookResult::Pause));
                    self.vm.run().unwrap();
                    self.vm.set_instr_limit(0);
                    self.vm.clear_debug_hook();
                    changed = true;
                }
            });

            self.render_impl(gui);

            let mut props = Props::new().with_fill(0xffffffff).with_pointer_events();
            props.size[1] = Some(17.0);
            gui.widget_scrollbar_part(ScrollbarPart::X, props, |_|{});

            let mut props = Props::new().with_fill(0xff808080).with_pointer_events();
            props.size[0] = Some(2.0*17.0);
            gui.widget_scrollbar_part(ScrollbarPart::Y, props, |_|{});

            let props = Props::new().with_fill(0x80800000).with_pointer_events();
            gui.widget_scrollbar_part(ScrollbarPart::Corner, props, |_|{});
        });

        changed |= self.hl_instr_node.get() != prev_hl_instr_node;

        changed |= self.show_instrs_dirty.get();
        self.show_instrs_dirty.set(false);

        self.inserted_semicolons = new_semis;
        self.syntax_highlighting = new_syntax;
        self.font_size = new_font_size;
        if changed {
            self.update_decos();
            self.update_vlines();
            self.update_show_instrs();
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


impl CodeView {
    fn render_reg(&self, func: kibi::FunctionId, pc: u16, reg: u8, gui: &mut Gui) {
        let _ = (func, pc);

        let events = gui.widget_text(Key::Counter,
            Props {
                font_face: FaceId::DEFAULT,
                font_size: self.font_size_bc,
                text_color: TokenClass::Default.color(),
                pointer_events: true,
                ..Default::default()
            },
            format!("r{reg}"));

        if let Some((dx, dy)) = events.mouse_delta() { println!("{func}.{pc}.{reg} mouse moved by {dx} {dy}") }
        if events.mouse_went_down(MouseButton::Left) { println!("{func}.{pc}.{reg} left down") }
        if events.mouse_went_up(MouseButton::Left)   { println!("{func}.{pc}.{reg} left up") }
    }

    fn render_instr(&self, instr: &VisualInstr, gui: &mut Gui) {
        fn text(text: String, color: u32, view: &CodeView, gui: &mut Gui) {
            gui.widget_text(Key::Counter,
                Props {
                    font_face: FaceId::DEFAULT,
                    font_size: view.font_size_bc,
                    text_color: color,
                    ..Default::default()
                },
                text);
        }

        let name = instr.data.name();

        let mut instr_props = Props::new().with_pointer_events();
        instr_props.padding[0] = [self.font_size_bc/10.0; 2];

        let events = gui.widget_box(Key::Counter, instr_props, |gui| {
            gui.widget_text(Key::Counter,
                Props {
                    font_face: FaceId::DEFAULT,
                    font_size: self.font_size_bc,
                    text_color: TokenClass::Comment.color(),
                    ..Default::default()
                },
                format!("{:03} ", instr.data.pc));

            gui.widget_text(Key::Counter,
                Props {
                    font_face: FaceId::DEFAULT,
                    font_size: self.font_size_bc,
                    text_color: TokenClass::Default.color(),
                    ..Default::default()
                },
                format!("{:11} ", name));

            let func_id = instr.func;
            let pc      = instr.data.pc;

            use kibi::bytecode::InstrData::*;
            match &instr.data.data {
                Nop => (),
                Unreachable => (),

                LoadNil  { dst } |
                LoadEnv  { dst } |
                LoadUnit { dst } |
                MapNew   { dst } => {
                    self.render_reg(func_id, pc + 1, *dst, gui);
                }

                Swap { dst, src } => {
                    self.render_reg(func_id, pc, *dst, gui);
                    text(format!(", "), TokenClass::Default.color(), self, gui);
                    self.render_reg(func_id, pc, *src, gui);
                }

                Copy { dst, src } |
                Op1  { dst, src } => {
                    self.render_reg(func_id, pc + 1, *dst, gui);
                    text(format!(", "), TokenClass::Default.color(), self, gui);
                    self.render_reg(func_id, pc, *src, gui);
                }

                Op2 { dst, src1, src2 } => {
                    self.render_reg(func_id, pc + 1, *dst, gui);
                    text(format!(", "), TokenClass::Default.color(), self, gui);
                    self.render_reg(func_id, pc, *src1, gui);
                    text(format!(", "), TokenClass::Default.color(), self, gui);
                    self.render_reg(func_id, pc, *src2, gui);
                }


                LoadBool { dst, value } => {
                    self.render_reg(func_id, pc + 1, *dst, gui);
                    text(format!(", "), TokenClass::Default.color(), self, gui);
                    text(format!("{value}"), TokenClass::from_data(kibi::TokenData::Bool(false)).color(), self, gui);
                }

                LoadInt   { dst, value } |
                AddInt    { dst, value } => {
                    self.render_reg(func_id, pc + 1, *dst, gui);
                    text(format!(", "), TokenClass::Default.color(), self, gui);
                    text(format!("#{value}"), TokenClass::from_data(kibi::TokenData::Number("")).color(), self, gui);
                }

                LoadConst { dst, index } => {
                    self.render_reg(func_id, pc + 1, *dst, gui);
                    text(format!(", "), TokenClass::Default.color(), self, gui);
                    // @todo: render the const's value.
                    text(format!("c{index}"), TokenClass::Default.color(), self, gui);
                }

                ListNew  { dst, values } |
                TupleNew { dst, values } => {
                    let _ = (dst, values);
                    text(format!("..."), TokenClass::Comment.color(), self, gui);
                }


                ReadPath { dst, base, keys } => {
                    let _ = (dst, base, keys);
                    text(format!("..."), TokenClass::Comment.color(), self, gui);
                }

                WritePath { base, keys, value } => {
                    let _ = (base, keys, value);
                    text(format!("..."), TokenClass::Comment.color(), self, gui);
                }


                Jump { target } => {
                    text(format!("{target}"), TokenClass::Default.color(), self, gui);
                }

                JumpC1 { target, src } => {
                    self.render_reg(func_id, pc, *src, gui);
                    text(format!(", {target}"), TokenClass::Default.color(), self, gui);
                }

                Call { dst, func, args } => {
                    let _ = (dst, func, args);
                    text(format!("..."), TokenClass::Comment.color(), self, gui);
                }

                Ret { src } => {
                    self.render_reg(func_id, pc, *src, gui);
                }
            }
            text(format!("\n"), TokenClass::Default.color(), self, gui);
        });

        let instr_props = gui.edit_props_no_render(&events);
        if events.hovered {
            self.hl_instr_node.set(instr.node);
            instr_props.fill = true;
            instr_props.fill_color = 0xff414752;
        }
        if events.hover_changed() {
            gui.mark_for_render(&events);
        }
    }

    fn render_impl(&self, gui: &mut Gui) {
        let space_size    = gui.measure_string(" ", FaceId::DEFAULT, self.font_size);
        let space_size_bc = gui.measure_string(" ", FaceId::DEFAULT, self.font_size_bc);

        for line in &self.vlines {
            let mut line_props = Props::new();
            line_props.layout = Layout::Flex(FlexLayout::default());
            gui.widget_box(Key::Counter, line_props, |gui| {
                // buttons for "show_instrs".
                let mut show_instrs_props = Props::new();
                show_instrs_props.layout = Layout::Flex(FlexLayout { align: FlexAlign::Begin, ..Default::default()});
                show_instrs_props.size[0] = Some(space_size_bc[0] * 3.0);
                gui.widget_box(Key::Counter, show_instrs_props, |gui| {
                    if line.instrs_begin < line.instrs_end {
                        let show_instrs = line.show_instrs.get();

                        let mut props = Props::new().with_pointer_events().with_fill(0xff2A2E37);
                        props.padding = [[self.font_size_bc/16.0; 2]; 2];
                        if show_instrs == TriState::True { props.fill_color = 0xff4A5160 }
                        let events = gui.widget_box(Key::Counter, props, |gui| {
                            let mut props = Props::new();
                            props.text_color = TokenClass::Default.color();
                            props.font_size  = self.font_size_bc;
                            gui.widget_text(Key::Counter, Props::new(), "y".to_string());
                        });
                        if events.clicked() {
                            line.show_instrs.set(TriState::True);
                            self.show_instrs_dirty.set(true);
                        }

                        let mut props = Props::new().with_pointer_events().with_fill(0xff2A2E37);
                        props.padding = [[self.font_size_bc/16.0; 2]; 2];
                        if show_instrs == TriState::Default { props.fill_color = 0xff4A5160 }
                        let events = gui.widget_box(Key::Counter, props, |gui| {
                            let mut props = Props::new();
                            props.text_color = TokenClass::Default.color();
                            props.font_size  = self.font_size_bc;
                            gui.widget_text(Key::Counter, Props::new(), "-".to_string());
                        });
                        if events.clicked() {
                            line.show_instrs.set(TriState::Default);
                            self.show_instrs_dirty.set(true);
                        }

                        let mut props = Props::new().with_pointer_events().with_fill(0xff2A2E37);
                        props.padding = [[self.font_size_bc/16.0; 2]; 2];
                        if show_instrs == TriState::False { props.fill_color = 0xff4A5160 }
                        let events = gui.widget_box(Key::Counter, props, |gui| {
                            let mut props = Props::new();
                            props.text_color = TokenClass::Default.color();
                            props.font_size  = self.font_size_bc;
                            gui.widget_text(Key::Counter, Props::new(), "n".to_string());
                        });
                        if events.clicked() {
                            line.show_instrs.set(TriState::False);
                            self.show_instrs_dirty.set(true);
                        }
                    }
                });

                // line number.
                let mut number_props = Props::new();
                number_props.font_size  = self.font_size;
                number_props.text_color = TokenClass::Comment.color();
                gui.widget_text(Key::Counter, number_props,
                    format!("  {:3}  ", line.number));

                // spans & bytecode.
                gui.widget_box(Key::Counter, Props::new(), |gui| {
                    gui.widget_box(Key::Counter, Props::new().with_pointer_events(), |gui| {
                        for span in &line.spans {
                            let mut props = Props::new();
                            props.font_face  = span.face;
                            props.font_size  = self.font_size;
                            props.text_color = span.color;
                            if let Some(fill) = span.fill {
                                props.fill = true;
                                props.fill_color = fill;
                            }
                            gui.widget_text(Key::Counter, props, span.text.clone());
                        }
                    });

                    // bytecode instructions.
                    let mut bc_props = Props::new();
                    bc_props.fill = true;
                    bc_props.fill_color = 0xff2A2E37;

                    let instrs_begin = line.instrs_begin;
                    let instrs_end   = if line.instrs_visible { line.instrs_end } else { instrs_begin };

                    if instrs_begin < instrs_end {
                        bc_props.padding = [
                            [space_size[1]/4.0; 2],
                            [space_size[1]/8.0; 2],
                        ];

                        bc_props.margin = [
                            [ (line.indent + 1) as f32 * space_size[0], 0.0 ],
                            [space_size[1]/4.0; 2],
                        ];
                    }

                    gui.widget_box(Key::Counter, bc_props, |gui| {
                        for instr_index in instrs_begin..instrs_end {
                            if let Some(gap) = line.instrs_gap {
                                if gap == instr_index {
                                    let size = space_size[1]/4.0;
                                    let mut gap_props = Props::new();
                                    gap_props.size[1] = Some(size);
                                    gap_props.margin[1] = [(size/2.0 - 0.5).max(0.0); 2];
                                    gap_props.fill = true;
                                    gap_props.fill_color = 0xFF41454F;
                                    gui.widget_box(Key::Counter, gap_props, |_|{});
                                }
                            }

                            let instr = &self.instrs[instr_index as usize];
                            self.render_instr(instr, gui);
                        }
                    });
                });
            });
        }
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
                    canvas_props.overflow = [Overflow::Clip; 2];

                    let events = gui.widget_box(Key::Counter, canvas_props, |gui| {
                        let mut body_props = Props::new();
                        body_props.layout = Layout::None;
                        body_props.pos    = [Some(self.offset[0]), Some(self.offset[1])];

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
                        self.offset[0] = self.down_offset[0] + (pos[0] - pos_target[0]);
                        self.offset[1] = self.down_offset[1] + (pos[1] - pos_target[1]);
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

                r.clear(11, 14, 20);

                assert!(r.has_clip() == false);
                gui.draw(r);
                assert!(r.has_clip() == false);
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

