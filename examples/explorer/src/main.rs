use minifb::{Window, WindowOptions};
use kibi::index_vec::*;
use kibi::ast::*;


mod renderer;
use renderer::*;

mod gui;
use gui::{*, Key};


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

    #[allow(dead_code)] // @important: used by the `NodeRef`s in ast_info.
    ast: Box<kibi::ast::item::Module<'a>>,
    ast_info: AstInfo<'a>,

    funcs: IndexVec<kibi::FunctionId, kibi::FuncDesc>,
    items: IndexVec<ItemId, kibi::bbir::Item>,
    value_maps: IndexVec<kibi::FunctionId, Vec<Vec<kibi::codegen::ValueMapping>>>,
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
        let (funcs, items, value_maps) = builder.krate.build();

        return CodeInfo {
            tokens,
            ast,
            ast_info,
            funcs,
            items,
            value_maps,
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


#[derive(Clone, Copy, Debug)]
struct RegSpan {
    text_begin: u32,
    text_end:   u32,
    func: kibi::FunctionId,
    pc:   u16,
    reg:  u8,
}


struct CodeView {
    pos: (f32, f32),
    text: String,
    info: CodeInfo<'static>,
    layout: TextLayout,
    source_map:  SourceMap,
    bc_layout: TextLayout,
    reg_spans: Vec<RegSpan>,
}

impl CodeView {
    pub fn new(fonts: &FontCtx) -> CodeView {
        CodeView {
            pos:    (150., 50.),
            text:   "".into(),
            info:   CodeInfo::new(""),
            layout: TextLayout::new(fonts),
            source_map: SourceMap { line_begins: vec![], source_spans: vec![], text_spans: vec![] },
            bc_layout: TextLayout::new(fonts),
            reg_spans: vec![],
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
        self.source_map.line_begins.push(text.len() as u32);

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

        let font_size = 24.;

        // update text layout & mappings.
        self.layout.clear();
        self.source_map.source_spans.clear();
        self.source_map.text_spans.clear();
        self.bc_layout.clear();
        self.reg_spans.clear();

        let mut deco_cursor = 0;
        let mut line_index = 0;
        let mut line_begin = 0;
        let mut src_lines = 0;
        let mut bc_lines  = 0;
        let mut active_items = vec![]; // source_line_end, bc_line_end
        for line_end in self.source_map.line_begins[1..].iter() {
            let line_end = *line_end as usize;

            // new item starts?
            if let Some(item) = 
                self.info.ast_info.items.iter()
                .find(|item| item.source_range.begin.line == line_index + 1)
            {
                if let kibi::bbir::ItemData::Func(func_id) = self.info.items[item.item_id].data {
                    // sync source & bytecode.
                    for _ in src_lines..bc_lines {
                        self.layout.append("\n", FaceId::DEFAULT, font_size, 0, 0);
                    }
                    for _ in bc_lines..src_lines {
                        self.bc_layout.append("\n", FaceId::DEFAULT, font_size, 0, 0);
                    }
                    src_lines = src_lines.max(bc_lines);
                    bc_lines  = bc_lines.max(src_lines);

                    let func = &self.info.funcs[func_id];
                    bc_lines += Self::add_bytecode_fn(func_id, func, font_size, &mut self.bc_layout, &mut self.reg_spans);
                    active_items.push((item.source_range.end.line, bc_lines));
                }
            }

            let mut text_cursor = line_begin;
            while text_cursor < line_end {
                let next_deco =
                    decos.get(deco_cursor)
                    .filter(|deco| deco.text_begin as usize <= line_end);

                if let Some(next_deco) = next_deco {
                    let deco_begin = (next_deco.text_begin as usize).max(line_begin);
                    let deco_end   = (next_deco.text_end   as usize).min(line_end);
                    debug_assert!(deco_begin <= deco_end);

                    if text_cursor < deco_begin {
                        let source_begin = text_cursor as u32;
                        let source_end   = deco_begin  as u32;

                        let text_begin = self.layout.text().len() as u32;
                        self.layout.append(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
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
                            self.layout.append(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, *color, 0);
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
                            self.layout.append(text, FaceId::DEFAULT, font_size, *color, 0);
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

                    if next_deco.text_end as usize <= line_end {
                        deco_cursor += 1;
                    }
                    text_cursor = deco_end;
                }
                else {
                    let source_begin = text_cursor as u32;
                    let source_end   = line_end    as u32;

                    let text_begin = self.layout.text().len() as u32;
                    self.layout.append(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
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

                    text_cursor = line_end;
                }
            }

            line_index += 1;
            line_begin = line_end;
            src_lines += 1;

            // old item expired? -> pad source.
            while let Some((source_line_end, bc_line_end)) = active_items.last().copied() {
                if source_line_end <= line_index {
                    for _ in src_lines..bc_line_end {
                        self.layout.append("\n", FaceId::DEFAULT, font_size, 0, 0);
                    }
                    src_lines = src_lines.max(bc_line_end);
                    active_items.pop();
                }
                else { break }
            }
        }
    }

    fn add_bytecode_fn(func_id: kibi::FunctionId, func: &kibi::FuncDesc, font_size: f32, bc_layout: &mut TextLayout, reg_spans: &mut Vec<RegSpan>) -> u32 {
        fn add_reg(func: kibi::FunctionId, pc: u16, reg: u8, font_size: f32, bc_layout: &mut TextLayout, reg_spans: &mut Vec<RegSpan>) {
            let text_begin = bc_layout.text().len() as u32;
            bc_layout.append(&format!("r{reg}"), FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
            let text_end = bc_layout.text().len() as u32;

            reg_spans.push(RegSpan { text_begin, text_end, func, pc, reg });
        }

        let kibi::FuncCode::ByteCode(code) = &func.code else { unreachable!() };
        let code = kibi::bytecode::ByteCodeDecoder::decode(code).unwrap();
        for instr in &code {
            let name = instr.name();
            bc_layout.append(&format!("{:03} ", instr.pc), FaceId::DEFAULT, font_size, TokenClass::Comment.color(), 0);
            bc_layout.append(&format!("{:11} ", name), FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);

            use kibi::bytecode::InstrData::*;
            match &instr.data {
                Nop => (),
                Unreachable => (),

                LoadNil  { dst } |
                LoadEnv  { dst } |
                LoadUnit { dst } |
                MapNew   { dst } => {
                    add_reg(func_id, instr.pc + 1, *dst, font_size, bc_layout, reg_spans);
                }

                Swap { dst, src } => {
                    add_reg(func_id, instr.pc, *dst, font_size, bc_layout, reg_spans);
                    bc_layout.append(", ", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                    add_reg(func_id, instr.pc, *src, font_size, bc_layout, reg_spans);
                }

                Copy { dst, src } |
                Op1  { dst, src } => {
                    add_reg(func_id, instr.pc + 1, *dst, font_size, bc_layout, reg_spans);
                    bc_layout.append(", ", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                    add_reg(func_id, instr.pc, *src, font_size, bc_layout, reg_spans);
                }

                Op2 { dst, src1, src2 } => {
                    add_reg(func_id, instr.pc + 1, *dst, font_size, bc_layout, reg_spans);
                    bc_layout.append(", ", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                    add_reg(func_id, instr.pc, *src1, font_size, bc_layout, reg_spans);
                    bc_layout.append(", ", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                    add_reg(func_id, instr.pc, *src2, font_size, bc_layout, reg_spans);
                }


                LoadBool { dst, value } => {
                    add_reg(func_id, instr.pc + 1, *dst, font_size, bc_layout, reg_spans);
                    bc_layout.append(", ", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                    bc_layout.append(&format!("{value}"), FaceId::DEFAULT, font_size, TokenClass::from_data(kibi::TokenData::Bool(false)).color(), 0);
                }

                LoadInt   { dst, value } |
                AddInt    { dst, value } => {
                    add_reg(func_id, instr.pc + 1, *dst, font_size, bc_layout, reg_spans);
                    bc_layout.append(", ", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                    bc_layout.append(&format!("#{value}"), FaceId::DEFAULT, font_size, TokenClass::from_data(kibi::TokenData::Number("")).color(), 0);
                }

                LoadConst { dst, index } => {
                    add_reg(func_id, instr.pc + 1, *dst, font_size, bc_layout, reg_spans);
                    bc_layout.append(", ", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                    // @todo: render the const's value.
                    bc_layout.append(&format!("c{index}"), FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                }

                ListNew  { dst, values } |
                TupleNew { dst, values } => {
                    let _ = (dst, values);
                    bc_layout.append(&format!("..."), FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                }


                ReadPath { dst, base, keys } => {
                    let _ = (dst, base, keys);
                    bc_layout.append(&format!("..."), FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                }

                WritePath { base, keys, value } => {
                    let _ = (base, keys, value);
                    bc_layout.append(&format!("..."), FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                }


                Jump { target } => {
                    bc_layout.append(&format!("{target}"), FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                }

                JumpC1 { target, src } => {
                    add_reg(func_id, instr.pc, *src, font_size, bc_layout, reg_spans);
                    bc_layout.append(", ", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                    bc_layout.append(&format!("{target}"), FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                }

                Call { dst, func, args } => {
                    let _ = (dst, func, args);
                    bc_layout.append(&format!("..."), FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
                }

                Ret { src } => {
                    add_reg(func_id, instr.pc, *src, font_size, bc_layout, reg_spans);
                }
            }
            bc_layout.append("\n", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
        }
        bc_layout.append("\n", FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);

        code.len() as u32 + 1
    }

    pub fn update(&mut self, window: &Window, offset: (f32, f32), r: &mut Renderer) {
        let (mx, my) = window.get_mouse_pos(minifb::MouseMode::Pass).unwrap();

        let src_x0 = self.pos.0 - offset.0;
        let src_y0 = self.pos.1 - offset.1;
        let src_x0i = src_x0.floor() as i32;
        let src_y0i = src_y0.floor() as i32;

        let bc_x0 = self.pos.0 + self.layout.width().ceil() - offset.0;
        let bc_y0 = self.pos.1 - offset.1;
        let bc_x0i = bc_x0.floor() as i32;
        let bc_y0i = bc_y0.floor() as i32;

        let mut src_hover     = vec![];
        let mut src_highlight = vec![];
        let mut bc_hover      = vec![];
        //let mut bc_highlight  = vec![];

        'hit_test_src: {
            let mhit = self.layout.hit_test_pos(mx - src_x0, my - src_y0);
            if mhit.out_of_bounds[0] || mhit.out_of_bounds[1] { break 'hit_test_src }

            let Some(source_pos) = self.source_map.text_to_source(mhit.text_pos_left) else { break 'hit_test_src };

            for info in self.info.ast_info.nodes.iter().rev() {
                let begin = self.source_map.source_pos_to_offset(info.source_range.begin);
                let end   = self.source_map.source_pos_to_offset(info.source_range.end);

                if source_pos < begin || source_pos >= end { continue }

                let Some(text_first) = self.source_map.source_to_text(begin)   else { continue };
                let Some(text_last)  = self.source_map.source_to_text(end - 1) else { continue };

                src_hover.push((text_first, text_last));

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
                                    src_highlight.push((text_first, text_last));
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
                                    src_highlight.push((text_first, text_last));
                                }
                            }

                            expr::IdentTarget::Dynamic => {
                                src_highlight.push((text_first, text_last));
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
                                src_highlight.push((text_first, text_last));
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
                                src_highlight.push((text_first, text_last));
                            }
                        }
                    }
                }

                break;
            }
        }

        'hit_test_bc: {
            let mhit = self.bc_layout.hit_test_pos(mx - bc_x0, my - bc_y0);
            if mhit.out_of_bounds[0] || mhit.out_of_bounds[1] { break 'hit_test_bc }

            let text_pos = mhit.text_pos_left;

            for span in &self.reg_spans {
                if text_pos < span.text_begin || text_pos >= span.text_end {
                    continue;
                }

                bc_hover.push((span.text_begin, span.text_end - 1));

                let value_mapping = &self.info.value_maps[span.func];
                for range in &value_mapping[span.reg as usize] {
                    let pc = span.pc as u32;
                    if pc <= range.pc_begin || pc > range.pc_end {
                        continue;
                    }

                    for node_id in range.values.iter().copied() {
                        let node_info = &self.info.ast_info.nodes[node_id];
                        let begin = self.source_map.source_pos_to_offset(node_info.source_range.begin);
                        let end   = self.source_map.source_pos_to_offset(node_info.source_range.end);
                        if let (Some(text_first), Some(text_last)) = (
                            self.source_map.source_to_text(begin),
                            self.source_map.source_to_text(end - 1))
                        {
                            src_highlight.push((text_first, text_last));
                        }
                    }
                }
            }
        }


        r.fill_rect_abs_opaque(
            src_x0i, src_y0i,
            (src_x0 + self.layout.width()  + 0.5) as i32,
            (src_y0 + self.layout.height() + 0.5) as i32,
            color_pack((30, 35, 40, 255)));

        for (first, last) in src_hover.iter().copied() {
            self.layout.hit_test_text_ranges(first, last + 1, |range| {
                let x0 = (src_x0 + range.x0) as i32;
                let x1 = (src_x0 + range.x1) as i32;
                let y0 = (src_y0 + range.y)  as i32;
                let y1 = (src_y0 + range.y + range.line_height) as i32;
                r.fill_rect_abs_opaque(x0, y0, x1, y1, color_pack((50, 55, 60, 255)));
            });
        }

        for (first, last) in src_highlight.iter().copied() {
            self.layout.hit_test_text_ranges(first, last + 1, |range| {
                let x0 = (src_x0 + range.x0) as i32;
                let x1 = (src_x0 + range.x1) as i32;
                let y0 = (src_y0 + range.y)  as i32;
                let y1 = (src_y0 + range.y + range.line_height) as i32;
                r.fill_rect_abs_opaque(x0, y0, x1, y1, color_pack((64, 73, 91, 255)));
            });
        }

        r.draw_text_layout_abs(src_x0i, src_y0i, &self.layout);


        for (first, last) in bc_hover.iter().copied() {
            self.bc_layout.hit_test_text_ranges(first, last + 1, |range| {
                let x0 = (bc_x0 + range.x0) as i32;
                let x1 = (bc_x0 + range.x1) as i32;
                let y0 = (bc_y0 + range.y)  as i32;
                let y1 = (bc_y0 + range.y + range.line_height) as i32;
                r.fill_rect_abs_opaque(x0, y0, x1, y1, color_pack((50, 55, 60, 255)));
            });
        }

        /*
        for (first, last) in bc_highlight.iter().copied() {
            self.layout.hit_test_text_ranges(first, last + 1, |range| {
                let x0 = (bc_x0 + range.x0) as i32;
                let x1 = (bc_x0 + range.x1) as i32;
                let y0 = (bc_y0 + range.y)  as i32;
                let y1 = (bc_y0 + range.y + range.line_height) as i32;
                r.fill_rect_abs_opaque(x0, y0, x1, y1, color_pack((64, 73, 91, 255)));
            });
        }
        */

        r.draw_text_layout_abs(bc_x0i, bc_y0i, &self.bc_layout);
    }
}



struct NewCodeView {
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

impl NewCodeView {
    pub fn new() -> NewCodeView {
        NewCodeView {
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

        fn quote_button_endquote(gui: &mut Gui, title: String) -> WidgetEvents {
            gui.widget_box(Key::Counter, Props::new().with_pointer_events(), |gui| {
                gui.widget_text(Key::Counter, Props::new(), title);
            })
        }

        if quote_button_endquote(gui, format!("inserted semicolons: {}", self.inserted_semicolons)).clicked() {
            new_semis = !self.inserted_semicolons;
            changed = true;
        }

        if quote_button_endquote(gui, format!("syntax highlighting: {}", self.syntax_highlighting)).clicked() {
            new_syntax = !self.syntax_highlighting;
            changed = true;
        }

        let mut deco_cursor = 0;
        let mut line_begin = 0;
        for line_end in self.lines[1..].iter() {
            let line_end = *line_end as usize;

            let mut line_props = Props::new();
            line_props.layout = Layout::Flex(FlexLayout::default());

            // we'll need a recursive function for nested items now.
            // so have like a `Renderer` or something for the line state.

            gui.widget_box(Key::U64(line_begin as u64), line_props, |gui|{
                let mut text_cursor = line_begin;
                while text_cursor < line_end {
                    let next_deco =
                        self.decos.get(deco_cursor)
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
                                    font_size: self.font_size, 
                                    text_color: TokenClass::Default.color(), 
                                    ..Default::default()
                                },
                                self.text[source_begin as usize .. source_end as usize].to_string());
                        }

                        match &next_deco.data {
                            DecorationData::Style { color } => {
                                let source_begin = deco_begin as u32;
                                let source_end   = deco_end   as u32;
                                gui.widget_text(Key::Counter,
                                    Props { 
                                        font_face: FaceId::DEFAULT, 
                                        font_size: self.font_size, 
                                        text_color: *color,
                                        ..Default::default()
                                    },
                                    self.text[source_begin as usize .. source_end as usize].to_string());
                            }

                            DecorationData::Replace { text, color } => {
                                gui.widget_text(Key::Counter,
                                    Props { 
                                        font_face: FaceId::DEFAULT, 
                                        font_size: self.font_size, 
                                        text_color: *color,
                                        ..Default::default()
                                    },
                                    text.to_string());
                            }
                        }

                        if next_deco.text_end as usize <= line_end {
                            deco_cursor += 1;
                        }
                        text_cursor = deco_end;
                    }
                    else {
                        let source_begin = text_cursor as u32;
                        let source_end   = line_end    as u32;
                        gui.widget_text(Key::Counter,
                            Props { 
                                font_face: FaceId::DEFAULT, 
                                font_size: self.font_size, 
                                text_color: TokenClass::Default.color(),
                                ..Default::default()
                            },
                            self.text[source_begin as usize .. source_end as usize].to_string());

                        text_cursor = line_end;
                    }
                }
            });

            line_begin = line_end;

            /*
            // new item starts?
            if let Some(item) = 
                self.info.ast_info.items.iter()
                .find(|item| item.source_range.begin.line == line_index + 1)
            {
                if let kibi::bbir::ItemData::Func(func_id) = self.info.items[item.item_id].data {
                    // sync source & bytecode.
                    for _ in src_lines..bc_lines {
                        self.layout.append("\n", FaceId::DEFAULT, font_size, 0, 0);
                    }
                    for _ in bc_lines..src_lines {
                        self.bc_layout.append("\n", FaceId::DEFAULT, font_size, 0, 0);
                    }
                    src_lines = src_lines.max(bc_lines);
                    bc_lines  = bc_lines.max(src_lines);

                    let func = &self.info.funcs[func_id];
                    bc_lines += Self::add_bytecode_fn(func_id, func, font_size, &mut self.bc_layout, &mut self.reg_spans);
                    active_items.push((item.source_range.end.line, bc_lines));
                }
            }
            */

            /*
            let mut text_cursor = line_begin;
            while text_cursor < line_end {
                let next_deco =
                    decos.get(deco_cursor)
                    .filter(|deco| deco.text_begin as usize <= line_end);

                if let Some(next_deco) = next_deco {
                    let deco_begin = (next_deco.text_begin as usize).max(line_begin);
                    let deco_end   = (next_deco.text_end   as usize).min(line_end);
                    debug_assert!(deco_begin <= deco_end);

                    if text_cursor < deco_begin {
                        let source_begin = text_cursor as u32;
                        let source_end   = deco_begin  as u32;

                        let text_begin = self.layout.text().len() as u32;
                        self.layout.append(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
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
                            self.layout.append(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, *color, 0);
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
                            self.layout.append(text, FaceId::DEFAULT, font_size, *color, 0);
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

                    if next_deco.text_end as usize <= line_end {
                        deco_cursor += 1;
                    }
                    text_cursor = deco_end;
                }
                else {
                    let source_begin = text_cursor as u32;
                    let source_end   = line_end    as u32;

                    let text_begin = self.layout.text().len() as u32;
                    self.layout.append(&text[source_begin as usize .. source_end as usize], FaceId::DEFAULT, font_size, TokenClass::Default.color(), 0);
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

                    text_cursor = line_end;
                }
            }

            line_index += 1;
            line_begin = line_end;
            src_lines += 1;

            // old item expired? -> pad source.
            while let Some((source_line_end, bc_line_end)) = active_items.last().copied() {
                if source_line_end <= line_index {
                    for _ in src_lines..bc_line_end {
                        self.layout.append("\n", FaceId::DEFAULT, font_size, 0, 0);
                    }
                    src_lines = src_lines.max(bc_line_end);
                    active_items.pop();
                }
                else { break }
            }
            */
        }

        self.inserted_semicolons = new_semis;
        self.syntax_highlighting = new_syntax;
        if changed {
            self.update_decos();
        }

        changed
    }
}


struct Explorer {
    window:   Window,
    renderer: Renderer,
    offset:     (f32, f32),
    last_mouse: (f32, f32),
    code:     CodeView,
    gui: Gui,
    new_code: NewCodeView,
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
            gui: Gui::new(&fonts),
            new_code: NewCodeView::new(),
        }
    }

    pub fn run(&mut self) {
        let mut never_updated = true;

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

            let mdown = self.window.get_mouse_down(minifb::MouseButton::Left);


            let gui = &mut self.gui;

            let mut changed = never_updated;
            for _ in 0..10 {
                if !gui.mouse_move(mx, my)
                && !gui.mouse_down(mdown)
                && !changed {
                    break;
                }

                let root_size = [size.0 as f32, size.1 as f32];
                let root_props = Props::new();

                changed = gui.update(root_size, root_props, |gui| {
                    self.new_code.render(gui)
                });

                never_updated = false;
            }


            let r = &mut self.renderer;
            r.set_size(size.0 as u32, size.1 as u32);

            r.clear(13, 16, 23);

            self.code.update(&self.window, self.offset, r);

            gui.draw(r);

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
        e.new_code.set_text(&source);
    }
    else {
        let source = include_str!("../../fib.kb");
        e.code.set_text(source);
        e.new_code.set_text(source);
    }

    e.run();
}

