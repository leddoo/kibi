use crate::bytecode::*;
use crate::value::*;
use crate::vm::Vm;
use crate::parser::Ast;


struct FuncBuilder<'a> {
    b: ByteCodeBuilder,
    num_params: u32,
    next_reg: u8,

    constants: Vec<Value>,

    locals: Vec<LocalDecl<'a>>,
    scope: u32,
}

struct LocalDecl<'a> {
    scope: u32,
    name: &'a str,
    reg: u8,
}

impl<'a> FuncBuilder<'a> {
    fn new(params: &[&'a str], is_chunk: bool) -> FuncBuilder<'a> {
        if is_chunk {
            assert_eq!(params.len(), 0);
        }

        let mut next_reg = 0;
        assert!(params.len() < 128);

        let mut locals = vec![];
        for name in params {
            let reg = next_reg;
            next_reg += 1;
            locals.push(LocalDecl { scope: 1, name, reg })
        }

        let scope = if is_chunk { 0 } else { 1 };

        FuncBuilder {
            b: ByteCodeBuilder::new(),
            num_params: params.len() as u32,
            next_reg,
            constants: vec![],
            locals,
            scope,
        }
    }

    fn push_scope(&mut self) {
        self.scope += 1;
    }

    fn pop_scope(&mut self) {
        let scope = self.scope;
        self.locals.retain(|l| l.scope < scope);
        self.scope -= 1;
    }

    fn def_global(&mut self, name: &'a str, value: Option<u8>, vm: &mut Vm) -> Result<(), ()> {
        let name = vm.string_new(name);
        let name = self.add_constant(name)?;

        let env = self.next_reg()?;
        let key = self.next_reg()?;
        self.b.load_env(env);
        self.b.load_const(key, name);
        if let Some(value) = value {
            self.b.def(env, key, value);
        }
        else {
            let nil = self.next_reg()?;
            self.b.load_nil(nil);
            self.b.def(env, key, nil);
        }
        Ok(())
    }

    fn def_local(&mut self, name: &'a str, reg: u8) {
        self.locals.push(LocalDecl { scope: self.scope, name, reg });
    }

    fn lookup_var(&self, name: &str) -> Option<u8> {
        for local in self.locals.iter().rev() {
            if local.name == name {
                return Some(local.reg);
            }
        }
        None
    }

    fn next_reg(&mut self) -> Result<u8, ()> {
        if self.next_reg < u8::MAX {
            let result = self.next_reg;
            self.next_reg += 1;
            return Ok(result);
        }
        Err(())
    }

    fn reg_or_next_reg(&mut self, reg: Option<u8>) -> Result<u8, ()> {
        if let Some(reg) = reg {
            return Ok(reg);
        }
        return self.next_reg();
    }

    fn add_constant(&mut self, value: Value) -> Result<u16, ()> {
        let result = self.constants.len();
        if result < u16::MAX as usize {
            self.constants.push(value);
            return Ok(result as u16);
        }
        Err(())
    }

    fn build(mut self) -> FuncProto {
        let top = self.next_reg as u32;

        self.b.ret(0, 0);

        FuncProto {
            code: FuncCode::ByteCode(self.b.build()),
            constants: self.constants,
            num_params: self.num_params,
            stack_size: top,
        }
    }
}

// on `dst`:
//  - optional to avoid needless copies (eg of locals).
//  - if the caller only needs read access, they can pass `None`.
//    this lets the callee choose the register.
//  - if the caller may write to the resulting register,
//    or request another value in the same register,
//    they must allocate a register and pass it as `Some`.
//  - if `dst` is `Some`, the callee must ensure the value ends up in that register,
//    and return `dst` from this function.
//  - when passing `num_rets = 0`, `dst` must be `None`.
//  - eventually, this convention should be replaced by some more formal
//    register allocation scheme.
fn compile<'a>(f: &mut FuncBuilder<'a>, ast: &Ast<'a>, vm: &mut Vm, dst: Option<u8>, num_rets: u8) -> Result<u8, ()> {
    match ast {
        Ast::Number(value) => {
            let dst = f.reg_or_next_reg(dst)?;

            let value = *value;
            if value as i16 as f64 == value {
                f.b.load_int(dst, value as i16);
            }
            else {
                let c = f.add_constant(Value::Number { value })?;
                f.b.load_const(dst, c);
            }

            Ok(dst)
        }
        Ast::String (value) => {
            let dst = f.reg_or_next_reg(dst)?;

            let s = vm.string_new(*value);
            let c = f.add_constant(s)?;
            f.b.load_const(dst, c);

            Ok(dst)
        }
        Ast::Atom (value) => {
            let name = *value;

            if let Some(var) = f.lookup_var(name) {
                if let Some(dst) = dst {
                    f.b.copy(dst, var);
                    Ok(dst)
                }
                else {
                    Ok(var)
                }
            }
            else {
                let dst = f.reg_or_next_reg(dst)?;

                let name = vm.string_new(name);
                let name = f.add_constant(name)?;

                let env = f.next_reg()?;
                let key = f.next_reg()?;
                f.b.load_env(env);
                f.b.load_const(key, name);
                f.b.get(dst, env, key);

                Ok(dst)
            }
        }
        Ast::List (values) => {
            let func = values.get(0).ok_or(())?;
            let args = &values[1..];

            // try special forms.
            if let Ast::Atom(op) = func {
                let op = *op;

                if op == "var" {
                    if num_rets > 0 { return Err(()) }
                    if args.len() == 0 { return Err(()) }
                    if args.len() > 2 { return Err(()) }

                    let Ast::Atom(name) = args[0] else { return Err(()) };

                    if f.scope == 0 {
                        if args.len() == 1 {
                            f.def_global(name, None, vm)?;
                        }
                        else {
                            let value = compile(f, &args[1], vm, None, 1)?;
                            f.def_global(name, Some(value), vm)?;
                        }
                    }
                    else {
                        let reg = f.next_reg()?;
                        compile(f, &args[1], vm, Some(reg), 1)?;
                        f.def_local(name, reg);
                    }

                    return Ok(0); // num_rets = 0
                }

                if op == "def" {
                    if num_rets > 0 { return Err(()) }
                    if args.len() != 3 { return Err(()) }

                    let obj = compile(f, &args[0], vm, None, 1)?;
                    let key = compile(f, &args[1], vm, None, 1)?;
                    let val = compile(f, &args[2], vm, None, 1)?;

                    f.b.def(obj, key, val);

                    return Ok(0); // num_rets = 0
                }

                if op == "set" {
                    if num_rets > 0 { return Err(()) }

                    if args.len() == 2 {
                        let Ast::Atom(name) = args[0] else { return Err(()) };

                        if let Some(var) = f.lookup_var(name) {
                            compile(f, &args[1], vm, Some(var), 1)?;
                        }
                        else {
                            let value = compile(f, &args[1], vm, None, 1)?;

                            let name = vm.string_new(name);
                            let name = f.add_constant(name)?;

                            let env = f.next_reg()?;
                            let key = f.next_reg()?;
                            f.b.load_env(env);
                            f.b.load_const(key, name);
                            f.b.set(env, key, value);
                        }

                        return Ok(0); // num_rets = 0
                    }

                    if args.len() == 3 {
                        let obj = compile(f, &args[0], vm, None, 1)?;
                        let key = compile(f, &args[1], vm, None, 1)?;
                        let val = compile(f, &args[2], vm, None, 1)?;

                        f.b.set(obj, key, val);

                        return Ok(0); // num_rets = 0
                    }

                    return Err(());
                }

                if op == "get" {
                    if num_rets != 1 { return Err(()) }
                    if args.len() != 2 { return Err(()) }

                    let obj = compile(f, &args[0], vm, None, 1)?;
                    let key = compile(f, &args[1], vm, None, 1)?;

                    let dst = f.reg_or_next_reg(dst)?;
                    f.b.get(dst, obj, key);

                    return Ok(dst);
                }

                if op == "do" {
                    // TEMP
                    // TODO: pass dst & num_rets to the last stmt.
                    if num_rets > 0 { return Err(()) };

                    f.push_scope();
                    for stmt in args {
                        compile(f, stmt, vm, None, 0)?;
                    }
                    f.pop_scope();

                    return Ok(0); // num_rets = 0
                }

                if op == "if" {
                    if args.len() < 2 || args.len() > 3 { return Err(()) }

                    let dst = f.reg_or_next_reg(dst)?;

                    let cond = &args[0];
                    let then = &args[1];

                    f.b.begin_block(); {
                        f.b.begin_block(); {
                            let c = compile(f, cond, vm, None, 1)?;

                            f.b.exit_false(c, 0);

                            compile(f, then, vm, Some(dst), num_rets)?;
                            f.b.exit_block(1);
                        } f.b.end_block();

                        if args.len() == 3 {
                            let els = &args[2];
                            compile(f, els, vm, Some(dst), num_rets)?;
                        }
                    } f.b.end_block();

                    return Ok(dst);
                }

                if op == "while" {
                    if num_rets > 0 { return Err(()) };
                    if args.len() != 2 { return Err(()) }

                    let cond = &args[0];
                    let body = &args[1];

                    f.b.begin_block(); {
                        let c = compile(f, cond, vm, None, 1)?;

                        f.b.exit_false(c, 0);

                        compile(f, body, vm, None, 0)?;

                        f.b.repeat_block(0);
                    }f.b.end_block();

                    return Ok(0); // num_rets = 0
                }

                if op == "fn" {
                    if num_rets != 1 { return Err(()) }
                    if args.len() != 2 { return Err(()) }

                    let proto = compile_function(&args[0], &args[1], vm)?;
                    let func = vm.func_new(proto);

                    let dst = f.reg_or_next_reg(dst)?;

                    let constant = f.add_constant(func)?;
                    f.b.load_const(dst, constant);

                    return Ok(dst);
                }

                if op == "return" {
                    if num_rets > 0 { return Err(()) }
                    if args.len() > 255 { return Err(()) }

                    if args.len() > 0 {
                        let mut regs = vec![];
                        for _ in args {
                            regs.push(f.next_reg()?);
                        }

                        for (i, arg) in args.iter().enumerate() {
                            compile(f, arg, vm, Some(regs[i]), 1)?;
                        }

                        f.b.ret(regs[0], regs.len() as u8);
                    }
                    else {
                        f.b.ret(0, 0);
                    }

                    return Ok(0); // num_rets = 0
                }
            }

            let dst = f.reg_or_next_reg(dst)?;

            let mut arg_regs = vec![];
            for arg in args {
                let r = compile(f, arg, vm, None, 1)?;
                arg_regs.push(r);
            }

            // try operators.
            if let Ast::Atom(op) = func {
                let op = *op;

                if op == "+" {
                    if num_rets != 1 { return Err(()) }
                    if arg_regs.len() != 2 { return Err(()) }
                    f.b.add(dst, arg_regs[0], arg_regs[1]);
                    return Ok(dst);
                }

                if op == "-" {
                    if num_rets != 1 { return Err(()) }
                    if arg_regs.len() != 2 { return Err(()) }
                    f.b.sub(dst, arg_regs[0], arg_regs[1]);
                    return Ok(dst);
                }

                if op == "*" {
                    if num_rets != 1 { return Err(()) }
                    if arg_regs.len() != 2 { return Err(()) }
                    f.b.mul(dst, arg_regs[0], arg_regs[1]);
                    return Ok(dst);
                }

                if op == "/" {
                    if num_rets != 1 { return Err(()) }
                    if arg_regs.len() != 2 { return Err(()) }
                    f.b.div(dst, arg_regs[0], arg_regs[1]);
                    return Ok(dst);
                }

                if op == "==" {
                    if num_rets != 1 { return Err(()) }
                    if arg_regs.len() != 2 { return Err(()) }
                    f.b.cmp_eq(dst, arg_regs[0], arg_regs[1]);
                    return Ok(dst);
                }

                if op == "<=" {
                    if num_rets != 1 { return Err(()) }
                    if arg_regs.len() != 2 { return Err(()) }
                    f.b.cmp_le(dst, arg_regs[0], arg_regs[1]);
                    return Ok(dst);
                }

                if op == "<" {
                    if num_rets != 1 { return Err(()) }
                    if arg_regs.len() != 2 { return Err(()) }
                    f.b.cmp_lt(dst, arg_regs[0], arg_regs[1]);
                    return Ok(dst);
                }

                if op == ">=" {
                    if num_rets != 1 { return Err(()) }
                    if arg_regs.len() != 2 { return Err(()) }
                    f.b.cmp_ge(dst, arg_regs[0], arg_regs[1]);
                    return Ok(dst);
                }

                if op == ">" {
                    if num_rets != 1 { return Err(()) }
                    if arg_regs.len() != 2 { return Err(()) }
                    f.b.cmp_gt(dst, arg_regs[0], arg_regs[1]);
                    return Ok(dst);
                }
            }

            // @todo-#code_size: detect packed call? (don't think they're common)
            // function call.
            let func_reg = compile(f, func, vm, None, 1)?;
            f.b.gather_call(func_reg, &arg_regs, dst, num_rets);

            Ok(dst)
        }
        Ast::Array (values) => {
            if num_rets == 0 { return Err(()) }

            let dst = f.reg_or_next_reg(dst)?;

            f.b.list_new(dst);

            for value in values {
                let reg = compile(f, value, vm, None, 1)?;
                f.b.list_append(dst, reg);
            }

            Ok(dst)
        }
        Ast::Table (values) => {
            if num_rets == 0 { return Err(()) }

            let dst = f.reg_or_next_reg(dst)?;

            f.b.table_new(dst);

            for (key, value) in values {
                let k = compile(f, key,   vm, None, 1)?;
                let v = compile(f, value, vm, None, 1)?;
                f.b.def(dst, k, v);
            }

            Ok(dst)
        }
    }
}


pub fn compile_function(params: &Ast, body: &Ast, vm: &mut Vm) -> Result<usize, ()> {
    let Ast::List(params) = params else { return Err(()) };

    let mut param_names = vec![];
    for param in params {
        let Ast::Atom(name) = param else { return Err(()) };
        param_names.push(*name);
    }

    let mut f = FuncBuilder::new(&param_names, false);
    compile(&mut f, body, vm, None, 0)?;

    let proto = f.build();

    let proto_index = vm.func_protos.len();
    vm.func_protos.push(proto);

    Ok(proto_index)
}

pub fn compile_chunk(ast: &[Ast], vm: &mut Vm) -> Result<(), ()> {
    let mut f = FuncBuilder::new(&[], true);
    for node in ast {
        compile(&mut f, node, vm, None, 0)?;
    }

    let proto = f.build();

    let proto_index = vm.func_protos.len();
    vm.func_protos.push(proto);

    vm.push_func(proto_index);
    Ok(())
}


