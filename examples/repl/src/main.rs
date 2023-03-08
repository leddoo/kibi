use kibi::*;


mod builtin {
    use super::*;

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


fn main() {
    let mut vm = Vm::new();

    vm.add_func("print", builtin::PRINT);
    vm.add_func("println", builtin::PRINTLN);
    vm.add_func("quit", FuncDesc {
        code: FuncCode::Native(NativeFuncPtrEx(|_| std::process::exit(0))),
        constants: vec![],
        num_params: 0,
        stack_size: 0,
    });

    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 {
        assert_eq!(args.len(), 2);

        let path = &args[1];
        let source = std::fs::read_to_string(path).unwrap();

        let t0 = std::time::Instant::now();
        let mut module = parser::parse_module(source.as_bytes()).unwrap();
        let dt_parse = t0.elapsed();

        let t0 = std::time::Instant::now();
        let mut infer = infer::Infer::new();
        infer.assign_ids_module(&mut module);
        infer.infer_module(&mut module);
        let dt_infer = t0.elapsed();

        let t0 = std::time::Instant::now();
        let builder = bbir_builder::Builder::new();
        builder.build_module(&module);
        builder.module.temp_load(&mut vm);
        let dt_compile = t0.elapsed();

        let t0 = std::time::Instant::now();
        vm.temp_call().unwrap();
        let dt_run = t0.elapsed();

        println!("parse:   {:?}", dt_parse);
        println!("infer:   {:?}", dt_infer);
        println!("compile: {:?}", dt_compile);
        println!("run:     {:?}", dt_run);

        return;
    }


    let running = &*Box::leak(Box::new(core::sync::atomic::AtomicBool::new(false)));

    let interrupt_ptr = vm.interrupt_ptr() as usize;
    ctrlc::set_handler(move || {
        if running.load(core::sync::atomic::Ordering::SeqCst) {
            let ptr = interrupt_ptr as *mut bool;
            unsafe { ptr.write_volatile(true) };
        }
        else {
            std::process::exit(0);
        }
    }).unwrap();


    let mut buffer = String::new();

    loop {
        if buffer.len() > 0 {
            print!("    ");
        }
        else {
            print!(">>> ");
        }
        use std::io::Write;
        std::io::stdout().lock().flush().unwrap();
        std::io::stdin().read_line(&mut buffer).unwrap();

        let t0 = std::time::Instant::now();
        let ic = vm.instruction_counter();

        let ast = {
            let chunk = buffer.trim();
            if chunk.len() == 0 {
                buffer.clear();
                continue;
            }

            match parser::parse_single(chunk.as_bytes()) {
                Ok(ast) => ast,
                Err(e) => {
                    match e.data {
                        compiler::ParseErrorData::UnexpectedEof => {
                            continue;
                        }
                        _ => {
                            println!("parse error at {}:{}-{}:{}: {:?}",
                                e.source.begin.line, e.source.begin.column,
                                e.source.end.line,   e.source.end.column,
                                e.data);
                            buffer.clear();
                            continue;
                        }
                    }
                }
            }
        };

        let mut module = ast::Module::new(ast.source, data::Block { stmts: vec![ast.to_stmt()] });

        let mut infer = infer::Infer::new();
        infer.assign_ids_module(&mut module);
        infer.infer_module(&mut module);

        let builder = bbir_builder::Builder::new();
        builder.build_module(&module);
        buffer.clear();


        running.store(true, core::sync::atomic::Ordering::SeqCst);
        builder.module.temp_load(&mut vm);
        let result = vm.temp_call();
        running.store(false, core::sync::atomic::Ordering::SeqCst);

        if let Err(_) = result {
            println!("runtime error");
            continue;
        }

        let dt = t0.elapsed();
        let di = vm.instruction_counter() - ic;
        println!("{:?}, {}op/s", t0.elapsed(), (di as f64 / dt.as_secs_f64()) as u64);
    }
}

