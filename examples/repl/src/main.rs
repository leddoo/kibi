use luazero::*;


mod builtin {
    use super::*;

    pub(crate) fn print(vm: &mut Vm) -> VmResult<u32> {
        vm.generic_print(0);
        return Ok(0);
    }
    pub(crate) const PRINT: FuncDesc = FuncDesc {
        code: FuncCode::Native(NativeFuncPtrEx(print)),
        constants: vec![],
        num_params: 1,
        stack_size: 1,
    };

    pub(crate) fn println(vm: &mut Vm) -> VmResult<u32> {
        vm.generic_print(0);
        println!();
        return Ok(0);
    }
    pub(crate) const PRINTLN: FuncDesc = FuncDesc {
        code: FuncCode::Native(NativeFuncPtrEx(println)),
        constants: vec![],
        num_params: 1,
        stack_size: 1,
    };

}


fn main() {
    {
        let example = r#"
            let foo = 42
            print(foo)

            let x = do
                var i = 0
                while i < 10:
                    i += 1
                    i *= 2
                end
                i
            end

            turtle
                .forward()
                .turn_left()
                .place()

            exit(0)
        "#;

        let mut line = 1;
        let mut toker = new_parser::Tokenizer::new(example.as_bytes());
        while let Some(tok) = toker.try_consume() {
            if tok.source.begin.line != line {
                line = tok.source.begin.line;
                println!();
            }
            print!("{:?} ", tok.data);
            if tok.source.is_collapsed() {
                print!("<<< inserted ");
            }
        }
        println!();


        let example = r#"
            var bar = 42
            bar
        "#;

        let mut p = new_parser::Parser::new(example.as_bytes());
        let chunk = p.parse_block().unwrap();
        println!("parsed: {:?}", chunk);


        if 1==1 { return }
    }

    let mut vm = Vm::new();

    vm.add_func("print", builtin::PRINT);
    vm.add_func("println", builtin::PRINTLN);
    vm.add_func("quit", FuncDesc {
        code: FuncCode::Native(NativeFuncPtrEx(|_| std::process::exit(0))),
        constants: vec![],
        num_params: 0,
        stack_size: 0,
    });


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

            match parse_single(chunk) {
                Ok(ast) => { ast }
                Err(e) => {
                    match e {
                        ParseError::Eoi => {
                            continue;
                        }
                        ParseError::Error => {
                            println!("parse error");
                            buffer.clear();
                            continue;
                        }
                    }
                }
            }
        };

        if let Err(_) = compile_chunk(&[ast], &mut vm) {
            println!("compile error");
            buffer.clear();
            continue;
        };
        buffer.clear();

        running.store(true, core::sync::atomic::Ordering::SeqCst);
        let result = vm.call();
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

