use luazero::*;


mod builtin {
    use super::*;

    pub(crate) fn print(vm: &mut Vm) -> Result<u32, ()> {
        // @todo-speed: remove check.
        let value = *vm.reg(0);
        vm.generic_print(value);
        return Ok(0);
    }
    pub(crate) const PRINT: FuncProto = FuncProto {
        code: FuncCode::Native(NativeFuncPtrEx(print)),
        constants: vec![],
        num_params: 1,
        stack_size: 1,
    };

    pub(crate) fn println(vm: &mut Vm) -> Result<u32, ()> {
        // @todo-speed: remove check.
        let value = *vm.reg(0);
        vm.generic_print(value);
        println!();
        return Ok(0);
    }
    pub(crate) const PRINTLN: FuncProto = FuncProto {
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

    vm.add_func("quit", FuncProto {
        code: FuncCode::Native(NativeFuncPtrEx(|_vm| std::process::exit(0))),
        constants: vec![],
        num_params: 0,
        stack_size: 0,
    });


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

        if let Err(_) = vm.call(0, 0, 0) {
            println!("runtime error");
            continue;
        }

        println!("{:?}", t0.elapsed());
    }
}

