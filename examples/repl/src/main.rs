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
            -- var bar = foo(1, 2+3) / 4
            -- ( a + f ( x ) ( y ) ) ( z )
            -- ()
            -- (a)
            -- (a,)
            -- (a,b)=(b,a)
            -- a[0] = foo.bar
            -- true == false or false and true
            -- do var i = 0; i += 1; i *= 2; i end
            -- if true: print(42) end
            -- if a == false: true else false end
            -- if a==1: one elif a==2: two else three end
            -- while true: print(hi) end
            -- return
            -- return 42
            -- let foo = (return 42) or 7
            -- ;-a;
            -- ;-a.foo;
            -- ;-a+foo;
            -- a + not b
            -- not a or b and not c
            -- nil ?? a <= false ?? true
            -- a?.foo
            -- fn foo(a, b): a + b end
            -- fn a, b => a + b
            -- [a, b,]
            -- { a, b: c }
            -- print("hi")

            --[[
                a
                --[[
                    b
                --]]
                c
            --]]

            --[[
            let a = true or false
            let b
            if a:
                a
            else:
                b = a
                b += true
            end
            --]]

            -- --[[

            -- bb0
            let a; let b; let c

            if true:
                -- bb1
                a += b

                -- bb4
                while b > c:
                    -- bb5
                    b -= c / a
                end

                -- bb6
            else:
                -- bb2
                a = c / a
                b = false
            end

            -- bb3
            let d = if true: a end -- bb7/8

            -- bb9
            a + a
            b + b
            c + c
            d + d

            --]]

            --[[

            -- bb0
            let a
            let one
            let n
            let x
            let y
            -- bb1
            while x < n:
                -- bb2
                -- let y -- broken

                -- bb4
                while y < n:
                    -- bb5
                    a += a
                    y += one
                end

                -- bb6
                a *= a
                x += one
            end

            -- bb3
            --]]
        "#;

        let mut p = new_parser::Parser::new(example.as_bytes());
        let (chunk_source, chunk) = p.parse_block().unwrap();
        //println!("parsed: {:#?}", chunk);

        let mut c = new_compiler::Compiler {};
        c.compile_chunk(chunk_source, &chunk).unwrap();


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

