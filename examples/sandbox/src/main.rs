
fn main() {
    let arena = sti::growing_arena::GrowingArena::new();

    let mut tok = kibi::parser::Tokenizer::new(&arena, r#"
        fn dump_json(val: JsonValue, indent = 0, do_indent = true) {
            if do_indent {
                print("  " * indent)
            }

            match val {
                -- .null      => println(f"null")
                -- .boolean b => println(f"a bool {b}")
                -- .number  n => println(f"a number {n}")

                .array a => {
                    println("an array:")
                    for v in a {
                        dump_json(v, indent + 1)
                    }
                }

                .object o => {
                    println("an object:")
                    for k, v in o {
                        -- print(f"{"  " * (indent + 1)}{k}: ")
                        dump_json(v, indent + 1, do_indent = false)
                    }
                }
            }
        }
    "#.as_bytes());

    let tokens = tok.run();
    for tok in &tokens {
        println!("{:?}", tok);
    }
}

