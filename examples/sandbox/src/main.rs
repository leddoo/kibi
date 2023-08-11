
fn main() {
    let arena = sti::growing_arena::GrowingArena::new();

    if 1==1 {
        use kibi::tt::*;

        // λ a b, Nat.rec((λ _, Nat), a, (λ _ r, Nat.succ(r)), b)
        let nat_add = &*
            arena.alloc_new(
            Term::mk_lambda(0, arena.alloc_new(Term::mk_nat()),
                arena.alloc_new(
                Term::mk_lambda(1, arena.alloc_new(Term::mk_nat()),
                    arena.alloc_new(
                    Term::mk_apply(
                        arena.alloc_new(
                        Term::mk_apply(
                            arena.alloc_new(
                            Term::mk_apply(
                                arena.alloc_new(
                                Term::mk_apply(
                                    arena.alloc_new(Term::mk_nat_rec(Level::L1)),
                                    arena.alloc_new(
                                    Term::mk_lambda(
                                        2,
                                        arena.alloc_new(Term::mk_nat()),
                                        arena.alloc_new(Term::mk_nat()))))),
                                arena.alloc_new(
                                Term::mk_bvar(BVar(1))))),
                            arena.alloc_new(
                            Term::mk_lambda(
                                3,
                                arena.alloc_new(Term::mk_nat()),
                                arena.alloc_new(
                                Term::mk_lambda(
                                    4,
                                    arena.alloc_new(Term::mk_nat()),
                                    arena.alloc_new(
                                    Term::mk_apply(
                                        arena.alloc_new(
                                        Term::mk_nat_succ()),
                                        arena.alloc_new(
                                        Term::mk_bvar(BVar(0))))))))))),
                        arena.alloc_new(
                        Term::mk_bvar(BVar(0)))))))));

        let n0 = &*arena.alloc_new(Term::mk_nat_zero());
        let n1 = &*arena.alloc_new(Term::mk_apply(arena.alloc_new(Term::mk_nat_succ()), arena.alloc_new(n0)));
        let n2 = &*arena.alloc_new(Term::mk_apply(arena.alloc_new(Term::mk_nat_succ()), arena.alloc_new(n1)));

        let n3 = &*
            arena.alloc_new(
            Term::mk_apply(
                arena.alloc_new(
                Term::mk_apply(
                    nat_add,
                    n1)),
                n2));

        let mut tc = TyCtx::new(&arena);
        let n3r = tc.reduce(n3);
        println!("{:?}", n3r);

        return;
    }

    let mut tok = kibi::parser::Tokenizer::new(&arena, r#"
        0
        false
        "hi\n\\\""
        a
        [a, b]
        [a, b,]
        a + b
        a + b * c - -d * e
        if a + b < c {
            c *= 2
        }

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

    let mut parser = kibi::parser::Parser::new(&arena, &tokens);
    while let Some(expr) = parser.parse_expr() {
        println!("{:?}", expr);
    }
}

