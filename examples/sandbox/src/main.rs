
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

        let nat_add = {
            let input = "λ(a: Nat, b: Nat) =>
                NatRec.{1}(λ(_: Nat) => Nat, a, λ(_: Nat, r: Nat) => NatSucc(r), b)";

            let tokens = kibi::parser::Tokenizer::tokenize(&arena, input.as_bytes());

            let mut parser = kibi::parser::Parser::new(&arena, &tokens);
            let ast = parser.parse_expr().unwrap();

            let mut elab = kibi::elab::Elab::new(&arena);
            let term = elab.elab_term(&ast).unwrap();

            term
        };

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

        let alloc = Alloc::new(&arena);
        let mut tc = TyCtx::new(alloc);
        let n3r = tc.reduce(n3);
        println!("{:?}", n3r);

        let n3t = tc.infer_type(n3).unwrap();
        let n3tw = tc.whnf(n3t);
        println!("type of 3: {:?}", n3tw);

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

