use kibi::error::ErrorCtx;

use kibi::tt::*;
use kibi::env::*;


#[test]
fn nat_add_elab() {
    let arena = sti::growing_arena::GrowingArena::new();
    let alloc = Alloc::new(&arena);

    // λ a b, Nat.rec(b, (λ _, Nat), a, (λ _ r, Nat.succ(r)))
    let nat_add = &*
        alloc.mkt_lambda(0, Term::NAT,
        alloc.mkt_lambda(1, Term::NAT,
            alloc.mkt_apps(alloc.mkt_nat_rec(Level::L1), &[
                alloc.mkt_bvar(BVar(0)),
                alloc.mkt_lambda(2, Term::NAT, Term::NAT),
                alloc.mkt_bvar(BVar(1)),
                alloc.mkt_lambda(
                    3,
                    Term::NAT,
                    alloc.mkt_lambda(
                        4,
                        Term::NAT,
                        alloc.mkt_apply(
                            Term::NAT_SUCC,
                            alloc.mkt_bvar(BVar(0))))),
            ])));

    let mut env = Env::new();
    let nat = env.create_nat();
    let eq = env.create_eq();
    let ns  = env.create_initial(nat, eq);

    let errors = ErrorCtx::new(&arena);

    let nat_add = {
        let input = "λ(a: Nat, b: Nat) =>
            Nat::rec.{1}(b, λ(_: Nat) => Nat, a, λ(_: Nat, r: Nat) => Nat::succ(r))";

        let tokens = kibi::parser::Tokenizer::tokenize(&arena, 0, input.as_bytes());

        let mut parser = kibi::parser::Parser::new(&arena, &errors, &tokens);
        let ast = parser.parse_expr().unwrap();

        let mut elab = kibi::elab::Elab::new(&mut env, ns, &errors, &arena);
        let (term, _) = elab.elab_expr(&ast).unwrap();

        assert!(term.syntax_eq(nat_add));

        term
    };

    errors.with(|errors| assert!(errors.empty()));

    let n1 = alloc.mkt_nat_val(1);
    let n2 = alloc.mkt_nat_val(2);
    let n3 = alloc.mkt_nat_val(3);

    let n3_add = alloc.mkt_apps(nat_add, &[n1, n2]);

    let mut lctx = LocalCtx::new(alloc);
    let mut tc = TyCtx::new(alloc, &mut lctx, &env);

    assert!(tc.reduce(n3_add).syntax_eq(n3));

    let n3_ty = tc.infer_type(n3_add).unwrap();
    assert!(tc.whnf(n3_ty).syntax_eq(Term::NAT));
}

