use kibi::error::ErrorCtx;

use kibi::string_table::StringTable;
use kibi::tt::*;
use kibi::env::*;


#[test]
fn nat_add_elab() {
    let alloc = sti::arena::Arena::new();

    let mut strings = StringTable::new(&alloc);

    // λ a b, Nat.rec((λ _, Nat), a, (λ _ r, Nat.succ(r)), b)
    let nat_add =
        alloc.mkt_lambda(strings.insert("a"), Term::NAT,
        alloc.mkt_lambda(strings.insert("b"), Term::NAT,
            alloc.mkt_apps(alloc.mkt_nat_rec(Level::L1), &[
                alloc.mkt_lambda(strings.insert(""), Term::NAT, Term::NAT),
                alloc.mkt_bound(BVar { offset: 1 }),
                alloc.mkt_lambda(
                    strings.insert("_"),
                    Term::NAT,
                    alloc.mkt_lambda(
                        strings.insert("r"),
                        Term::NAT,
                        alloc.mkt_apply(
                            Term::NAT_SUCC,
                            alloc.mkt_bound(BVar { offset: 0 })))),
                alloc.mkt_bound(BVar { offset: 0 }),
            ])));

    let mut env = Env::new();

    let errors = ErrorCtx::new(&alloc);

    let nat_add = {
        let input = "λ(a: Nat, b: Nat) =>
            Nat::rec(λ(_: _) => _, a, λ(_: _, r: _) => Nat::succ(r), b)";

        let tokens = kibi::parser::Tokenizer::tokenize(input.as_bytes(), 0, &mut strings, &alloc);

        let mut parser = kibi::parser::Parser::new(&tokens, &errors, &strings, &alloc);
        let ast = parser.parse_expr().unwrap();

        let mut elab = kibi::elab::Elab::new(&mut env, SymbolId::ROOT, &errors, &strings, &alloc);
        let (term, _) = elab.elab_expr(&ast).unwrap();

        let term = elab.instantiate_term_vars(term);
        assert!(elab.check_no_unassigned_variables().is_some());

        let term = elab.reduce_ex(term, false);
        assert!(term.syntax_eq(nat_add));

        term
    };

    errors.with(|errors| assert!(errors.empty()));

    let n1 = alloc.mkt_nat_val(1);
    let n2 = alloc.mkt_nat_val(2);
    let n3 = alloc.mkt_nat_val(3);

    let n3_add = alloc.mkt_apps(nat_add, &[n1, n2]);

    let mut elab = kibi::elab::Elab::new(&mut env, SymbolId::ROOT, &errors, &strings, &alloc);
    assert!(elab.reduce(n3_add).syntax_eq(n3));

    let n3_ty = elab.infer_type(n3_add).unwrap();
    assert!(elab.whnf(n3_ty).syntax_eq(Term::NAT));
}

