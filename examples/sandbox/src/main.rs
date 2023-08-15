use kibi::ast::*;

fn main() {
    let arena = sti::growing_arena::GrowingArena::new();

    let input = "
reduce (λ(a: Nat, b: Nat) =>
        NatRec.{1}(
            λ(_: Nat) => Nat,
            a,
            λ(_: Nat, r: Nat) => NatSucc(r),
            b))(1, 2)

def Nat_add = λ(a: Nat, b: Nat) =>
        NatRec.{1}(
            λ(_: Nat) => Nat,
            a,
            λ(_: Nat, r: Nat) => NatSucc(r),
            b)

reduce Nat_add(1, 2)
";

    let tokens = kibi::parser::Tokenizer::tokenize(&arena, input.as_bytes());

    let mut parser = kibi::parser::Parser::new(&arena, &tokens);
    while !parser.tokens.is_empty() {
        let item = parser.parse_item().unwrap();

        match item.kind {
            ItemKind::Def(_) => {
            }

            ItemKind::Reduce(expr) => {
                let mut elab = kibi::elab::Elab::new(&arena);
                let (term, _) = elab.elab_expr(expr).unwrap();
                let red = elab.tc().reduce(term);
                println!("{:?}", red);
            }
        }
    }
}

