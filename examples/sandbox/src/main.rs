use kibi::ast::*;
use kibi::env::*;

fn main() {
    let arena = sti::growing_arena::GrowingArena::new();

    let input = "
reduce (λ(a: Nat, b: Nat) =>
    Nat::rec.{1}(
        b,
        λ(_: Nat) => Nat,
        a,
        λ(_: Nat, r: Nat) => Nat::succ(r))
    )(1, 2)

def Nat.add (a: Nat, b: Nat): Nat =
    b.rec.{1}(
        λ(_: Nat) => Nat,
        a,
        λ(_: Nat, r: Nat) => r.succ)

reduce 1.add(2)
";

    let tokens = kibi::parser::Tokenizer::tokenize(&arena, input.as_bytes());

    let mut env = Env::new();
    let nat = env.create_nat();
    let ns = env.create_initial(nat);

    let mut parser = kibi::parser::Parser::new(&arena, &tokens);
    while !parser.tokens.is_empty() {
        let item = parser.parse_item().unwrap();

        match item.kind {
            ItemKind::Def(_) => {
            }

            ItemKind::Reduce(expr) => {
                let mut elab = kibi::elab::Elab::new(&mut env, ns, &arena);
                let (term, _) = elab.elab_expr(expr).unwrap();
                let red = elab.tc().reduce(term);
                println!("{:?}", red);
            }
        }
    }
}

