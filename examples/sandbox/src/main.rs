use sti::vec::Vec;

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

def Nat::add (a: Nat, b: Nat): Nat :=
    Nat::rec.{1}(
        b,
        λ(_: Nat) => Nat,
        a,
        λ(_: Nat, r: Nat) => Nat::succ(r))

reduce Nat::add(1, 2)
";

    let tokens = kibi::parser::Tokenizer::tokenize(&arena, 0, input.as_bytes());

    let mut env = Env::new();
    let nat = env.create_nat();
    let ns = env.create_initial(nat);

    let mut parse_errors = Vec::new();

    let mut elab = kibi::elab::Elab::new(&mut env, ns, &arena);

    let mut parser = kibi::parser::Parser::new(&arena, &mut parse_errors, &tokens);
    while !parser.tokens.is_empty() {
        let Some(item) = parser.parse_item() else { break };

        match &item.kind {
            ItemKind::Def(def) => {
                let Some(_) = elab.elab_def(def) else { break };
            }

            ItemKind::Reduce(expr) => {
                let Some((term, _)) = elab.elab_expr(expr) else { break };
                let red = elab.tc().reduce(term);
                println!("{:?}", red);
            }
        }
    }

    let mut errors = Vec::new();
    for e in &parse_errors { errors.push(e) }

    for e in &errors {
        println!("{:?}", e);
        let mut begin = (e.source.begin - 10.min(e.source.begin)) as usize;
        let mut end = (e.source.end   + 10).min(input.len() as u32) as usize;
        while input.as_bytes()[begin] & 0xc0 == 0x80 { begin -= 1 }
        while input.as_bytes()[end]   & 0xc0 == 0x80 { end   -= 1 }
        println!("{:?}", &input[begin..end]);
    }
}

