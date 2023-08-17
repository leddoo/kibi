use sti::vec::Vec;

use kibi::ast::*;
use kibi::env::*;


fn main() {
    let arena = sti::growing_arena::GrowingArena::new();
    arena.min_block_size.set(1024*1024);

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

    let p0 = arena.alloc_ptr::<u8>().as_ptr() as usize;
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
                println!("def {:?}", def.name);
            }

            ItemKind::Reduce(expr) => {
                let Some((term, _)) = elab.elab_expr(expr) else { break };
                let red = elab.tc().reduce(term);
                println!("reduced: {:?}", red);
            }
        }
    }

    let p1 = arena.alloc_ptr::<u8>().as_ptr() as usize;
    println!("total: {:?}", p1 - p0 - 16);

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


    let pp = kibi::pp::PP::new(&arena);

    /*
        want:
            hello a b c d

            hello a b c
              d

            hello a b
              c d
    */

    let p0 = arena.alloc_ptr::<u8>().as_ptr() as usize;
    let doc =
        pp.group(pp.cat(
            pp.group(pp.cat(
                pp.group(pp.cat(
                    pp.group(pp.cat(
                        pp.text("hello"),
                        pp.cat(pp.line(), pp.text("a")))),
                    pp.cat(pp.line(), pp.text("b")))),
                pp.cat(pp.line(), pp.text("c")))),
            pp.cat(pp.line(), pp.text("d"))));
    let p1 = arena.alloc_ptr::<u8>().as_ptr() as usize;
    println!("pp size: {:?}", p1 - p0 - 16);

    let p0 = arena.alloc_ptr::<u8>().as_ptr() as usize;
    let doc = pp.group(pp.cats(&[
        pp.text("hello"),
        pp.group(pp.indent(1, pp.cats(&[
            pp.group(pp.cat(pp.line(), pp.text("a,"))),
            pp.group(pp.cat(pp.line(), pp.text("b,"))),
            pp.group(pp.cat(pp.line(), pp.text("c,"))),
            pp.group(pp.cat(pp.line(), pp.text("d;"))),
        ]))),
    ]));
    let p1 = arena.alloc_ptr::<u8>().as_ptr() as usize;
    println!("pp size: {:?}", p1 - p0 - 16);

    let print = |doc: &kibi::pp::Doc, width: i32| {
        let doc = pp.render(doc, width);

        let mut buffer = String::new();
        doc.layout_string(&mut buffer);

        for _ in 0..width { print!("-") } println!();
        println!("{}", buffer);
    };

    for i in (5..18).step_by(3) {
        print(doc, i);
    }
}

