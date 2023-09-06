use kibi::sti;
use kibi::pp::*;
use kibi::error::*;
use kibi::ast::*;
use kibi::tt::TermPP;
use kibi::env::*;


fn main() {
    let input = "
-- reduce (λ(a: Nat, b: Nat) => Nat::rec(a, λ _ r => Nat::succ(r), b))(1, 2)

def Nat::add (a b: Nat): Nat :=
    Nat::rec(a, λ _ r => Nat::succ(r), b)

reduce Nat::add(1, 2)
".as_bytes();

    let input = {
        let args = std::env::args();
        if args.len() == 2 {
            let path = args.into_iter().nth(1).unwrap();
            Vec::leak(std::fs::read(path).unwrap())
        }
        else { input }
    };

    let printing = true;

    let arena = sti::arena::Arena::new();
    arena.min_block_size.set(1024*1024);

    let mut strings = kibi::string_table::StringTable::new(&arena);

    let tok_t0 = std::time::Instant::now();
    let tokens = kibi::parser::Tokenizer::tokenize(input, 0, &mut strings, &arena);
    if printing { println!("tok: {:?}", tok_t0.elapsed()) }

    let mut env = Env::new();

    let errors = ErrorCtx::new(&arena);

    let mut parse_dt = std::time::Duration::ZERO;
    let mut work_dt = std::time::Duration::ZERO;

    let mut parser = kibi::parser::Parser::new(&tokens, &errors, &strings, &arena);
    while !parser.tokens.is_empty() {
        let t0 = std::time::Instant::now();

        let Some(item) = parser.parse_item() else { break };

        parse_dt += t0.elapsed();

        let mut elab = kibi::elab::Elab::new(&mut env, SymbolId::ROOT, &errors, &strings, &arena);

        match &item.kind {
            ItemKind::Axiom(axiom) => {
                let Some(_) = elab.elab_axiom(axiom) else { break };
                work_dt += t0.elapsed();

                if printing {
                    print!("axiom ");
                    match axiom.name {
                        IdentOrPath::Ident(name) => {
                            println!("{}", &strings[name]);
                        }

                        IdentOrPath::Path(path) => {
                            print!("{}", &strings[path.parts[0]]);
                            for part in path.parts[1..].iter().copied() {
                                print!("::{}", &strings[part]);
                            }
                            println!();
                        }
                    }
                }

                let Some(()) = elab.check_no_unassigned_variables() else {
                    println!("error: unassigned inference variables");
                    break;
                };
            }

            ItemKind::Def(def) => {
                let Some(_) = elab.elab_def(def) else { break };
                work_dt += t0.elapsed();

                if printing {
                    print!("def ");
                    match def.name {
                        IdentOrPath::Ident(name) => {
                            println!("{}", &strings[name]);
                        }

                        IdentOrPath::Path(path) => {
                            print!("{}", &strings[path.parts[0]]);
                            for part in path.parts[1..].iter().copied() {
                                print!("::{}", &strings[part]);
                            }
                            println!();
                        }
                    }
                }

                let Some(()) = elab.check_no_unassigned_variables() else {
                    println!("error: unassigned inference variables");
                    break;
                };
            }

            ItemKind::Reduce(expr) => {
                let Some((term, _)) = elab.elab_expr(expr) else { break };
                let r = elab.reduce(term);
                work_dt += t0.elapsed();

                if printing {
                    let temp = sti::arena_pool::ArenaPool::tls_get_temp();
                    let mut pp = TermPP::new(&elab.env, &strings, &*temp);
                    let r = pp.pp_term(r);
                    let r = pp.indent(9, r);
                    let r = pp.render(r, 80);
                    let r = r.layout_string();
                    println!("reduced: {}", r);
                }
            }

            ItemKind::Inductive(ind) => {
                let Some(_) = elab.elab_inductive(ind) else { break };
                work_dt += t0.elapsed();

                if printing {
                    println!("inductive {}", &strings[ind.name]);
                }
            }
        }
    }

    if printing {
        let stats = arena.stats();
        println!("allocated: {}, blocks: {}",
            stats.total_allocated - arena.current_block_size() + arena.current_block_used(),
            stats.num_blocks);
        println!("parse: {:?}", parse_dt);
        println!("work:  {:?}", work_dt);
    }

    errors.with(|errors| {
        errors.iter(|e| {
            // error line:
            {
                print!("error: ");

                match e.kind {
                    ErrorKind::Parse(e) => {
                        match e {
                            ParseError::Expected(what) => {
                                println!("expected: {what}");
                            }

                            ParseError::Unexpected(what) => {
                                println!("unexpected: {what}");
                            }
                        }
                    }

                    ErrorKind::Elab(e) => {
                        match e {
                            ElabError::SymbolShadowedByLocal(name) => {
                                println!("symbol {:?} shadowed by a local variable", name);
                            }

                            ElabError::UnresolvedLevel(name) => {
                                println!("unresolved level: {name:?}");
                            }

                            ElabError::UnresolvedName { base, name } => {
                                if base != "" {
                                    println!("unresolved name. cannot find {name:?} in {base:?}");
                                }
                                else {
                                    println!("unresolved name: {name:?}");
                                }
                            }

                            ElabError::LevelMismatch { expected, found } => {
                                println!("level count mismatch. expected {expected} levels, found {found}");
                            }

                            ElabError::TypeMismatch {..} => {
                                println!("type mismatch.");
                            }

                            ElabError::TypeExpected {..} => {
                                println!("type expected.");
                            }

                            ElabError::TooManyArgs => {
                                println!("too many args.");
                            }
                        }
                    }
                }
            }

            // code:
            {
                let err_begin = e.source.begin as usize;
                let err_end   = e.source.end   as usize;
                let mut begin = err_begin;
                let mut end   = err_end;
                while begin > 0 && input[begin - 1] != b'\n' { begin -= 1 }
                while end < input.len() && input[end] != b'\n' { end += 1 }

                let begin_line = {
                    let mut line = 1;
                    let mut at = begin;
                    while at > 0 {
                        if input[at] == b'\n' { line += 1 }
                        at -= 1;
                    }
                    line
                };

                let string = unsafe { core::str::from_utf8_unchecked(&input[begin..end]) };

                let mut line = begin_line;
                let mut at = begin;
                for l in string.lines() {
                    println!("{:4} | {}", line, l);

                    let end = at + l.len();
                    if err_begin < end && err_end > at {
                        let b = err_begin.max(at) - at;
                        let e = err_end.min(end)  - at;
                        for _ in 0..b+7 { print!(" ") }
                        for _ in 0..(e-b).max(1) { print!("^") }
                        println!();
                    }

                    line += 1;
                    at = end + 1;
                }
            }

            // extra info.
            {
                match e.kind {
                    ErrorKind::Parse(e) => {
                        match e {
                            ParseError::Expected(_) => {}
                            ParseError::Unexpected(_) => {}
                        }
                    }

                    ErrorKind::Elab(e) => {
                        match e {
                            ElabError::SymbolShadowedByLocal(_) => {
                            }

                            ElabError::UnresolvedName {..} => {}

                            ElabError::UnresolvedLevel(_) => {}

                            ElabError::LevelMismatch {..} => {}

                            ElabError::TypeMismatch { expected, found } => {
                                let pp = PP::new(&arena);
                                let expected = pp.render(expected, 50);
                                let expected = expected.layout_string();
                                let found = pp.render(found, 50);
                                let found = found.layout_string();
                                println!("expected: {}", expected.lines().next().unwrap());
                                for line in expected.lines().skip(1) {
                                    println!("          {}", line);
                                }
                                println!("found:    {}", found.lines().next().unwrap());
                                for line in found.lines().skip(1) {
                                    println!("          {}", line);
                                }
                            }

                            ElabError::TypeExpected { found } => {
                                let pp = PP::new(&arena);
                                let found = pp.render(found, 50);
                                let found = found.layout_string();
                                println!("found: {}", found.lines().next().unwrap());
                                for line in found.lines().skip(1) {
                                    println!("       {}", line);
                                }
                            }

                            ElabError::TooManyArgs => (),
                        }
                    }
                }
            }

            println!();
        });
    });
}

