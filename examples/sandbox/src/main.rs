use kibi::compiler::Compiler;


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

    let mut comp = Compiler::new(); 
    comp.do_file("main.kb", input).unwrap();
}

