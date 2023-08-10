
- current:
    - foundation - parser, type inference, interpreter.
    - no macros.
    - no any.

- todo:
    - tt: do we actually need to generate the IR for inference?
        - couldn't we use the same logic (to identify var versions)
          and just use that for type inference.
          and only *generate* the IR for type checking (and actually
          using kernel terms).
    - parser.
        Block(expr::Block<'a>),
        Op1(expr::Op1<'a>),
        Op2(expr::Op2<'a>),
        Field(expr::Field<'a>),
        Index(expr::Index<'a>),
        Call(expr::Call<'a>),
        Assign(expr::Assign<'a>),
        Map(expr::Map<'a>),
        MapType(expr::MapType<'a>),
        Match(expr::Match<'a>),
        If(expr::If<'a>),
        Loop(expr::Loop<'a>),
        TypeHint(expr::TypeHint<'a>),
        Path(Path<'a>),
    - begin type inference.
        - type/expr repr.
        - start with axioms & built-ins. inductive later.
            - eq & nat w/ rec should be good enough for testing.


- backlog:
    - parser:
        - labels.
        - combined match/if.
        - optional do block.
    - macros:
        - figure out compilation order.

