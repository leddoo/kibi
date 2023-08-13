
- current:
    - foundation - parser, type inference, interpreter.
    - no macros.
    - no any.

- todo:
    - tt imp:
        - infer type.
        - def-eq.

    - sti:
        - Vec::truncate track caller.
        - KVec::truncate, clone.


- stuff:
    - parser.
        Block(expr::Block<'a>),
        Field(expr::Field<'a>),
        Index(expr::Index<'a>),
        Call(expr::Call<'a>),
        - method call.
        Map(expr::Map<'a>),
        MapType(expr::MapType<'a>),
        Match(expr::Match<'a>),
        If(expr::If<'a>),
        Loop(expr::Loop<'a>),
        TypeHint(expr::TypeHint<'a>),
        Path(Path<'a>),


- backlog:
    - parser:
        - labels.
        - combined match/if.
        - optional do block.
    - macros:
        - figure out compilation order.

