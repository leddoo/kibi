- traits:
    - binders:
        - orthogonal to explicit/implicit.
        - if implicit or `_`, does impl resolution.
        - syntax:
            - `<A>` means `<A: Type>`.
            - `<A is Foo + Bar>` means `<A: Type, _: Foo(A), _: Bar(A)>`.

- memory management for lsp aka incremental compilation:
    - string table:
        - assuming the user types 5 characters per second,
          which is way too much,
          and that every keystroke results in a new string,
          where the average identifier length is 10 bytes,
          we allocate 50 bytes per second.
          filling 1 MiB of memory would take 6 hours.
        - so we just don't free strings.
    - errors: tbd.
    - tokens & ast:
        - one arena per file.
    - terms:
        - thinking one arena per definition. compact after elab.
        - we'll have to trade some cycles for memory usage here.
        - though the compaction also leads to linear traversals
          (if done right), so it could actually improve perf.
        - i mean, for now, we don't have to compact at all.
        - since we want the local & ivar contexts too,
          ig we should store those in the env.
        - for join points, we'd like those to be owned by their
          definition, cause well, they're one thing. so the data
          could be stored on the parent symbol, the join points
          just referring to that.
        - re copying out: though that would actually be easier,
          as we can use stuff from the env for type checking
          without copying on read. and results may not end up in
          final term.
    - re incremental:
        - technically, multiple arenas doesn't make sense,
          until we do incremental compilation.
          cause we need to process the entire file anyway.
        - so how does incr work?
        - well, we need to identify all dependencies of an item.
          that's its ast + the env.
          for the env, it's looked up names & data of used symbols.
        - name dependencies may be relevant for MT too.


- effects:
    - in particular, panics.
    - `fn foo(): B` means `lam foo(_: ()): Io(B)` or something like that.
    - so if you use `fn` in traits, you expect those to potentially panic
      or have other side-effects.
    - using `Pi`, you can make that explicit (or require totality).
    - the IR is going to get pretty nasty though. oh well.
        - actually, that's pretty bad.
        - cause it also breaks `A -> B -> C`.
        - we could just mark the decl as partial.
        - yeah, that seems better.
        - we could still do explicit effects later on.
          for now, `partial` as a catch-all seems fine.



