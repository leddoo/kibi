- defs:
    - gen(pp): set of used variables.
    - kill(pp): set of defined variables.
    - dataflow equations:
        ```
        // regular statements: one `in` set for all preds.
        live_in(pp) = (live_out(pp) - kill(pp)) ∪ gen(pp)

        // phis: one `in` set for each pred..
        // and all phis are simultaneous.
        live_in(phis(maps), pred) = (live_out(phis) - kills(phis)) ∪ {map[pred] for map in maps}

        live_out(pp)    = ∪(live_in(pp) for s in succ(pp))
        live_out(final) = ∅
        ```

