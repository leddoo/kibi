
- defs:
    - dominates(a, b): all paths from entry to b flow through a.
    - strictly dominates(a, b): dom(a, b) ∧ a ≠ b
    - immediately dominates(a, b): sdom(a, b) ∧ ¬∃ c, sdom(a, c) ∧ sdom(c, b)
    - dominance frontier(a): { b, ¬sdom(a, b) ∧ ∃ p: pred(b), dom(a, p) }


- compute idom:
    ```
    doms = { nil for bb in bbs }
    doms[bb0] = bb0

    while changed:
        for bb in bbs.reverse_post_order:
            if bb == bb0: continue

            new_idom = first pred p, where doms[p] != nil
            for p in bb.pred:
                if p != new_idom and doms[p] != nil:
                    new_idom = intersect(p, new_idom)

            doms[bb] = new_dom

    fn rpi(a) = bbs.reverse_post_order.find_index(a)

    fn intersect(a, b):
        x = a
        y = b
        while x != y:
            while rpi(x) < rpi(y):
                x = doms[x]
            while rpi(y) < rpi(x:
                y = doms[y]
        return x
    ```
    - how the heck does it work?
        - 1) nodes higher in the dominance tree have higher postorder indices.
            - root is entry; entry postorder index is max.
            - for other nodes: something like "lower index node can only have edge to higher index node, if there's a loop. and then, the lower index node can't dominate."
        - 2) dom is union of idoms.
            - `∀ b, dom(b) = { b, idom(b), idom(idom(b)), ..., bb0 }`
            - similar logic: if there's another dom, that's not in the chain, there must be another path from the root to the node. so it's not a dom.
        - 3) the dom equation:
            - `dom[a] = {a} ∪ ∩(dom[p] for p in preds(a))`.
            - `dom[a] = {a} ∪ ∩({p, idom(p), ...} for p in preds(a))`.
            - intersection is assoc/comm.
            - intersection looks like: `{p, idom(p), ...} ∩ {q, idom(q), ...}`.
                - so this will be some sequence of idoms.
                - meaning, once we hit the first common idom, all following ones will be the same.
            - why does the postorder index comparison work?
                - all indices in a sub-tree are less.
            - but doms isn't idom! why don't we miss anything?
                - we start at the node itself.
                - and do that in each iteration.
        - other observations:
            - we always start with a predecessor, then move up.
                - this seems to guarantee the immediacy.
                - in particular: if indeg(bb) < 2, idom(bb) = bb.pred.
                - for indeg(bb) >= 2, we use intersection to find the first common ancestor.
            - when does the algo require multiple iters?
                - looks like that happens for irreducible graphs.
                - eg: initial iter may find one loop entry as the idom. in next iter, other preds are processed & intersection will go higher up.


- compute df:
    ```
    df = [ [] for bb in bbs ]

    for bb in bbs:
        for p in bb.preds:
            at = p
            while at ≠ idom(bb):
                df[at].add(bb)
                at = idom(at)
    ```

- convert to ssa:
    ```
    def insert_phis():
        for var in vars:
            for d in defs(var):
                for bb in df(d.bb):
                    add once to bb: `var = phi [(p, var) for p in bb.preds]`
                    and add this new def to defs(var)

    def rename_vars():
        def visit(bb, new_names):
            -- update var names.
            for stmt in bb:
                replace args with new_names[arg]
                replace dst with new_dst
                -- immutable update.
                new_names[dst].push(new_dst)
            
            -- propagate to successors (dominance frontier)
            for s in bb.succ:
                update phi reads

            -- propagate to dominated nodes.
            -- these don't have phi nodes & can read directly from new_names.
            for d in idom_by(bb):
                rename(d, new_names)

        visit(bb0, [ [var] for var in vars ])
    ```
