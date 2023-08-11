use sti::growing_arena::GrowingArena;


pub struct TyCtx<'a> {
    pub arena: &'a GrowingArena,
}

