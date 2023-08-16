
#[derive(Clone, Copy, Debug)]
pub struct SourceRange {
    pub begin: u32,
    pub end:   u32,
}

impl SourceRange {
    #[track_caller]
    #[inline(always)]
    pub fn join(self, other: SourceRange) -> SourceRange {
        debug_assert!(self.begin <= other.end);
        SourceRange { begin: self.begin, end: other.end }
    }
}


