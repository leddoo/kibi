
#[derive(Clone, Copy, Debug)]
pub struct SourceRange {
    pub begin: u32,
    pub end:   u32,
}

impl SourceRange {
    pub const UNKNOWN: SourceRange = SourceRange { begin: 0, end: 0 };

    #[inline(always)]
    pub fn collapsed(pos: u32) -> SourceRange {
        SourceRange { begin: pos, end: pos }
    }

    #[track_caller]
    #[inline(always)]
    pub fn join(self, other: SourceRange) -> SourceRange {
        debug_assert!(self.begin <= other.end);
        SourceRange { begin: self.begin, end: other.end }
    }
}


