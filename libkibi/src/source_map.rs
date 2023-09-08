use sti::vec::Vec;
use sti::traits::CopyIt;


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


pub struct SourceMap<'a> {
    files: Vec<File<'a>>,
    len: usize,
}

#[derive(Clone, Copy)]
struct File<'a> {
    name: &'a str,
    contents: &'a [u8],
}

impl<'a> SourceMap<'a> {
    pub fn new() -> Self {
        Self {
            files: Vec::new(),
            len: 0,
        }
    }

    pub fn add_file(&mut self, name: &'a str, contents: &'a [u8]) -> Option<u32> {
        let offset = self.len;

        // not enough space.
        if contents.len() > u32::MAX as usize - offset {
            return None
        }

        self.files.push(File { name, contents });
        self.len += contents.len();

        return Some(offset as u32);
    }

    pub fn lookup(&self, pos: u32) -> (&'a str, &'a [u8]) {
        let mut cursor = 0;
        for File { name, contents } in self.files.copy_it() {
            let end = cursor + contents.len() as u32;

            if pos < end {
                return (name, contents);
            }

            cursor = end;
        }
        unreachable!()
    }
}


