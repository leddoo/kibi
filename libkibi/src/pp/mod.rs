use sti::growing_arena::GrowingArena;


// impl of "A prettier printer" by Philip Wadler
// https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf


pub struct PP<'a> {
    arena: &'a GrowingArena,
}


pub type DocRef<'a> = &'a Doc<'a>;

pub struct Doc<'a> {
    pub kind: DocKind<'a>,
}

#[derive(Debug)]
pub enum DocKind<'a> {
    Nil,
    Text  (&'a str,    DocRef<'a>),
    Line  (i32,        DocRef<'a>),
    Choice(DocRef<'a>, DocRef<'a>),
}


impl<'a> Doc<'a> {
    #[inline(always)]
    pub fn ptr_eq(&self, other: &Doc) -> bool {
        core::ptr::eq(self, other)
    }

    pub fn fits(&self, width: i32) -> bool {
        if width < 0 {
            return false;
        }

        match self.kind {
            DocKind::Nil => true,

            DocKind::Text(string, rest) => 
                rest.fits(width - string.len() as i32),

            DocKind::Line(_, _) => true,

            DocKind::Choice(_, _) => unreachable!()
        }
    }

    pub fn layout(&self, buffer: &mut String) {
        self.layout_ex(0, buffer)
    }

    pub fn layout_ex(&self, indent: i32, buffer: &mut String) {
        match self.kind {
            DocKind::Nil => (),

            DocKind::Text(string, rest) => {
                buffer.push_str(string);
                rest.layout_ex(indent, buffer);
            }

            DocKind::Line(delta, rest) => {
                buffer.push('\n');
                let new_indent = indent + delta;
                for _ in 0..new_indent {
                    buffer.push(' ');
                }
                rest.layout_ex(new_indent, buffer)
            }

            DocKind::Choice(_, _) => unreachable!(),
        }
    }
}

impl<'a> core::fmt::Debug for Doc<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        self.kind.fmt(f)
    }
}


impl<'a> PP<'a> {
    #[inline(always)]
    pub fn new(arena: &'a GrowingArena) -> Self {
        Self { arena }
    }

    #[inline(always)]
    pub fn nil(&self) -> DocRef<'a> {
        &Doc { kind: DocKind::Nil }
    }

    #[inline(always)]
    pub fn text_and(&self, string: &'a str, rest: DocRef<'a>) -> DocRef<'a> {
        if string.len() == 0 {
            return rest;
        }
        self.arena.alloc_new(Doc { kind: DocKind::Text(string, rest) })
    }

    #[inline(always)]
    pub fn text(&self, string: &'a str) -> DocRef<'a> {
        self.text_and(string, self.nil())
    }

    #[inline(always)]
    pub fn line(&self, indent_delta: i32, rest: DocRef<'a>) -> DocRef<'a> {
        self.arena.alloc_new(Doc { kind: DocKind::Line(indent_delta, rest) })
    }


    #[inline(always)]
    fn choice(&self, a: DocRef<'a>, b: DocRef<'a>) -> DocRef<'a> {
        self.arena.alloc_new(Doc { kind: DocKind::Choice(a, b) })
    }

    pub fn cat(&self, a: DocRef<'a>, b: DocRef<'a>) -> DocRef<'a> {
        match a.kind {
            // Nil <> y = y
            DocKind::Nil => b,

            // (s ‘Text‘ x) <> y = s ‘Text‘ (x <> y)
            DocKind::Text(string, rest) =>
                self.text_and(string, self.cat(rest, b)),

            // (i ‘Line‘ x) <> y = i ‘Line‘ (x <> y)
            DocKind::Line(delta, rest) =>
                self.line(delta, self.cat(rest, b)),

            // (x ‘Union‘ y) <> z = (x <> z) ‘Union‘ (y <> z)
            DocKind::Choice(c1, c2) =>
                self.choice(
                    self.cat(c1, b),
                    self.cat(c2, b)),
        }
    }

    pub fn group(&self, doc: DocRef<'a>) -> DocRef<'a> {
        match doc.kind {
            // group Nil = Nil
            DocKind::Nil => doc,

            // group (s ‘Text‘ x) = s ‘Text‘ group x
            DocKind::Text(string, rest) => {
                let rest_group = self.group(rest);
                if rest_group.ptr_eq(rest) {
                    return doc;
                }
                self.text_and(string, rest_group)
            }

            // group (i ‘Line‘ x) = (" " ‘Text‘ flatten x) ‘Union‘ (i ‘Line‘ x)
            DocKind::Line(_, rest) => {
                self.choice(self.text_and(" ", self.flatten(rest)), doc)
            }

            // group (x ‘Union‘ y) = group x ‘Union‘ y
            DocKind::Choice(a, b) => {
                let a_group = self.group(a);
                if a_group.ptr_eq(a) {
                    return doc;
                }
                self.choice(a_group, b)
            }
        }
    }

    pub fn flatten(&self, doc: DocRef<'a>) -> DocRef<'a> {
        match doc.kind {
            // flatten Nil = Nil
            DocKind::Nil => doc,

            // flatten (s ‘Text‘ x) = s ‘Text‘ flatten x
            DocKind::Text(string, rest) => {
                let rest_flat = self.flatten(rest);
                if rest_flat.ptr_eq(rest) {
                    return doc;
                }
                self.text_and(string, rest_flat)
            }

            // flatten (i ‘Line‘ x) = " " ‘Text‘ flatten x
            DocKind::Line(_, rest) => {
                self.text_and(" ", rest)
            }

            // flatten (x ‘Union‘ y) = flatten x
            DocKind::Choice(a, _) => {
                self.flatten(a)
            }
        }
    }

    #[inline(always)]
    pub fn best(&self, doc: DocRef<'a>, width: i32) -> DocRef<'a> {
        self.best_ex(doc, width, 0, 0)
    }

    pub fn best_ex(&self, doc: DocRef<'a>, width: i32, indent: i32, used: i32) -> DocRef<'a> {
        match doc.kind {
            // best w k Nil = Nil
            DocKind::Nil => doc,

            // best w k (s ‘Text‘ x) = s ‘Text‘ best w (k + length s) x
            DocKind::Text(string, rest) => {
                // approximate length as utf8 length.
                let len = string.len() as i32;
                let best_rest = self.best_ex(rest, width, indent, used + len);
                if best_rest.ptr_eq(rest) {
                    return doc;
                }
                self.text_and(string, best_rest)
            }

            // best w k (i ‘Line‘ x) = i ‘Line‘ best w i x
            DocKind::Line(delta, rest) => {
                let new_indent = indent + delta;
                let best_rest = self.best_ex(rest, width, new_indent, new_indent);
                if best_rest.ptr_eq(rest) {
                    return doc;
                }
                self.line(delta, best_rest)
            }

            // best w k (x ‘Union‘ y) = better w k (best w k x) (best w k y)
            DocKind::Choice(a, b) => {
                let best_a = self.best_ex(a, width, indent, used);
                if best_a.fits(width - used) {
                    return best_a;
                }
                self.best_ex(b, width, indent, used)
            }
        }
    }
}

