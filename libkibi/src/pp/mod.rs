use sti::growing_arena::GrowingArena;


// impl of "A prettier printer" by Philip Wadler
// https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf


pub struct PP<'a> {
    pub alloc: &'a GrowingArena,
}


pub type DocRef<'a> = &'a Doc<'a>;

pub struct Doc<'a> {
    pub kind: DocKind<'a>,
}

#[derive(Debug)]
pub enum DocKind<'a> {
    Nil,
    Line(bool), // flatten as space.
    Text(&'a str),
    Indent(i32,        DocRef<'a>),
    Cat   (DocRef<'a>, DocRef<'a>),
    Choice(DocRef<'a>, DocRef<'a>),
}



pub type RDocRef<'a> = &'a RDoc<'a>;

pub struct RDoc<'a> {
    pub kind: RDocKind<'a>,
}

#[derive(Debug)]
pub enum RDocKind<'a> {
    Nil,
    Text(&'a str, RDocRef<'a>),
    Line(i32,     RDocRef<'a>),
}


impl<'a> Doc<'a> {
    #[inline(always)]
    pub fn ptr_eq(&self, other: &Doc) -> bool {
        core::ptr::eq(self, other)
    }

    #[inline(always)]
    pub fn is_nil(&self) -> bool {
        matches!(self.kind, DocKind::Nil)
    }
}

impl<'a> core::fmt::Debug for Doc<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        self.kind.fmt(f)
    }
}

impl<'a> RDoc<'a> {
    pub fn fits(&self, mut width: i32) -> bool {
        let mut at = self;
        loop {
            if width < 0 { return false }

            match at.kind {
                RDocKind::Nil => return true,

                RDocKind::Text(string, rest) => {
                    width -= string.len() as i32;
                    at = rest;
                }

                RDocKind::Line(_, _) => return true,
            }
        }
    }

    pub fn layout_string(&self, buffer: &mut String) {
        let mut at = self;
        loop {
            match at.kind {
                RDocKind::Nil => return,

                RDocKind::Text(string, rest) => {
                    buffer.push_str(string);
                    at = rest;
                }

                RDocKind::Line(indent, rest) => {
                    buffer.push('\n');
                    buffer.reserve(indent as usize);
                    for _ in 0..indent {
                        buffer.push(' ');
                    }
                    at = rest;
                }
            }
        }
    }
}

impl<'a> core::fmt::Debug for RDoc<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        self.kind.fmt(f)
    }
}


impl<'a> PP<'a> {
    #[inline(always)]
    pub fn new(alloc: &'a GrowingArena) -> Self {
        Self { alloc }
    }


    #[inline(always)]
    pub fn alloc_str(&self, string: &str) -> &'a str {
        // @temp.
        use sti::alloc::*;
        unsafe {
            let ptr = self.alloc.alloc(Layout::for_value(string)).unwrap();
            core::ptr::copy_nonoverlapping(string.as_ptr(), ptr.as_ptr(), string.len());
            core::str::from_utf8_unchecked(
                core::slice::from_raw_parts(ptr.as_ptr(), string.len()))
        }
    }


    #[inline(always)]
    pub fn nil(&self) -> DocRef<'a> {
        &Doc { kind: DocKind::Nil }
    }

    #[inline(always)]
    pub fn line_or_sp(&self) -> DocRef<'a> {
        &Doc { kind: DocKind::Line(true) }
    }

    #[inline(always)]
    pub fn line(&self) -> DocRef<'a> {
        &Doc { kind: DocKind::Line(false) }
    }

    #[inline(always)]
    pub fn text(&self, string: &'a str) -> DocRef<'a> {
        self.alloc.alloc_new(Doc { kind: DocKind::Text(string) })
    }

    #[inline(always)]
    pub fn space(&self) -> DocRef<'a> {
        &Doc { kind: DocKind::Text(" ") }
    }

    #[inline(always)]
    pub fn indent(&self, delta: i32, rest: DocRef<'a>) -> DocRef<'a> {
        self.alloc.alloc_new(Doc { kind: DocKind::Indent(delta, rest) })
    }

    #[inline(always)]
    pub fn cat(&self, a: DocRef<'a>, b: DocRef<'a>) -> DocRef<'a> {
        self.alloc.alloc_new(Doc { kind: DocKind::Cat(a, b) })
    }

    #[inline(always)]
    pub fn cats(&self, docs: &[DocRef<'a>]) -> DocRef<'a> {
        if docs.len() == 0 {
            return self.nil();
        }

        let mut result = docs[0];
        for doc in &docs[1..] {
            if !doc.is_nil() {
                result = self.cat(result, doc);
            }
        }
        result
    }


    #[inline(always)]
    fn choice(&self, a: DocRef<'a>, b: DocRef<'a>) -> DocRef<'a> {
        self.alloc.alloc_new(Doc { kind: DocKind::Choice(a, b) })
    }

    #[inline(always)]
    pub fn group(&self, doc: DocRef<'a>) -> DocRef<'a> {
        // group x = flatten x :<|> x
        self.choice(self.flatten(doc), doc)
    }

    pub fn flatten(&self, doc: DocRef<'a>) -> DocRef<'a> {
        match doc.kind {
            // flatten NIL = NIL
            DocKind::Nil => doc,

            // flatten LINE = TEXT " "
            DocKind::Line(space) => {
                if space { self.space() }
                else     { self.nil()   }
            }

            // flatten (TEXT s) = TEXT s
            DocKind::Text(_) => doc,

            // flatten (NEST i x) = flatten x
            DocKind::Indent(_, rest) => self.flatten(rest),

            // flatten (x :<> y) = flatten x :<> flatten y
            DocKind::Cat(a, b) => {
                let flat_a = self.flatten(a);
                let flat_b = self.flatten(b);
                if flat_a.ptr_eq(a) && flat_b.ptr_eq(b) {
                    return doc;
                }
                self.cat(flat_a, flat_b)
            }

            // flatten (x :<|> y) = flatten x
            DocKind::Choice(a, _) => self.flatten(a),
        }
    }


    #[inline(always)]
    pub fn rnil(&self) -> RDocRef<'a> {
        &RDoc { kind: RDocKind::Nil }
    }

    #[inline(always)]
    pub fn rline(&self, indent: i32, rest: RDocRef<'a>) -> RDocRef<'a> {
        self.alloc.alloc_new(RDoc { kind: RDocKind::Line(indent, rest) })
    }

    #[inline(always)]
    pub fn rtext(&self, string: &'a str, rest: RDocRef<'a>) -> RDocRef<'a> {
        self.alloc.alloc_new(RDoc { kind: RDocKind::Text(string, rest) })
    }


    #[inline(always)]
    pub fn render(&self, doc: DocRef<'a>, width: i32) -> RDocRef<'a> {
        self.render_ex(width, 0, Some(&RenderList::new(0, doc, None)))
    }
}

#[derive(Clone, Copy)]
struct RenderList<'l, 'a> {
    indent: i32,
    doc: DocRef<'a>,
    tail: Option<&'l RenderList<'l, 'a>>,
}

impl<'l, 'a> RenderList<'l, 'a> {
    #[inline(always)]
    fn new(indent: i32, doc: DocRef<'a>, tail: Option<&'l RenderList<'l, 'a>>) -> Self {
        Self { indent, doc, tail }
    }
}

impl<'a> PP<'a> {
    fn render_ex<'l>(&self, width: i32, used: i32, list: Option<&'l RenderList<'l, 'a>>) -> RDocRef<'a> {
        let Some(RenderList { indent, doc, tail }) = list.copied() else {
            // be w k [] = Nil
            return self.rnil();
        };

        match doc.kind {
            // be w k ((i,NIL):z) = be w k z
            DocKind::Nil => self.render_ex(width, used, tail),

            // be w k ((i,LINE):z) = i ‘Line‘ be w i z
            DocKind::Line(_) => {
                let tail = self.render_ex(width, indent, tail);
                self.rline(indent, tail)
            }

            // be w k ((i,TEXT s):z) = s ‘Text‘ be w (k + length s) z
            DocKind::Text(string) => {
                let len = string.len() as i32;
                let rest = self.render_ex(width, used + len, tail);
                self.rtext(string, rest)
            }

            // be w k ((i,NEST j x):z) = be w k ((i+j,x):z)
            DocKind::Indent(delta, rest) => {
                let list = RenderList::new(indent + delta, rest, tail);
                self.render_ex(width, used, Some(&list))
            }

            // be w k ((i,x :<> y):z) = be w k ((i,x):(i,y):z)
            DocKind::Cat(a, b) => {
                let list = RenderList::new(indent, b, tail);
                let list = RenderList::new(indent, a, Some(&list));
                self.render_ex(width, used, Some(&list))
            }

            // be w k ((i,x :<|> y):z) = better w k (be w k ((i,x):z)) (be w k ((i,y):z))
            DocKind::Choice(a, b) => {
                let list_a = RenderList::new(indent, a, tail);
                let best_a = self.render_ex(width, used, Some(&list_a));
                if best_a.fits(width - used) {
                    return best_a;
                }

                let list_b = RenderList::new(indent, b, tail);
                self.render_ex(width, used, Some(&list_b))
            }
        }
    }
}

