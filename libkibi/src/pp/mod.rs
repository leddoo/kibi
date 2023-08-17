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
    Line,
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
}

impl<'a> core::fmt::Debug for Doc<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        self.kind.fmt(f)
    }
}

impl<'a> RDoc<'a> {
    fn fits(&self, width: i32) -> bool {
        if width < 0 {
            return false;
        }

        match self.kind {
            RDocKind::Nil => true,

            RDocKind::Text(string, rest) =>
                rest.fits(width - string.len() as i32),

            RDocKind::Line(_, _) => true,
        }
    }

    pub fn layout(&self, buffer: &mut String) {
        match self.kind {
            RDocKind::Nil => (),

            RDocKind::Text(string, rest) => {
                buffer.push_str(string);
                rest.layout(buffer);
            }

            RDocKind::Line(indent, rest) => {
                buffer.push('\n');
                for _ in 0..indent {
                    buffer.push(' ');
                }
                rest.layout(buffer)
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
    pub fn new(arena: &'a GrowingArena) -> Self {
        Self { arena }
    }


    #[inline(always)]
    pub fn nil(&self) -> DocRef<'a> {
        &Doc { kind: DocKind::Nil }
    }

    #[inline(always)]
    pub fn line(&self) -> DocRef<'a> {
        self.arena.alloc_new(Doc { kind: DocKind::Line })
    }

    #[inline(always)]
    pub fn text(&self, string: &'a str) -> DocRef<'a> {
        self.arena.alloc_new(Doc { kind: DocKind::Text(string) })
    }

    #[inline(always)]
    pub fn space(&self) -> DocRef<'a> {
        &Doc { kind: DocKind::Text(" ") }
    }

    #[inline(always)]
    pub fn indent(&self, delta: i32, rest: DocRef<'a>) -> DocRef<'a> {
        self.arena.alloc_new(Doc { kind: DocKind::Indent(delta, rest) })
    }

    #[inline(always)]
    pub fn cat(&self, a: DocRef<'a>, b: DocRef<'a>) -> DocRef<'a> {
        self.arena.alloc_new(Doc { kind: DocKind::Cat(a, b) })
    }

    #[inline(always)]
    pub fn cats(&self, docs: &[DocRef<'a>]) -> DocRef<'a> {
        if docs.len() == 0 {
            return self.nil();
        }

        let mut result = docs[0];
        for doc in &docs[1..] {
            result = self.cat(result, doc);
        }
        result
    }


    #[inline(always)]
    fn choice(&self, a: DocRef<'a>, b: DocRef<'a>) -> DocRef<'a> {
        self.arena.alloc_new(Doc { kind: DocKind::Choice(a, b) })
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
            DocKind::Line => self.space(),

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
        self.arena.alloc_new(RDoc { kind: RDocKind::Line(indent, rest) })
    }

    #[inline(always)]
    pub fn rtext(&self, string: &'a str, rest: RDocRef<'a>) -> RDocRef<'a> {
        self.arena.alloc_new(RDoc { kind: RDocKind::Text(string, rest) })
    }


    #[inline(always)]
    pub fn render(&self, doc: DocRef<'a>, width: i32) -> RDocRef<'a> {
        self.render_ex(width, 0, &mut vec![(0, doc)])
    }

    pub fn render_ex(&self, width: i32, used: i32, z: &mut Vec<(i32, DocRef<'a>)>) -> RDocRef<'a> {
        let Some((indent, doc)) = z.pop() else {
            // be w k [] = Nil
            return self.rnil();
        };

        match doc.kind {
            // be w k ((i,NIL):z) = be w k z
            DocKind::Nil => self.render_ex(width, used, z),

            // be w k ((i,LINE):z) = i ‘Line‘ be w i z
            DocKind::Line => {
                let rest = self.render_ex(width, indent, z);
                self.rline(indent, rest)
            }

            // be w k ((i,TEXT s):z) = s ‘Text‘ be w (k + length s) z
            DocKind::Text(string) => {
                let len = string.len() as i32;
                let rest = self.render_ex(width, used + len, z);
                self.rtext(string, rest)
            }

            // be w k ((i,NEST j x):z) = be w k ((i+j,x):z)
            DocKind::Indent(delta, rest) => {
                z.push((indent + delta, rest));
                self.render_ex(width, used, z)
            }

            // be w k ((i,x :<> y):z) = be w k ((i,x):(i,y):z)
            DocKind::Cat(a, b) => {
                z.push((indent, b));
                z.push((indent, a));
                self.render_ex(width, used, z)
            }

            // be w k ((i,x :<|> y):z) = better w k (be w k ((i,x):z)) (be w k ((i,y):z))
            DocKind::Choice(a, b) => {
                let mut za = z.clone();
                za.push((indent, a));
                let best_a = self.render_ex(width, used, &mut za);
                if best_a.fits(width - used) {
                    return best_a;
                }

                z.push((indent, b));
                self.render_ex(width, used, z)
            }
        }
    }
}

