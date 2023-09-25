use core::marker::PhantomData;

use sti::arena::Arena;
use sti::keyed::KVec;
use sti::hash::{HashMapF, HashFn};
use sti::hash::fxhash::FxHasher32;


sti::define_key!(pub, u32, Atom, opt: OptAtom);

impl Atom { pub const NULL: Atom = Atom(0); }


pub struct StringTable<'a> {
    alloc: &'a Arena,
    strings: KVec<Atom, HashStr<'a>>,
    table: HashMapF<HashStr<'a>, Atom, HashStrHashFn>,

    // `HashStr` speeds up table resizing,
    // cause the hashes don't need to be recomputed,
    // which would touch all the string memory in hash (aka random) order.
    // lexing was about 12% faster for a 600 MiB test file.
    // though that's obviously not super realistic.
    // might not matter for normal inputs ¯\_(ツ)_/¯
}

impl<'a> StringTable<'a> {
    #[inline(always)]
    pub fn new(alloc: &'a Arena) -> Self {
        let mut result = Self {
            alloc,
            strings: KVec::new(),
            table: HashMapF::fnew(),
        };

        let init = &[
            (Atom::NULL, ""), (atoms::_hole, "_"),
            (atoms::max, "max"), (atoms::imax, "imax"), (atoms::reduce, "reduce"),
            (atoms::Nat, "Nat"), (atoms::zero, "zero"), (atoms::succ, "succ"),
            (atoms::rec, "rec"), (atoms::Eq, "Eq"), (atoms::refl, "refl"),
            (atoms::M, "M"), (atoms::m_zero, "m_zero"), (atoms::m_succ, "m_succ"),
            (atoms::n, "n"), (atoms::ih, "ih"), (atoms::mp, "mp"),
            (atoms::T, "T"), (atoms::a, "a"), (atoms::b, "b"),
            (atoms::m_refl, "m_refl"), (atoms::axiom, "axiom"), (atoms::r, "r"),
            (atoms::Add, "Add"), (atoms::add, "add"),
            (atoms::_mut, "mut"), (atoms::shr, "shr"), (atoms::_const, "const"),
            (atoms::Unit, "Unit"), (atoms::mk, "mk"),
            (atoms::Bool, "Bool"), (atoms::_false, "false"), (atoms::_true, "true"),
            (atoms::ite, "ite"),
            (atoms::ax_sorry, "ax_sorry"),
            (atoms::ax_uninit, "ax_uninit"),
            (atoms::ax_unreach, "ax_unreach"),
            (atoms::ax_error, "ax_error"),
            (atoms::jp, "jp"),
            (atoms::goal, "goal"), (atoms::sorry, "sorry"),
            (atoms::assumption, "assumption"), (atoms::rw, "rw"),
            (atoms::rewrite, "rewrite"), (atoms::by, "by"),
        ];

        for (atom, string) in init.iter().copied() {
            let a = result.insert(string);
            assert_eq!(a, atom);
        }

        return result;
    }

    #[inline(always)]
    pub fn insert(&mut self, str: &str) -> Atom {
        let q = HashStr::new(str);
        let hash = q.hash();

        // the borrow trait sucks. sorry not sorry.
        let q: HashStr<'a> = unsafe { core::mem::transmute(q) };

        *self.table.get_or_insert_with_key(&q, |_| {
            let str = self.alloc.alloc_str(str);
            let str = HashStr::with_hash(str, hash);
            (str, self.strings.push(str))
        })
    }
}

impl<'a> core::ops::Index<Atom> for StringTable<'a> {
    type Output = str;

    #[inline(always)]
    fn index(&self, atom: Atom) -> &Self::Output {
        self.strings[atom].as_str()
    }
}


#[allow(non_upper_case_globals)]
pub mod atoms {
    use super::Atom;

    pub const _hole:    Atom = Atom(1);
    pub const max:      Atom = Atom(2);
    pub const imax:     Atom = Atom(3);
    pub const reduce:   Atom = Atom(4);
    pub const Nat:      Atom = Atom(5);
    pub const zero:     Atom = Atom(6);
    pub const succ:     Atom = Atom(7);
    pub const rec:      Atom = Atom(8);
    pub const Eq:       Atom = Atom(9);
    pub const refl:     Atom = Atom(10);
    pub const M:        Atom = Atom(11);
    pub const m_zero:   Atom = Atom(12);
    pub const m_succ:   Atom = Atom(13);
    pub const n:        Atom = Atom(14);
    pub const ih:       Atom = Atom(15);
    pub const mp:       Atom = Atom(16);
    pub const T:        Atom = Atom(17);
    pub const a:        Atom = Atom(18);
    pub const b:        Atom = Atom(19);
    pub const m_refl:   Atom = Atom(20);
    pub const axiom:    Atom = Atom(21);
    pub const r:        Atom = Atom(22);
    pub const Add:      Atom = Atom(23);
    pub const add:      Atom = Atom(24);
    pub const _mut:     Atom = Atom(25);
    pub const shr:      Atom = Atom(26);
    pub const _const:   Atom = Atom(27);
    pub const Unit:     Atom = Atom(28);
    pub const mk:       Atom = Atom(29);
    pub const Bool:     Atom = Atom(30);
    pub const _false:   Atom = Atom(31);
    pub const _true:    Atom = Atom(32);
    pub const ite:      Atom = Atom(33);
    pub const ax_sorry:     Atom = Atom(34);
    pub const ax_uninit:    Atom = Atom(35);
    pub const ax_unreach:   Atom = Atom(36);
    pub const ax_error:     Atom = Atom(37);
    pub const jp:           Atom = Atom(38);
    pub const goal:         Atom = Atom(39);
    pub const sorry:        Atom = Atom(40);
    pub const assumption:   Atom = Atom(41);
    pub const rw:           Atom = Atom(42);
    pub const rewrite:      Atom = Atom(43);
    pub const by:           Atom = Atom(44);
}



#[derive(Clone, Copy)]
pub struct HashStr<'a> {
    ptr: *const u8,
    len: u32,
    hash: u32,
    phantom: PhantomData<&'a str>,
}

impl<'a> HashStr<'a> {
    pub fn new(str: &'a str) -> Self {
        let ptr = str.as_ptr();
        let len = str.len().try_into().unwrap();
        let hash = FxHasher32::hash_bytes(str.as_bytes());
        Self { ptr, len, hash, phantom: PhantomData }
    }

    #[inline(always)]
    pub fn with_hash(str: &'a str, hash: u32) -> Self {
        let ptr = str.as_ptr();
        let len = str.len().try_into().unwrap();
        Self { ptr, len, hash, phantom: PhantomData }
    }

    #[inline(always)]
    pub fn hash(&self) -> u32 { self.hash }

    #[inline(always)]
    pub fn as_str(&self) -> &'a str {
        unsafe {
            core::str::from_utf8_unchecked(
                core::slice::from_raw_parts(
                    self.ptr, self.len as usize))
        }
    }
}

impl<'a> core::ops::Deref for HashStr<'a> {
    type Target = str;

    #[inline(always)]
    fn deref(&self) -> &Self::Target { self.as_str() }
}

impl<'a> PartialEq for HashStr<'a> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash && self.as_str() == other.as_str()
    }
}
impl<'a> Eq for HashStr<'a> {}


struct HashStrHashFn;
impl<'a> HashFn<HashStr<'a>> for HashStrHashFn {
    type Seed = ();
    type Hash = u32;

    const DEFAULT_SEED: () = ();

    #[inline(always)]
    fn hash_with_seed(_: (), value: &HashStr<'a>) -> u32 {
        value.hash
    }
}

