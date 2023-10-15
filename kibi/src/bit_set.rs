use core::ptr::NonNull;
use core::marker::PhantomData;

use sti::arena::Arena;
use sti::keyed::Key;


pub struct BitSetImpl<'a, K: Key, const MUT: bool> {
    // invariant: bits[self.len..] = 0
    ptr: NonNull<u32>,
    len: usize,
    phantom: PhantomData<(&'a u32, fn(K) -> K)>,
}

pub type BitSet<'a, K>    = BitSetImpl<'a, K, false>;
pub type BitSetMut<'a, K> = BitSetImpl<'a, K, true>;


impl<'a, K: Key> BitSet<'a, K> {
    #[inline(always)]
    pub fn from_iter<I: Iterator<Item = K>>(alloc: &'a Arena, len: usize, iter: I) -> BitSet<'a, K> {
        BitSetMut::from_iter(alloc, len, iter).into()
    }
}

impl<'a, K: Key> BitSetMut<'a, K> {
    pub fn new(alloc: &'a Arena, len: usize) -> BitSetMut<'a, K> {
        assert!(K::from_usize(len).is_some());

        let size = (len + 31) / 32;
        let ptr = sti::alloc::alloc_array(alloc, size).unwrap();
        unsafe { core::ptr::write_bytes(ptr.as_ptr(), 0, size) };
        BitSetMut { ptr, len, phantom: PhantomData }
    }

    #[inline]
    pub fn from_iter<I: Iterator<Item = K>>(alloc: &'a Arena, len: usize, iter: I) -> BitSetMut<'a, K> {
        let mut this = Self::new(alloc, len);
        for k in iter {
            this.insert(k);
        }
        return this;
    }

    #[track_caller]
    #[inline(always)]
    pub fn clear(&mut self) {
        let size = (self.len + 31) / 32;
        unsafe { core::ptr::write_bytes(self.ptr.as_ptr(), 0, size) };
    }

    #[track_caller]
    #[inline(always)]
    pub fn insert(&mut self, k: K) {
        let k = k.usize();
        assert!(k < self.len);

        let idx = k / 32;
        let bit = k % 32;
        unsafe { *self.ptr.as_ptr().add(idx) |= 1 << bit; }
    }

    #[track_caller]
    #[inline(always)]
    pub fn remove(&mut self, k: K) {
        let k = k.usize();
        assert!(k < self.len);

        let idx = k / 32;
        let bit = k % 32;
        unsafe { *self.ptr.as_ptr().add(idx) &= !(1 << bit); }
    }

    #[track_caller]
    #[inline(always)]
    pub fn assign(&mut self, other: BitSet<K>) {
        assert_eq!(self.len, other.len);
        let size = (self.len + 31) / 32;
        unsafe {
            core::ptr::copy_nonoverlapping(
                other.ptr.as_ptr(),
                self.ptr.as_ptr(),
                size);
        }
    }

    #[track_caller]
    #[inline(always)]
    pub fn union(&mut self, other: BitSet<K>) {
        assert_eq!(self.len, other.len);
        let size = (self.len + 31) / 32;
        for i in 0..size { unsafe {
            *self.ptr.as_ptr().add(i) |= *other.ptr.as_ptr().add(i)
        }}
    }

    /// (a - b) U c
    #[track_caller]
    #[inline(always)]
    pub fn diff_union(&mut self, a: BitSet<K>, b: BitSet<K>, c: BitSet<K>) -> bool {
        assert_eq!(self.len, a.len);
        assert_eq!(self.len, b.len);
        assert_eq!(self.len, c.len);
        let size = (self.len + 31) / 32;

        let mut changed = false;
        for i in 0..size { unsafe {
            let dst = self.ptr.as_ptr().add(i);
            let old = *dst;
            let new =
                  *a.ptr.as_ptr().add(i) & !*b.ptr.as_ptr().add(i)
                | *c.ptr.as_ptr().add(i);
            changed |= new != old;
            *dst = new;
        }}
        return changed;
    }
}

impl<'a, K: Key, const MUT: bool> BitSetImpl<'a, K, MUT> {
    #[inline(always)]
    pub fn borrow<'this>(&'this self) -> BitSet<'this, K> {
        BitSet { ptr: self.ptr, len: self.len, phantom: PhantomData }
    }

    #[track_caller]
    #[inline(always)]
    pub fn has(&self, k: K) -> bool {
        let k = k.usize();
        assert!(k < self.len);

        let idx = k / 32;
        let bit = k % 32;
        unsafe { (*self.ptr.as_ptr().add(idx) & (1 << bit)) != 0}
    }

    #[track_caller]
    #[inline(always)]
    pub fn iter(&self) -> BitSetIter<K> {
        let size = (self.len + 31) / 32;
        BitSetIter { set: self.borrow(), size, idx: 0, buffer: 0 }
    }
}


impl<'a, K: Key + core::fmt::Debug, const MUT: bool> core::fmt::Debug for BitSetImpl<'a, K, MUT> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<'a, K: Key + core::fmt::Display, const MUT: bool> core::fmt::Display for BitSetImpl<'a, K, MUT> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{{")?;
        for (i, k) in self.iter().enumerate() {
            if i != 0 { write!(f, ", ")? }
            write!(f, "{k}")?;
        }
        write!(f, "}}")
    }
}

impl<'a, K: Key, const MUT: bool> Default for BitSetImpl<'a, K, MUT> {
    #[inline(always)]
    fn default() -> Self {
        Self { ptr: NonNull::dangling(), len: 0, phantom: PhantomData }
    }
}

impl<'a, K: Key> Into<BitSet<'a, K>> for BitSetMut<'a, K> {
    #[inline(always)]
    fn into(self) -> BitSet<'a, K> {
        BitSet { ptr: self.ptr, len: self.len, phantom: PhantomData }
    }
}

impl<'a, K: Key> Clone for BitSet<'a, K> {
    #[inline(always)]
    fn clone(&self) -> Self { *self }
}

impl<'a, K: Key> Copy for BitSet<'a, K> {}


#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct BitSetIter<'a, K: Key> {
    set: BitSet<'a, K>,
    size: usize,
    idx:  usize,
    buffer: u32,
}

impl<'a, K: Key> Iterator for BitSetIter<'a, K> {
    type Item = K;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        while self.buffer == 0 {
            if self.idx >= self.size {
                return None;
            }

            self.buffer = unsafe { self.set.ptr.as_ptr().add(self.idx).read() };
            self.idx += 1;
        }

        let bit = self.buffer.trailing_zeros();
        self.buffer &= self.buffer - 1;

        Some(K::from_usize_unck(32*(self.idx - 1) + bit as usize))
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.set.len - self.idx;
        (0, Some(len))
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitset_basic() {
        sti::define_key!(u32, K);
        fn k(i: usize) -> K { K::from_usize(i).unwrap() }

        let alloc = Arena::new();

        let mut a = BitSetMut::new(&alloc, 72);
        for i in 0..72 {
            assert_eq!(a.has(k(i)), false);
        }
        assert_eq!(a.iter().next(), None);

        assert_eq!(a.has(k(31)), false);
        a.insert(k(31));
        assert_eq!(a.has(k(31)), true);
        a.remove(k(31));
        assert_eq!(a.has(k(31)), false);

        a.insert(k(31));
        a.insert(k(32));
        a.insert(k(71));
        assert_eq!(a.has(k(31)), true);
        assert_eq!(a.has(k(32)), true);
        assert_eq!(a.has(k(71)), true);

        let mut it = a.iter();
        assert_eq!(it.next(), Some(k(31)));
        assert_eq!(it.next(), Some(k(32)));
        assert_eq!(it.next(), Some(k(71)));
        assert_eq!(it.next(), None);
    }
}

