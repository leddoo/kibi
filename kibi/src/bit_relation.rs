use core::ptr::NonNull;
use core::marker::PhantomData;

use sti::traits::CopyIt;
use sti::arena::Arena;
use sti::keyed::Key;


pub struct BitRelationImpl<'a, K: Key, const MUT: bool> {
    // indexed [K1][K2].
    // invariant: bit_rows[*][self.width..] = 0
    ptr: NonNull<u32>,
    len: usize,
    phantom: PhantomData<(&'a u32, fn(K) -> K)>,
}

pub type BitRelation<'a, K>    = BitRelationImpl<'a, K, false>;
pub type BitRelationMut<'a, K> = BitRelationImpl<'a, K, true>;


impl<'a, K: Key> BitRelationMut<'a, K> {
    pub fn new(alloc: &'a Arena, len: usize) -> BitRelationMut<'a, K> {
        assert!(K::from_usize(len).is_some());
        assert!(K::from_usize(len).is_some());

        let stride = (len + 31) / 32;
        let size = stride.checked_mul(len).unwrap();
        let ptr = sti::alloc::alloc_array(alloc, size).unwrap();
        unsafe { core::ptr::write_bytes(ptr.as_ptr(), 0, size) };
        BitRelationMut { ptr, len, phantom: PhantomData }
    }

    #[track_caller]
    #[inline(always)]
    pub fn insert(&mut self, k1: K, k2: K) {
        let k1 = k1.usize();
        let k2 = k2.usize();
        assert!(k1 < self.len);
        assert!(k2 < self.len);

        let stride = (self.len + 31) / 32;
        let col = k2 / 32;
        let bit = k2 % 32;
        unsafe { *self.ptr.as_ptr().add(k1*stride + col) |= 1 << bit; }
    }

    #[track_caller]
    #[inline(always)]
    pub fn remove(&mut self, k1: K, k2: K) {
        let k1 = k1.usize();
        let k2 = k2.usize();
        assert!(k1 < self.len);
        assert!(k2 < self.len);

        let stride = (self.len + 31) / 32;
        let col = k2 / 32;
        let bit = k2 % 32;
        unsafe { *self.ptr.as_ptr().add(k1*stride + col) &= !(1 << bit); }
    }

    #[track_caller]
    #[inline(always)]
    pub fn union_rows(&mut self, dst: K, src: K) -> bool {
        let dst = dst.usize();
        let src = src.usize();
        assert!(dst < self.len);
        assert!(src < self.len);
        if dst == src {
            return false;
        }

        let stride = (self.len + 31) / 32;
        let dst_row = dst*stride;
        let src_row = src*stride;

        let mut changed = false;
        for i in 0..stride { unsafe {
            let dst = self.ptr.as_ptr().add(dst_row + i);
            let src = self.ptr.as_ptr().add(src_row + i);
            let old = *dst;
            let new = *dst | *src;
            changed |= new != old;
            *dst = new;
        }}
        return changed;
    }
}

impl<'a, K: Key, const MUT: bool> BitRelationImpl<'a, K, MUT> {
    #[inline(always)]
    pub fn len(&self) -> usize { self.len }

    #[inline(always)]
    pub fn borrow<'this>(&'this self) -> BitRelation<'this, K> {
        BitRelation { ptr: self.ptr, len: self.len, phantom: PhantomData }
    }

    #[track_caller]
    #[inline(always)]
    pub fn has(&self, k1: K, k2: K) -> bool {
        let k1 = k1.usize();
        let k2 = k2.usize();
        assert!(k1 < self.len);
        assert!(k2 < self.len);

        let stride = (self.len + 31) / 32;
        let col = k2 / 32;
        let bit = k2 % 32;
        unsafe { (*self.ptr.as_ptr().add(k1*stride + col) & (1 << bit)) != 0}
    }


    pub fn transitive_from(alloc: &'a Arena, len: usize, related: &[(K, K)]) -> Self {
        let mut r = BitRelationMut::new(alloc, len);
        for (k1, k2) in related.copy_it() {
            r.insert(k1, k2);
        }

        let mut changed = true;
        while changed {
            changed = false;
            for (k1, k2) in related.copy_it() {
                // make k1 related to anything k2 is related to.
                changed |= r.union_rows(k1, k2);
            }
        }
        return Self { ptr: r.ptr, len: r.len, phantom: PhantomData };
    }
}


impl<'a, K: Key> Into<BitRelation<'a, K>> for BitRelationMut<'a, K> {
    #[inline(always)]
    fn into(self) -> BitRelation<'a, K> {
        BitRelation { ptr: self.ptr, len: self.len, phantom: PhantomData }
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitrelation_basic() {
        sti::define_key!(u32, K);
        fn k(i: usize) -> K { K::from_usize(i).unwrap() }

        let alloc = Arena::new();

        let mut a = BitRelationMut::new(&alloc, 33);
        for i in 0..a.len() {
            for j in 0..a.len() {
                assert_eq!(a.has(k(i), k(j)), false);
            }
        }

        assert_eq!(a.has(k(2), k(31)), false);
        a.insert(k(2), k(31));
        assert_eq!(a.has(k(2), k(31)), true);
        a.remove(k(2), k(31));
        assert_eq!(a.has(k(2), k(31)), false);

        a.insert(k(2), k(31));
        a.insert(k(2), k(32));
        a.insert(k(3), k(31));
        for i in 0..a.len() {
            for j in 0..a.len() {
                if ![(2, 31), (2, 32), (3, 31)].contains(&(i, j)) {
                    assert_eq!(a.has(k(i), k(j)), false);
                }
                else {
                    assert_eq!(a.has(k(i), k(j)), true);
                }
            }
        }
    }

    #[test]
    fn bitrelation_transitive() {
        sti::define_key!(u32, K);
        fn k(i: usize) -> K { K::from_usize(i).unwrap() }

        let alloc = Arena::new();

        let r = BitRelation::transitive_from(&alloc, 33, &[
            (k(1), k(1)),
            (k(1), k(32)),
            (k(32), k(5)),
            (k(5), k(7)),
            (k(3), k(5)),
            (k(8), k(9)),
            (k(10), k(10)),
        ]);

        let full_relation = &[
            (1, 1), (1, 32), (1, 5), (1, 7),
            (32, 5), (32, 7),
            (5, 7),
            (3, 5), (3, 7),
            (8, 9),
            (10, 10),
        ];

        for i in 0..r.len() {
            for j in 0..r.len() {
                assert_eq!(r.has(k(i), k(j)), full_relation.contains(&(i, j)));
            }
        }
    }
}

