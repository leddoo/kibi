use core::marker::PhantomData;

pub trait Key: Copy {
    fn from_usize(value: usize) -> Self;
    fn usize(self) -> usize;
}


pub struct IndexVec<K: Key, V> {
    values: Vec<V>,
    unused: PhantomData<K>,
}

impl<K: Key, V> IndexVec<K, V> {
    #[inline(always)]
    pub fn new() -> Self {
        Self { values: vec![], unused: PhantomData }
    }

    #[inline(always)]
    pub fn with_capacity(cap: usize) -> Self {
        Self { values: Vec::with_capacity(cap), unused: PhantomData }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    #[inline(always)]
    pub fn push(&mut self, value: V) {
        self.values.push(value);
    }

    #[inline(always)]
    pub fn get(&self, key: K) -> Option<&V> {
        self.values.get(key.usize())
    }

    #[inline(always)]
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.values.get_mut(key.usize())
    }

    #[inline(always)]
    pub fn retain<F: FnMut(&V) -> bool>(&mut self, f: F) {
        self.values.retain(f)
    }

    #[inline(always)]
    pub fn retain_mut<F: FnMut(&mut V) -> bool>(&mut self, f: F) {
        self.values.retain_mut(f)
    }

    #[inline(always)]
    pub fn iter(&self) -> core::slice::Iter<V> { self.values.iter() }

    #[inline(always)]
    pub fn iter_mut(&mut self) -> core::slice::IterMut<V> { self.values.iter_mut() }

    #[inline(always)]
    pub fn inner(&self) -> &Vec<V> { &self.values }

    #[inline(always)]
    pub fn inner_mut(&mut self) -> &mut Vec<V> { &mut self.values }
}


impl<K: Key, V> core::ops::Index<K> for IndexVec<K, V> {
    type Output = V;

    #[inline(always)]
    fn index(&self, index: K) -> &Self::Output {
        &self.values[index.usize()]
    }
}

impl<K: Key, V> core::ops::IndexMut<K> for IndexVec<K, V> {
    #[inline(always)]
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.values[index.usize()]
    }
}


impl<K: Key, V: Clone> Clone for IndexVec<K, V> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self { values: self.values.clone(), unused: PhantomData }
    }
}

impl<K: Key, V: core::fmt::Debug> core::fmt::Debug for IndexVec<K, V> {
    #[inline(always)]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.values.fmt(f)
    }
}

impl<K: Key, V: PartialEq> PartialEq for IndexVec<K, V> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.values.eq(&other.values)
    }
}


impl<K: Key, V> From<Vec<V>> for IndexVec<K, V> {
    #[inline(always)]
    fn from(values: Vec<V>) -> Self {
        Self { values, unused: PhantomData }
    }
}


impl<'a, K: Key, V> IntoIterator for &'a IndexVec<K, V> {
    type Item = &'a V;
    type IntoIter = core::slice::Iter<'a, V>;
    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.values.iter()
    }
}

impl<'a, K: Key, V> IntoIterator for &'a mut IndexVec<K, V> {
    type Item = &'a mut V;
    type IntoIter = core::slice::IterMut<'a, V>;
    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.values.iter_mut()
    }
}

impl<K: Key, V> IntoIterator for IndexVec<K, V> {
    type Item = V;
    type IntoIter = <Vec<V> as IntoIterator>::IntoIter;
    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.values.into_iter()
    }
}

impl<K: Key, V> FromIterator<V> for IndexVec<K, V> {
    #[inline(always)]
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        Self { values: Vec::from_iter(iter), unused: PhantomData }
    }
}


macro_rules! index_vec {
    () => (
        IndexVec::from(vec![])
    );
    ($elem:expr; $n:expr) => (
        IndexVec::from(vec![$elem; $n])
    );
    ($($x:expr),+ $(,)?) => (
        IndexVec::from(vec![$($x),+])
    );
}
pub(crate) use index_vec;

