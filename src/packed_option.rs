
pub trait Reserved: PartialEq + Sized + Copy + PartialEq + core::fmt::Debug {
    const RESERVED: Self;

    fn some(self) -> PackedOption<Self> {
        debug_assert_ne!(self, Self::RESERVED);
        PackedOption { value: self }
    }
}

#[derive(Clone, Copy, PartialEq)]
#[repr(transparent)]
pub struct PackedOption<T: Reserved> {
    value: T
}

impl<T: Reserved> PackedOption<T> {
    pub const NONE: PackedOption<T> = PackedOption { value: Reserved::RESERVED };

    #[inline(always)]
    pub fn is_none(&self) -> bool {
        self.value == T::RESERVED
    }

    #[inline(always)]
    pub fn is_some(&self) -> bool {
        self.value != T::RESERVED
    }

    #[inline(always)]
    pub fn to_option(self) -> Option<T> {
        self.is_some().then_some(self.value)
    }

    #[inline(always)]
    pub fn unwrap(self) -> T {
        self.to_option().unwrap()
    }

    #[inline(always)]
    pub fn unwrap_unck(self) -> T {
        self.value
    }
}


impl<T: Reserved> From<Option<T>> for PackedOption<T> {
    #[inline(always)]
    fn from(value: Option<T>) -> Self {
        if let Some(value) = value {
            PackedOption { value }
        }
        else {
            PackedOption { value: T::RESERVED }
        }
    }
}

impl<T: Reserved> Into<Option<T>> for PackedOption<T> {
    #[inline(always)]
    fn into(self) -> Option<T> {
        self.to_option()
    }
}


impl<T: Reserved> core::fmt::Debug for PackedOption<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_some() {
            write!(f, "Some({:?})", self.value)
        }
        else { write!(f, "None") }
    }
}


