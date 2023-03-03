pub mod packed_option;
pub mod index_vec;
pub mod compiler;
pub mod bytecode;
pub mod value;
pub mod vm;

pub use bytecode::*;
pub use value::*;
pub use vm::*;



mod macros {
    macro_rules! define_id_basic {
        ($name: ident) => {
            #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
            #[repr(transparent)]
            pub struct $name(u32);

            impl $name {
                #[inline(always)]
                pub fn new_unck(value: u32) -> Self { Self(value) }

                #[inline(always)]
                pub const fn value(self) -> u32 { self.0 }

                #[inline(always)]
                pub fn from_usize(value: usize) -> Self {
                    debug_assert!(value < u32::MAX as usize / 2);
                    $name(value as u32)
                }

                #[inline(always)]
                pub fn usize(self) -> usize {
                    self.0 as usize
                }

                #[inline(always)]
                pub fn some(self) -> crate::packed_option::PackedOption<Self> {
                    crate::packed_option::Reserved::some(self)
                }
            }

            impl crate::packed_option::Reserved for $name {
                const RESERVED: Self = Self(u32::MAX);
            }

            impl crate::index_vec::Key for $name {
                #[inline(always)]
                fn from_usize(value: usize) -> Self {
                    Self::from_usize(value)
                }

                #[inline(always)]
                fn usize(self) -> usize {
                    self.0 as usize
                }
            }
        };
    }
    pub(crate) use define_id_basic;

    macro_rules! define_id_opt {
        ($name: ident, $opt_name: ident) => {
            pub type $opt_name = crate::packed_option::PackedOption<$name>;
        };
    }
    pub(crate) use define_id_opt;


    macro_rules! define_id_display {
        ($name: ident, $fmt: expr) => {
            impl core::fmt::Display for $name {
                #[inline]
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    write!(f, $fmt, self.0)
                }
            }
        };
    }
    pub(crate) use define_id_display;


    macro_rules! define_id {
        ($name: ident) => {
            crate::macros::define_id_basic!($name);
        };

        ($name: ident, $opt_name: ident) => {
            crate::macros::define_id_basic!($name);
            crate::macros::define_id_opt!($name, $opt_name);
        };

        ($name: ident, $fmt: expr) => {
            crate::macros::define_id_basic!($name);
            crate::macros::define_id_display!($name, $fmt);
        };

        ($name: ident, $opt_name: ident, $fmt: expr) => {
            crate::macros::define_id_basic!($name);
            crate::macros::define_id_opt!($name, $opt_name);
            crate::macros::define_id_display!($name, $fmt);
        };
    }
    pub(crate) use define_id;
}

