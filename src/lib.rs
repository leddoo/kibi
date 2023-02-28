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
                pub const fn usize(self) -> usize { self.0 as usize }

                #[inline(always)]
                pub fn from_usize(index: usize) -> $name {
                    assert!(index < u32::MAX as usize / 2);
                    $name(index as u32)
                }
            }
        };
    }
    pub(crate) use define_id_basic;


    macro_rules! define_id_optional {
        ($name: ident, $opt_name: ident) => {
            #[derive(Clone, Copy, PartialEq)]
            #[repr(transparent)]
            pub struct $opt_name(u32);

            impl $name {
                #[inline(always)]
                pub const fn some(self) -> $opt_name { $opt_name(self.0) }
            }

            impl $opt_name {
                pub const NONE: $opt_name = $opt_name(u32::MAX);

                #[inline(always)]
                pub fn to_option(self) -> Option<$name> {
                    (self != Self::NONE).then_some($name(self.0))
                }

                #[inline(always)]
                pub fn unwrap(self) -> $name {
                    self.to_option().unwrap()
                }
            }

            impl From<Option<$name>> for $opt_name {
                #[inline(always)]
                fn from(value: Option<$name>) -> Self {
                    if let Some(id) = value { id.some() }
                    else { $opt_name::NONE }
                }
            }

            impl From<$opt_name> for Option<$name> {
                #[inline(always)]
                fn from(value: $opt_name) -> Self {
                    value.to_option()
                }
            }

            impl core::fmt::Debug for $opt_name {
                #[inline]
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    self.to_option().fmt(f)
                }
            }
        };
    }
    pub(crate) use define_id_optional;


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
            crate::macros::define_id_optional!($name, $opt_name);
        };

        ($name: ident, $fmt: expr) => {
            crate::macros::define_id_basic!($name);
            crate::macros::define_id_display!($name, $fmt);
        };

        ($name: ident, $opt_name: ident, $fmt: expr) => {
            crate::macros::define_id_basic!($name);
            crate::macros::define_id_optional!($name, $opt_name);
            crate::macros::define_id_display!($name, $fmt);
        };
    }
    pub(crate) use define_id;
}

