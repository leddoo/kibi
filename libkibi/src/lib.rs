pub use sti;


pub mod pp;
pub mod source_map;
pub mod error;
pub mod ast;
pub mod parser;
pub mod tt;
pub mod env;
pub mod elab;


// @temp
trait AllocStrExt {
    fn alloc_str<'a>(&'a self, string: &str) -> &'a str;
}

impl AllocStrExt for sti::arena::Arena {
    #[inline(always)]
    fn alloc_str<'a>(&'a self, string: &str) -> &'a str {
        // @temp.
        use sti::alloc::*;
        unsafe {
            let ptr = self.alloc(Layout::for_value(string)).unwrap();
            core::ptr::copy_nonoverlapping(string.as_ptr(), ptr.as_ptr(), string.len());
            core::str::from_utf8_unchecked(
                core::slice::from_raw_parts(ptr.as_ptr(), string.len()))
        }
    }
}

