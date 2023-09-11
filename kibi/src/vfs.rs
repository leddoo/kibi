use sti::vec::Vec;


#[derive(Clone, Copy, Debug)]
pub enum VfsError {
    FileNotFound,
}

pub trait Vfs {
    fn read(&self, path: &str) -> Result<Vec<u8>, VfsError>;
}



use core::cell::RefCell;
use sti::string::String;
use sti::hash::HashMap;


pub struct MemFs {
    inner: RefCell<HashMap<String, Vec<u8>>>,
}

impl MemFs {
    pub fn new() -> Self {
        Self { inner: RefCell::new(HashMap::new()) }
    }

    pub fn write(&self, path: &str, contents: &[u8]) {
        self.inner.borrow_mut().insert(path.into(), contents.into());
    }
}

impl Vfs for MemFs {
    fn read(&self, path: &str) -> Result<Vec<u8>, VfsError> {
        self.inner.borrow().get(path).cloned().ok_or(VfsError::FileNotFound)
    }
}


