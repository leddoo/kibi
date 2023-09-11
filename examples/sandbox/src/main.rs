use kibi::sti;

use sti::rc::Rc;

use kibi::vfs::MemFs;
use kibi::compiler::Compiler;


fn main() {
    kibi::spall::init("target/trace.spall").unwrap();

    let input = include_bytes!("../../../hello.kb");


    let fs = Rc::new(MemFs::new());

    let vfs = unsafe { fs.clone().cast(|p| p as *mut sti::rc::RcInner<dyn kibi::vfs::Vfs>) };

    let mut kc = Compiler::new(vfs); 

    fs.write("hello.kb", input);
    kc.add_source("hello.kb");
}

