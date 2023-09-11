use kibi::sti;

use sti::rc::Rc;

use kibi::vfs::MemFs;
use kibi::compiler::Compiler;


fn main() {
    kibi::spall::init("target/trace.spall").unwrap();

    let input = include_bytes!("../../../hello.kb");


    let fs = Rc::new(MemFs::new());

    let mut kc = Compiler::new(&fs); 

    fs.write("hello.kb", input);
    kc.add_source("hello.kb");
}

