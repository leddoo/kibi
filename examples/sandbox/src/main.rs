use kibi::sti;

use sti::rc::Rc;

use kibi::vfs::MemFs;
use kibi::compiler::Compiler;


fn main() {
    kibi::spall::init("target/trace.spall").unwrap();

    let fs = Rc::new(MemFs::new());
    fs.write("hello.kb", include_bytes!("../../../hello.kb"));

    let mut c = Compiler::new(&fs);
    c.add_source("hello.kb");
    c.update();

    println!("{:#?}", c.query_semantic_tokens("hello.kb"));
}

