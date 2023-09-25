use kibi::sti;

use sti::rc::Rc;

use kibi::vfs::MemFs;
use kibi::compiler::Compiler;


fn main() {
    kibi::spall::init("target/trace.spall").unwrap();

    let (path, contents) = {
        if std::env::args().len() == 2 {
            let path = std::env::args().nth(1).unwrap();
            let code = &*std::vec::Vec::leak(std::fs::read(&path).unwrap());
            let path = core::str::from_utf8(std::vec::Vec::leak(path.into_bytes())).unwrap();
            (path, code)
        }
        else {
            ("hello.kb", &include_bytes!("../../../hello.kb")[..])
            //("sb.kb", &include_bytes!("../../../sb.kb")[..])
        }
    };

    let fs = Rc::new(MemFs::new());
    fs.write(path, contents);

    let mut c = Compiler::new(&fs);

    let t0 = std::time::Instant::now();
    c.add_source(path);
    c.update();
    let dt = t0.elapsed();
    println!("single run: {:?}", dt);

    if 0==1 {
        let t0 = std::time::Instant::now();
        let iters = 1000;
        for _ in 0..iters {
            c.file_changed(path);
            c.update();
        }
        let dt = t0.elapsed();
        println!("multi run: {:?}", dt/iters);
    }

    //println!("{:#?}", c.query_semantic_tokens("hello.kb"));
    println!("{:#?}", c.query_diagnostics(&*sti::arena_pool::ArenaPool::tls_get_temp()));
}

