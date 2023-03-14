use minifb::{Window, WindowOptions};


mod renderer;
use renderer::*;


fn main() {
    let mut window = Window::new("kibi explorer", 800, 600, WindowOptions {
        resize: true,
        ..Default::default()
    }).unwrap();

    window.limit_update_rate(Some(std::time::Duration::from_millis(6)));


    let mut r = Renderer::new();

    while window.is_open() {
        let size = window.get_size();
        r.set_size(size.0 as u32, size.1 as u32);

        r.clear(13, 16, 23);

        r.draw_text("hey there, it's ber", 50., 50., 26., 200, 200, 200, 255);

        window.update_with_buffer(r.data(), size.0, size.1).unwrap();
    }
}

