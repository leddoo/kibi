use kibi::sti;
use sti::arena_pool::ArenaPool;
use sti::vec::Vec;
use sti::string::String;

mod json;


fn main() {
    use std::io::Read;
    use std::io::Write;

    let mut log = std::fs::File::create("lsp.log").unwrap();

    let mut message = Vec::new();
    let mut buffer = [0; 128*1024];
    loop {
        match std::io::stdin().lock().read(&mut buffer) {
            Ok(n) => {
                message.extend_from_slice(&buffer[..n]);

                if message.len() > 0 {
                    if !process_message(&mut message, &mut log) {
                        return;
                    }
                }
            }

            Err(_) => {
                _ = log.write(b"reading stdin failed. exiting.");
                return;
            }
        }

        // @todo: block.
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
}


fn process_message(msg: &mut Vec<u8>, log: &mut std::fs::File) -> bool {
    use std::io::Write;

    _ = log.write(b"[debug] try parsing\n");

    let bytes = msg.as_slice();

    let Some(end_headers) = bytes.windows(4).position(|w| w == b"\r\n\r\n") else {
        _ = log.write(b"[debug] not enough data\n");
        _ = log.write(bytes);
        _ = log.write(b"\n\n");
        return true;
    };

    let headers = &bytes[..end_headers];
    let content = &bytes[end_headers+4..];

    let Ok(headers) = core::str::from_utf8(headers) else {
        _ = log.write(b"[error] headers are not valid utf8:\n");
        _ = log.write(headers);
        _ = log.write(b"\n");
        return false;
    };
    _ = log.write(b"[debug] headers valid utf8\n");

    let mut content_length = None;
    for header in headers.lines() {
        let Some((key, value)) = header.split_once(": ") else { return false };
        _ = log.write(format!("[debug] header {key:?}: {value:?}\n").as_bytes());

        if key == "Content-Length" {
            let Ok(value) = usize::from_str_radix(value, 10) else {
                _ = log.write(b"[error] content length not a number: ");
                _ = log.write(value.as_bytes());
                _ = log.write(b"\n");
                return false;
            };

            content_length = Some(value);
        }
    }

    let Some(content_length) = content_length else {
        _ = log.write(b"[error] content length missing\n");
        return false;
    };

    if content_length > content.len() {
        _ = log.write(format!("[debug] valid headers, but need more data. have {}, need {}\n",
                content.len(), content_length).as_bytes());
        return true;
    }

    let content = &content[..content_length];

    let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };
    let content = match json::parse(&*temp, content) {
        Ok(content) => content,
        Err(e) => {
            _ = log.write(format!("[error] invalid json {:?}", e).as_bytes());
            return false;
        }
    };

    _ = log.write(format!("[debug] content:\n{:#}\n", content).as_bytes());

    {
        use core::fmt::Write;

        let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };

        let mut buf = String::new_in(&*temp);
        write!(&mut buf, "{}", content).unwrap();

        match json::parse(&*temp, buf.as_bytes()) {
            Ok(json) => {
                _ = log.write(format!("[debug] json-reparse: {}\n", json == content).as_bytes());
            }
            Err(e) => {
                _ = log.write(format!("[debug] json-reparse failed: {:?}\n", e).as_bytes());
            }
        }
    }

    let consumed = end_headers + 4 + content_length;
    unsafe {
        let remaining = msg.len() - consumed;
        let ptr = msg.as_mut_ptr();
        core::ptr::copy(
            ptr.add(consumed),
            ptr,
            remaining);
        msg.set_len(remaining);
    }

    _ = log.write(b"[debug] ok, ready to parse message\n");

    unsafe {
        static mut SEND: bool = true;
        if !SEND {
            return true;
        }
        SEND = false;
    }

    _ = std::io::stdout().write(b"Content-Length: 59\r\n\r\n{\"id\": 1, \"jsonrpc\": \"2.0\", \"result\": {\"capabilities\":{}} }");

    _ = std::io::stdout().flush();

    _ = log.write(b"[debug] wrote a silly response\n");

    return true;
}

