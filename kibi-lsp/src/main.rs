use kibi::sti;
use sti::arena_pool::ArenaPool;
use sti::vec::Vec;
use sti::string::String;

mod json;


use std::fs::File;
use std::io::Write;

struct Lsp {
    stdin: File,
    stdout: File,
    log: File,

    message: Vec<u8>,
    initialized: bool,
}

impl Lsp {
    pub fn new() -> Self {
        Self {
            stdin: File::create("target/lsp.stdin").unwrap(),
            stdout: File::create("target/lsp.stdout").unwrap(),
            log: File::create("target/lsp.log").unwrap(),
            message: Vec::new(),
            initialized: false,
        }
    }

    pub fn process_bytes(&mut self, bytes: &[u8]) -> bool {
        _ = self.stdin.write(bytes);

        self.message.extend_from_slice(bytes);

        while self.message.len() > 0 {
            let mut msg = self.message.take();

            let bytes = msg.as_slice();

            let Some(end_headers) = bytes.windows(4).position(|w| w == b"\r\n\r\n") else {
                return true;
            };

            let headers = &bytes[..end_headers];
            let content = &bytes[end_headers+4..];

            let headers = core::str::from_utf8(headers).unwrap();

            let mut content_length = None;
            for header in headers.lines() {
                let (key, value) = header.split_once(": ").unwrap();

                if key == "Content-Length" {
                    let value = usize::from_str_radix(value, 10).unwrap();
                    content_length = Some(value);
                }
            }

            let content_length = content_length.unwrap();

            if content_length > content.len() {
                return true;
            }

            let content = &content[..content_length];

            let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };
            let content = json::parse(&*temp, content).unwrap();

            {
                use core::fmt::Write;

                let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };
                let mut buf = String::new_in(&*temp);
                write!(&mut buf, "{}", content).unwrap();

                assert_eq!(json::parse(&*temp, buf.as_bytes()), Ok(content));
            }

            let ok = self.process_message(content);
            _ = self.log.flush();
            if !ok {
                return false;
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
            self.message = msg;
        }

        return true;
    }

    fn process_message(&mut self, msg: json::Value) -> bool {
        _ = writeln!(self.log, "[debug] {:?} message: {:#}", time(), msg);

        assert_eq!(msg["jsonrpc"], "2.0".into());

        let id = msg.get("id").and_then(|id| id.try_number()).map(|id| {
            assert_eq!(id as i32 as f64, id);
            id as i32
        });

        let method = msg["method"].try_string().unwrap();

        let params = msg.get("params").unwrap_or(&json::Value::Null);
        assert!(params.is_object() || params.is_array() || params.is_null());

        if !self.initialized {
            if method != "initialize" {
                _ = writeln!(self.log, "[error]: received {method:?} message before \"initialize\"");
            }

            let id = id.unwrap();

            //let client_cap = params["capabilities"];


            self.send_response(id, Ok(json::Value::Object(&[
                ("capabilities", json::Value::Object(&[
                    ("positionEncoding", "utf-8".into()),

                    ("textDocumentSync", 1.0.into()), // full sync
                                                      //
                    // @temp: select from client's list.
                    ("semanticTokensProvider", json::Value::Object(&[
                        ("legend", json::Value::Object(&[
                            ("tokenTypes", json::Value::Array(&[
                                "namespace".into(),
                                "type".into(),
                                "class".into(),
                                "enum".into(),
                                "interface".into(),
                                "struct".into(),
                                "typeParameter".into(),
                                "parameter".into(),
                                "variable".into(),
                                "property".into(),
                                "enumMember".into(),
                                "event".into(),
                                "function".into(),
                                "method".into(),
                                "macro".into(),
                                "keyword".into(),
                                "modifier".into(),
                                "comment".into(),
                                "string".into(),
                                "number".into(),
                                "regexp".into(),
                                "operator".into(),
                                "decorator".into(),
                            ])),
                            ("tokenModifiers", json::Value::Array(&[
                                "declaration".into(),
                                "definition".into(),
                                "readonly".into(),
                                "static".into(),
                                "deprecated".into(),
                                "abstract".into(),
                                "async".into(),
                                "modification".into(),
                                "documentation".into(),
                                "defaultLibrary".into(),
                            ])),
                        ])),
                        ("full", json::Value::Object(&[
                            ("delta", false.into()),
                        ])),
                    ])),
                ])),
            ])));

            self.initialized = true;
            return true;
        }

        match method {
            "shutdown" => {
                let id = id.unwrap();
                self.send_response(id, Ok(json::Value::Null));
            }

            "exit" => {
                _ = writeln!(self.log, "[debug] exit received");
                return false;
            }

            _ => {
                _ = writeln!(self.log, "[warn]: message not supported {method:?}");
            }
        }
        return true;
    }

    fn send_response(&mut self, id: i32, result: Result<json::Value, json::Value>) {
        use core::fmt::Write;

        let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };

        let mut content = String::new_in(&*temp);
        sti::write!(&mut content, "{}", json::Value::Object(&[
            ("jsonrpc", "2.0".into()),
            ("id", (id as f64).into()),
            match result {
                Ok(result) => ("result", result),
                Err(error) => ("error",  error),
            }
        ]));

        print!("Content-Length: {}\r\n\r\n{}", content.len(), content);
        std::io::stdout().flush().unwrap();

        _ = write!(self.stdout, "Content-Length: {}\r\n\r\n{}", content.len(), content);
    }
}


fn time() -> std::time::Duration {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap()
}


fn main() {
    use std::io::Read;


    let mut lsp = Lsp::new();

    let mut buffer = [0; 128*1024];
    loop {
        match std::io::stdin().lock().read(&mut buffer) {
            Ok(n) => {
                if !lsp.process_bytes(&buffer[..n]) {
                    _ = writeln!(lsp.log, "[debug] exiting");
                    return;
                }
            }

            Err(_) => {
                _ = write!(lsp.log, "reading stdin failed. exiting.");
                return;
            }
        }

        // @todo: block.
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
}


