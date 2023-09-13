use kibi::sti;
use kibi::spall;

use sti::traits::CopyIt;
use sti::arena_pool::ArenaPool;
use sti::vec::Vec;
use sti::hash::HashMap;
use sti::string::String;
use sti::rc::Rc;

use kibi::vfs::MemFs;
use kibi::compiler::Compiler;

mod json;


use std::fs::File;
use std::io::Write;

struct Lsp {
    stdin: File,
    stdout: File,
    log: File,

    message: Vec<u8>,
    initialized: bool,

    next_request_id: u32,
    active_requests: HashMap<u32, ()>,

    vfs: Rc<MemFs>,
    compiler: Compiler,
}

impl Lsp {
    pub fn new() -> Self {
        let vfs = Rc::new(MemFs::new());
        let compiler = Compiler::new(&vfs);
        Self {
            stdin: File::create(&format!("target/lsp-{}.stdin", std::process::id())).unwrap(),
            stdout: File::create(&format!("target/lsp-{}.stdout", std::process::id())).unwrap(),
            log: File::create(&format!("target/lsp-{}.log", std::process::id())).unwrap(),
            message: Vec::new(),
            initialized: false,
            next_request_id: 1,
            active_requests: HashMap::new(),
            vfs,
            compiler,
        }
    }

    pub fn process_bytes(&mut self, bytes: &[u8]) -> bool {
        spall::trace_scope!("kibi_lsp/process_bytes");

        _ = self.stdin.write(bytes);

        self.message.extend_from_slice(bytes);

        while self.message.len() > 0 {
            spall::trace_scope!("kibi_lsp/parse_message");

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
                self.message = msg;
                return true;
            }

            let content = &content[..content_length];

            let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };
            let content = {
                spall::trace_scope!("kibi_lsp/parse_content");

                let content = json::parse(&*temp, content).unwrap();
                {
                    use core::fmt::Write;

                    let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };
                    let mut buf = String::new_in(&*temp);
                    write!(&mut buf, "{}", content).unwrap();

                    assert_eq!(json::parse(&*temp, buf.as_bytes()), Ok(content));
                }
                content
            };

            let t0 = std::time::Instant::now();
            if !self.process_message(content) {
                return false;
            }
            let dt = t0.elapsed();
            _ = writeln!(self.log, "[debug] responded in {:?}", dt);

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
        {
            spall::trace_scope!("kibi_lsp/log_message");
            _ = writeln!(self.log, "[debug] {:?} message: {:#}", time(), msg);
        }

        assert_eq!(msg["jsonrpc"], "2.0".into());

        if let Some(method) = msg.get("method") {
            let method = method.as_string();

            let params = msg.get("params").unwrap_or(().into());
            assert!(params.is_object() || params.is_array() || params.is_null());

            if let Some(id) = msg.get("id") {
                let id = id.as_number();
                assert_eq!(id as u32 as f64, id);
                let id = id as u32;

                self.process_request(method, id, params)
            }
            else {
                self.process_notification(method, params)
            }
        }
        else {
            let id = msg["id"].as_number();
            assert_eq!(id as u32 as f64, id);
            let id = id as u32;

            let result =
                if let Some(result) = msg.get("result") {
                    Ok(result)
                }
                else { Err(msg["error"]) };

            self.process_response(id, result)
        }
    }

    fn process_request(&mut self, method: &str, id: u32, params: json::Value) -> bool {
        spall::trace_scope!("kibi_lsp/process_request"; "{method} ({id})");

        if !self.initialized {
            if method != "initialize" {
                _ = writeln!(self.log, "[error]: received {method:?} request before \"initialize\"");
                return true;
            }

            //let client_cap = params["capabilities"];


            self.send_response(id, Ok(json::Value::Object(&[
                ("capabilities", json::Value::Object(&[
                    ("positionEncoding", "utf-8".into()),

                    ("textDocumentSync", 1.0.into()), // full sync
                    ("semanticTokensProvider", json::Value::Object(&[
                        ("legend", json::Value::Object(&[
                            ("tokenTypes", json::Value::Array(&[
                                "error".into(),
                                "comment".into(),
                                "keyword".into(),
                                "punctuation".into(),
                                "operator".into(),
                                "string".into(),
                                "number".into(),
                                "type".into(),
                                "parameter".into(),
                                "variable".into(),
                                "property".into(),
                                "function".into(),
                                "method".into(),
                            ])),
                            ("tokenModifiers", json::Value::Array(&[])),
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
                self.send_response(id, Ok(json::Value::Null));
                return true;
            }

            "textDocument/semanticTokens/full" => {
                let doc = params["textDocument"];
                let path = doc["uri"].as_string();

                let tokens = self.compiler.query_semantic_tokens(path);

                let mut encoded = String::with_cap(5*5*tokens.len());
                use core::fmt::Write;

                sti::write!(&mut encoded, "[");
                for (i, token) in tokens.copy_it().enumerate() {
                    if i != 0 { sti::write!(&mut encoded, ",") }
                    sti::write!(&mut encoded, "{},{},{},{},{}",
                        token.delta_line, token.delta_col, token.len,
                        token.class as u32, 0);
                }
                sti::write!(&mut encoded, "]");

                self.send_response(id, Ok(json::Value::Object(&[
                    ("data", json::Value::Encoded(&encoded)),
                ])));

                return true;
            }

            _ => {
                _ = writeln!(self.log, "[warn]: request not supported {method:?}");
                return true;
            }
        }
    }

    fn process_notification(&mut self, method: &str, params: json::Value) -> bool {
        spall::trace_scope!("kibi_lsp/process_notification"; "{method}");

        if !self.initialized {
            _ = writeln!(self.log, "[error]: received {method:?} notification before \"initialize\"");
            return true;
        }

        match method {
            "exit" => {
                _ = writeln!(self.log, "[debug] exit received");
                return false;
            }

            "textDocument/didOpen" => {
                let doc = params["textDocument"];

                let lang = doc["languageId"];
                if lang != "kibi".into() {
                    return true;
                }

                let path = doc["uri"].as_string();
                let text = doc["text"].as_string();

                self.vfs.write(path, text.as_bytes());

                self.compiler.add_source(path);

                self.send_diagnostics();

                return true;
            }

            "textDocument/didClose" => {
                let doc = params["textDocument"];

                let path = doc["uri"].as_string();
                self.compiler.remove_source(path);

                return true;
            }

            "textDocument/didChange" => {
                let doc = params["textDocument"];

                let path = doc["uri"].as_string();

                let changes = params["contentChanges"].as_array();
                assert_eq!(changes.len(), 1);

                let change = changes[0];
                assert_eq!(change.get("range"), None);

                let text = change["text"].as_string();

                self.vfs.write(path, text.as_bytes());

                self.compiler.file_changed(path);

                self.send_request("workspace/semanticTokens/refresh", ().into());

                self.send_diagnostics();

                return true;
            }

            _ => {
                _ = writeln!(self.log, "[warn]: notification not supported {method:?}");
                return true;
            }
        }
    }

    fn process_response(&mut self, id: u32, result: Result<json::Value, json::Value>) -> bool {
        spall::trace_scope!("kibi_lsp/process_response"; "{id}");

        if !self.initialized {
            _ = writeln!(self.log, "[error]: received response before \"initialize\"");
            return true;
        }

        if self.active_requests.remove(&id).is_none() {
            _ = writeln!(self.log, "[error]: received response for inactive request {id}");
        }

        let _ = result;

        true
    }


    fn send_diagnostics(&mut self) {
        let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };
        let files = self.compiler.query_diagnostics(&*temp);

        for file in files.iter() {
            use core::fmt::Write;

            let mut result = String::with_cap_in(&*temp, file.diagnostics.len()*64);

            sti::write!(&mut result, "{{\"uri\":{:?},\"diagnostics\":[", file.path);

            for (i, d) in file.diagnostics.iter().enumerate() {
                if i != 0 { _ = write!(&mut result, ","); }
                sti::write!(&mut result, "{{");
                sti::write!(&mut result, "\"range\":{{\"start\":{{\"line\":{},\"character\":{}}},\"end\":{{\"line\":{},\"character\":{}}}}}",
                    d.range.begin.line, d.range.begin.col, d.range.end.line, d.range.end.col);
                sti::write!(&mut result, ",\"message\":{:?}", d.message);
                sti::write!(&mut result, "}}");
            }

            sti::write!(&mut result, "]}}");

            self.send_notification("textDocument/publishDiagnostics", json::Value::Encoded(&result));
        }
    }


    fn send_request(&mut self, method: &str, params: json::Value) {
        use core::fmt::Write;

        let id = self.next_request_id;
        self.next_request_id += 1;
        self.active_requests.insert(id, ());

        spall::trace_scope!("kibi_lsp/send_request"; "{} ({})", method, id);

        let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };

        let mut content = String::new_in(&*temp);
        sti::write!(&mut content, "{}", json::Value::Object(&[
            ("jsonrpc", "2.0".into()),
            ("id", (id as f64).into()),
            ("method", method.into()),
            ("params", params),
        ]));

        print!("Content-Length: {}\r\n\r\n{}", content.len(), content);

        _ = write!(self.stdout, "Content-Length: {}\r\n\r\n{}", content.len(), content);
    }

    fn send_notification(&mut self, method: &str, params: json::Value) {
        use core::fmt::Write;

        spall::trace_scope!("kibi_lsp/send_notification"; "{}", method);

        let temp = unsafe { ArenaPool::tls_get_scoped(&[]) };

        let mut content = String::new_in(&*temp);
        sti::write!(&mut content, "{}", json::Value::Object(&[
            ("jsonrpc", "2.0".into()),
            ("method", method.into()),
            ("params", params),
        ]));

        print!("Content-Length: {}\r\n\r\n{}", content.len(), content);

        _ = write!(self.stdout, "Content-Length: {}\r\n\r\n{}", content.len(), content);
    }

    fn send_response(&mut self, id: u32, result: Result<json::Value, json::Value>) {
        use core::fmt::Write;

        spall::trace_scope!("kibi_lsp/send_response"; "id: {}", id);

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

        _ = write!(self.stdout, "Content-Length: {}\r\n\r\n{}", content.len(), content);
    }
}


fn time() -> std::time::Duration {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap()
}


fn main() {
    use std::io::Read;

    kibi::spall::init(&format!("target/lsp-{}.spall", std::process::id())).unwrap();


    let mut lsp = Lsp::new();

    let mut buffer = [0; 128*1024];
    loop {
        match std::io::stdin().lock().read(&mut buffer) {
            Ok(n) => {
                if !lsp.process_bytes(&buffer[..n]) {
                    _ = writeln!(lsp.log, "[debug] exiting");
                    return;
                }
                std::io::stdout().flush().unwrap();
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


