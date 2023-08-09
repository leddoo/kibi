
just some random stuff:

```
use std::fs::File

// in json module:
enum JsonValue {
    null
    boolean: Bool
    number:  Number
    array:   [JsonValue]
    object:  {String, JsonValue}
}


fn main() {
    let contents = File::read("people.json")!
    let doc = json::parse(contents)!
    dump_json(doc)
}

fn dump_json(val: JsonValue, indent = 0, do_indent = true) {
    if do_indent {
        print("  " * indent)
    }

    match val {
        .null      => println(f"null")
        .boolean b => println(f"a bool {b}")
        .number  n => println(f"a number {n}")

        .array a => {
            println("an array:")
            for v in a {
                dump_json(v, indent + 1)
            }
        }

        .object o => {
            println("an object:")
            for k, v in o {
                print(f"{"  " * (indent + 1)}{k}: ")
                dump_json(v, indent + 1, do_indent = false)
            }
        }
    }
}

```


some grammar stuff:

```
module:
    - item*

item:
    - item_use:
        - "use" use_path

        use_path:
            - path
            - use_path "::" "*"

    - item_fn:
        - "fn" ident param_list ret? block

        param_list: "(" sep_by(binding, ",") ")"

        ret: "->" expr

    - item_enum:
        - tbd

    - item_struct:
        - tbd


ident: yk, idents

dot_ident: "." no_ws ident

path:
    - ident
    - path "::" ident

binding:
    - ident (":" expr)? ("=" expr)?


stmt:
    - item
    - "let" binding ";"
    - expr ";"

expr:
    - path

    - dot_ident

    - expr_parens:
        - "(" (expr_tup | expr_type_hint) ")"

    - expr_unop:
        - unop expr // with precedence

    - expr_binop:
        - expr binop expr // with precedence.

    - expr_field:
        - expr "." ident

    - expr_index:
        - expr "[" expr_tup "]"

    - expr_call:
        - expr "(" sep_by(call_arg, ",") ")"

        call_arg:
            - expr
            - ident "=" expr

    - expr_assign:
        - expr_tup "=" expr_tup

    - expr_list:
        - "[" expr "]"

    - expr_list_type
        - "[" expr "]"

    - expr_map:
        - "{" sep_by(ident ":" expr, ",") "}"

    - expr_map_type
        - "{" expr "," expr "}"

    - expr_match:
        - "match" expr "{" match_case* "}"

        match_case: (path | dot_ident) ident? "=>" (expr | block) ";"

    - expr_if:
        - "if" expr block ("elif" expr block)* ("else" block)?

    - expr_while:
        - "while" expr block

    - expr_loop:
        - "loop" block

    - expr_do:
        - "do" block


    block: "{" stmt* "}"

    expr_tup:
        - expr
        - expr_tuple

    expr_tuple: sep_by(expr, ",")

    expr_type_hint: expr ":" expr


```

