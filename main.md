
- todo:
    - basic prototype:
        - environment.
        - tables.
        - generic ops.
        - constants.
    - basic front-end.
        - lisp syntax - easy to parse.
        - point is to just mess around a bit.
    - more features.
        - meta tables.
        - upvalues.

    - define semantics.
        - values.
        - environments.
        - ast & operational semantics.

- function calls.
    - would be dope if you could specify where the return value should go.
        - already use all 3 bytes.
        - could use convention that args & function need to be at top of stack.
          then only need to know number of args. function is at `top - #args`.
    - varargs/multret:
        - don't love the idea of adjusting top.
        - varargs are fine. function knows how many args it passes.
        - interesting cases:
            - passing own varargs to another function.
            - passing multret as varargs to another function.
    - thinking layout:
        ```
            | func | params? | varargs | params | locals & temps |   multret   |
                                       |--------- regs ----------|
                                                   | func | args |--- args? ---|
                                                   | func | params? |  varargs | params | ... |
        ```
        - to call, place func & args at end of regs.
            - option to include multret in args.
        - but multret: maybe just store those in a separate array.
            - multret can only ever be at the end of the stack (cause we don't adjust top).
            - benefit of being at end of stack is that are in place for forwarding to another function.
    - thinking ops:
        - call: #args, dest, #rets.
            - `#args = -1` -> include multret in args.
            - `#rets = -1` -> store in multret.
        - ret: #rets.
            - `#rets = -1` -> return multret.
        - varargs_to_multret:
            - copies the current function's varargs into the multret section.
            - can be used for varargs forwarding (`#args = -1`).
                - if passed to `List.new`, collects varags into list.
                - although, you'd probably want a special instruction for that.
                  to avoid the double copy.
                - maybe this could be a property of the varargs param.
                    - something like `fn foo(a, b, c[])`.
                    - meaning, the varargs are collected into a list & removed from the stack on entry.
        - select_varags:
            - copies fixed number of varargs to register(s).
        - select_multret:
            - copies fixed number of multret to register(s).
    - compound ops:
        - multret to list: call list ctor with multret.
        - varargs to list: varargs to multret + call list ctor with multret.
        - list to multret: built-in function (call with results in multret).
    - on errors:
        - issue: non-call operations can fail.
            - perhaps, we should have try/catch/finally?
            - function doesn't return the expected number of values.
                - this could be implemented as an error in the callee.
                - pcall would forward the expected number of values (minus one).
                  and return the bool + the values or `nil`s.
            - selecting too many values from varargs/multret.
                - seems this is now the only thing that can't be done by creating a wrapper function + pcall.
                - so i guess these should just have fallibility baked in.
                - `ok, x, y = c...`.
                - meaning, require n+1 register, where the first one indicates success.
                - and like pcall, return a bunch of nils on error.
                - or maybe: return number of selected values. fill rest with nil.
    - multret collapsing:
        - need ability to call any function, but only require one argument.
        - hmm, i guess requiring *fewer* values than were actually returned is fine actually.
          so shouldn't be an error.
        - `x = 1, 2` is fine (`x = 1`).
        - `x, y = 1` is an error.
        - is a bit weird, but seems fine. this isn't unpacking/pattern matching like in python.
    - native functions:
        - native function value.
            - just a function pointer store in `Value`.
            - used for the built-ins & other stateless native functions.
            - are passed the vm state & stuff.
        - native closure object.
            - basically wraps `Box<dyn Fn(&mut Vm)>`.
            - but with inline storage (of state + vtable ptr),
              assuming we can do that on stable rust.

- lztf (luazero transfer format).
    - similar to wasm/llvm-ir.
    - module oriented.
    - safe to run untrusted modules.
    - pre-optimized. eg: pre-resolved built-ins & methods.
    - not fully optimized/lowered:
        - default mapping for abstract operations still perform runtime type checks.
        - inline cache & hidden class optimizations, as well as interruptible jumps are not exposed.
        - vm can perform implementation specific optimizations at load time.
        - the fully optimized vm bytecode could be cached by the application.
            - but unsafe to run.
            - and not stable across vm implementation versions.
    - module:
        - list of functions.
        - main function (must have no extra upvalues).
        - constants.
        - linking info.
        - type info.
    - function:
        - number of (extra) upvalues & registers.
            - later with type info.
            - "extra" upvalues, cause all functions have an environment (first upvalue).
        - instruction sequence.
            - generic ops.
            - built-ins.
            - labels.
            - 3 address code.
    - for now, structured control flow.
        - front-end won't have goto. instead: labeled break/continue & defer.
        - hoping (not sure) this simplifies analyses:
            - loop identification (only `repeat`) for interrupt checking jumps.
            - hidden class pre-computation & array reserving.
        - could be a mistake, we'll see.


- less stupid:
    - instructions:
        - load into specific "registers" (~ locals).
        - compare & jump if true/false.
        - loop prep & loop step (the trailing condition trick thing).
        - inline caching.


- cool stuff:
    - interruptible jump.
        - checks the vm state for an interrupt handler before jumping.
        - can safely run plugin code on main thread.
            - have watchdog thread.
            - if main thread takes too long, interrupt.
            - query what it's doing.
            - ask user whether to cancel the operation.
        - technically need to use an atomic, cause otherwise UB in rust.
            - thing is, this check is executed *a lot*.
            - maybe using a raw pointer is fine.
              and don't store the memory on the vm,
              cause the memory must not be borrowed.
    - typed user data.
    - assert meta table instruction.
    - `coverage` instruction.
        - with inline hit counter.
        - have to walk code to reset/collect data.
        - but has really low overhead & don't need to allocate counter indices.


- idioms:
    - `nil` is `Option::None`.
        - `nil` is a valid table value. it signifies the absence of a field's *value*. this is different from the field *itself* being absent. accessing absent table fields raises an error.
        - similarly, there's a difference between a variable being undefined (raising an error, if accessed), and holding a `nil` value.
        - "optional parameters" are parameters that default to `nil`, if not specified by the user. however, the user can also explicitly pass a `nil` value, and the callee cannot detect this. initially, this may seem inconsistent with the behavior of absent table fields and undefined variables. but it actually isn't, because it doesn't make sense for parameters to be "absent" (or "undefined"). if optional parameters, that were given no value by the caller, were "absent", the callee would trigger an error, if they tried accessing those parameters. clearly this is undesirable, hence the default state of optional parameters is `nil` and not absent/undefined. this has another nice property: if a function takes multiple optional parameters, the caller can provide a value for one of the later optional parameters by simply passing `nil` for all optional parameters preceding it. if explicitly passing `nil` had different behavior than not passing a value, the virtual machine would have to implement named parameters for this use case. this way however, named parameters can be implemented entirely by the language front-ends.
        - there is no `Option<Option>`; `nil` can only represent absence once. in particular, optional parameters cannot have optional types, they already add one level of optionality.



- goals:
    - lua, but less error prone.
    - clean api.
        - return value based error handling.
        - well-defined byte code.
    - zero dependencies.
    - highly introspective.
    - fast.


- what i want to do differently:
    - zero based indexing.
    - snake_case.
    - arbitrary precision integers (optional, but default enabled).
    - floats & integers as separate types.
        - python style: with auto conversion to float but errors on int too large.
        - perhaps strict mode, where conversions have to be explicit.
    - native lists?
        - not as separate types, don't want to break uniformity.
        - but maybe do it like js. so with a "List" meta table, `[]` syntax, contiguous storage (length determines buffer size, nils are valid values ~ equiv to table, but take up storage).
        - thinking js-like is the way to go. `[]` syntax, special `len` field, `append` method. apart from spec simplicity, i don't see why we should hack regular tables to be efficient as arrays, if we can just have arrays directly. (still behaving like a regular table, in that they can have other attrs).
        - though, i've never used the fact that you can put properties on arrays in js.
        - maybe just go with python style lists? distinct type. no props.
    - computed table entries?
        - possible with `__index` & `__new_index`.
        - but better performance with native support. don't need to index twice, don't need to chain meta tables when have another use case for `__index`.
    - string: immutable utf8. buffer: byte array.
    - vector types.
    - missing key errors on index.
        - `nil` is a valid table value.
        - `get` method that takes an alternative value, default is nil.
    - missing key errors on write?
        - `table.key := value` as infallible version.
        - `__get`, `__set`, `__def`.
    - arity errors.
        - then also default args, cause otherwise have to explicitly pass nil for optional args.
        - and prob named args too, cause that lets you specify any one of multiple default args.
        - default args as upvalues.
    - globals have to be declared.
        - analogous to: key error in environment table.
        - `global name` -> `_ENV._G.name = nil`.
        - `local name` in top level -> `_ENV.name = nil`.
    - native table freezing.
    - require boolean for conditional & loop?
        - seems consistent with the "more strict" changes.

- what stays the same:
    - pcall based exception handling.
    - metatables.
    - method semantics `obj:method(arg)` -> `obj.method(obj, arg)`.

- study lua:
    - concepts:
        - values & types.
        - environments.
        - execution context.
        - error handling.
        - meta tables.
        - garbage collection.
        - coroutines.
        - syntax.
        - c api.
        - libraries.
    - values & types:
        - dynamically typed.
        - values have types, not value holders.
        - all values are first class (can be stored in variables, passed around).
        - basic types: nil, boolean, number, string, function, userdata, thread, table.
        - falsy values: false, nil. everything else, truthy.
        - nil value in table means absence of a value. assigning nil removes the table entry.
        - numbers: integers & floats. converted automatically.
        - value vs reference types.
            - Tables, functions, threads, and (full) userdata values are objects: variables do not actually contain these values, only references to them. Assignment, parameter passing, and function returns always manipulate references to such values; these operations do not imply any kind of copy. 
        - length of string must fit in lua integer.
        - tables: associative array. keys can be any lua value, except nil & nan.

