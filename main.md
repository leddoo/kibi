
- next steps:
    - step debugger.
    - wasm.
        - nominal structs, enums & traits, typeid.
        - better runtime errors.
    - macros, modules, multithreading.
    - error handling:
        - try operator.
        - pcall.
    - `Gc` type, `new`.
        - implicit deref/inout with methods.
        - but pass without deref.
        - so `&*` to inout boxed value?
        - compiler could do implicit stuff if has types.
        - fix gc.


- todo: step debugger.
    - render pcs.
        - arrows.
        - highlighting lines.
        - including dormant ones. (show "inverse depth")
    - scrollable codeview.
    - partial code view.
        - probably through replacements.
    - multiple code views.

