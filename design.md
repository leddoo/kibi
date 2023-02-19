
### types & values:

- `Nil`:
    - value type.
    - values: `nil`.

- `Bool`:
    - value type.
    - values: `false`, `true`.

- `Int`:
    - value type.
    - values: signed, 64 bit, 2's complement integer.

- `Float`:
    - value type.
    - values: ieee 754 binary64.

- `String`:
    - value type.
    - values: valid utf8 sequence.

- `Tuple`:
    - value type.
    - values: finite sequence of values.

- `List`:
    - reference type.
    - values: finite sequence of values.

- `Map`:
    - reference type.
    - values: unordered set of (key, value) pairs.
        - keys must be unique by raw equality.
        - keys must not be `NaN`s.

- `Object`:
    - reference type.
    - values: unordered set of (key, value) pairs, prototype slot.
        - keys must be unique strings.

- `Function`:
    - reference type.
    - values: function, method flag, environment slot, captures.


### vm operations

- `get_index(base: Value, index: Value) -> Result<Value>`
    - semantics:
        ```
        if base is Nil, Bool, Int, Float, String:
            return Err(type).
        if base is Tuple(values), List(values):
            let index = to_int_exact(index)?
            return array_get_index(values, index).ok_or(Err(bounds))
        if base is Map(values):
            return map_get_index(values, index).ok_ok(Err(key))
        if base is Object(object):
            return object_get_index(object, index)
        unreachable
        ```

- `set_index(base: Value, index: Value, value: Value, is_define: Bool)`
    - semantics:
        ```
        if base is Nil, Bool, Int, Float, String, Tuple:
            return Err(type).
        if base is List(values):
            let index = to_int_exact(index)?
            array_set_index(values, index, valuex, is_define)?
        if base is Map(values):
            map_set_index(values, index, value, is_define)?
        if base is Object(object):
            object_set_index(object, index, value, is_define)?
        unreachable
        ```

- `call(func: Value, args: Tuple)`
    - tbd.

- `method_call(self: Value, name: String, args: Tuple)`
    - semantics:
        ```
        let m = get_index(self, name)
        if is_method(m):
            call m, (self, *args)
        else:
            call m, args
        ```

- todo: op1/op2.


### abstract operations

- `to_int_exact(value: Value) -> Result<Int>`
    - if value is an `Int`, returns value.
    - if value is a `Float`, tries to convert to `Int`, such that converting back to `Float` produces the same value.
    - else returns error.

- `array_get_index(array: Array, index: Int) -> Option<Value>`
    - tries to return the value at `index`.
    - if `index < 0`, returns nothing.
    - if `index >= 0`, returns nothing.

- `array_set_index(array: Array, index: Int, value: Value, is_define: Bool) -> Result<()>`
    - if `array` is frozen, returns error.
    - if `index < 0`, returns error.
    - if `index >= array_len(array)`
        - if `is_define`:
            - resizes `array` to length `index+1`.
            - new values are `nil`.
        - else, returns error.
    - stores `value` in `array` at `index`.

- `map_get_index(map: Map, key: Value) -> Option<Value>`
    - if there is a pair `(k, v) in map, raw_eq(k, key)`, returns `v`.
    - otherwise, returns nothing.

- `map_set_index(map: Map, key: Value, value: Value, is_define: Bool) -> Result<()>`
    - if there is a pair `(k, v) in map, raw_eq(k, key)`:
        - replaces `v` with `value`.
    - otherwise:
        - if `is_define`: adds `(key, value)` to `map`.
        - otherwise: returns error.

- `object_get_index(object: Object, key: Value) -> Result<Value>`
    - tbd.

- `object_set_index(object: Object, key: Value, value: Value, is_define: Bool) -> Result<()>`
    - tbd.



### limits

- the maximum number of entries for Tuples, Lists, Maps, Objects is `2^31 - 1`.



### functions

- this should be split up into: compiler docs, vm docs.
    - compiler: what vm operations it generates, etc. (define in terms of vm semantics)
    - vm: method is function object with method flag set.

- parameters:
    - format: `(self? [required]) [optional] varargs?`
    - argument binding:
        - in general, positional (left to right, one by one).
        - self:
            - is the first required parameter.
            - if the call is a `method-call`, binds to the `self` argument.
        - optional parameters are `nil`, if not bound to an argument.
        - the varargs parameter is the empty tuple, if not bound to any arguments.
        - if there are fewer arguments than required parameters (not enough arguments).
        - if there are more arguments than required parameters:
            - first, the optional parameters are assigned, one by one.
            - if there are arguments left:
                - if the function takes varargs, the extra arguments are accumulated into a tuple, which is bound to the varargs parameter.
                - otherwise, the call fails (too many arguments).

- return values:
    - all functions must return exactly one value.
    - the compiler emits `return nil`, if no value is returned.

- methods:
    - method: a function with the `method` flag set.
        - the compiler sets the `method` flag, if the first parameter is called `self`.
            - usage of "self" for other parameters has no effect and raises an warning.
    - method-call: a special instruction.
        - format: `method_call self: reg, name: string, [args: reg]`.
        - the compiler emits `method-call`s for `call-expr`s whose `target` is a `field-expr`: `($self . $name)($args)`.



### stuff

- TBD:
    - `__method_call` metamethod?

