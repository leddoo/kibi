
- move out in drop: consider special case, ref not live out.
  and all drop code is in drop (added by elab), so compiler
  knows what isn't dropped yet.
- `&out T` for out params. initially uninit, but live out.

