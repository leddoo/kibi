kibi
- a scripting language, kinda.
- **heavy wip**.

what's happening?
- i'm rewriting it.
- it still is intended to be a scripting language, but i'm also messing
  with dependent types and a powerful macro system.
- so simplicity isn't really a goal anymore (it is, but it's a different
  kind of simplicity).
- beginner friendliness is also out the window. as in, i'm just making
  a scripting language, that i want to use, and it'll be as beginner friendly
  as is feasible.
- i'm again going with value types, as they play very nicely with dependent types.
- this time, the (only) runtime target will be (standalone) wasm. a major
  motivation for the language is building better development tools (specifically
  around visual debugging). as i started working on that in the last iteration
  (the kibi explorer), i realized, most of what i was doing was language
  independent, so i switched my focus to wasm and building my dev tools around that.

