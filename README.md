# `System.FFI.Safe`

Memory safe FFI for Idris 2.

While Idris is itself a memory safe language, FFIs pose a problem
to memory safety: memory needs to be manually managed since the
garbage collector does not know anything about C-allocated memory
and how it might be used. This library builds on top of Idris'
existing FFI and borrows (pun-intended) ideas from Rust to prevent
common memory corruption bugs using dependent types.

A butchered version of my MSc dissertation explaining the
code can be found in `doc/main.pdf`

## status

- Currently this is a prototype, requirign a few small
  modifications/improvements to the compiler.
  - These changes can be found here: https://github.com/idris-lang/Idris2/compare/main...ear7h:Idris2:ear7h
- Only the Chez backend is supported

## running

```
make repl
:exec test
```

```
make pdf
```

