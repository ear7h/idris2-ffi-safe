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

## Example

```idris
TestStruct : Type
TestStruct = Struct "TestStruct"
  [ ("a", Bits8)
  , ("b", Bits16)
  , ("c", Bits32)
  , ("d", Bits64) ]

-- the usual FFI declaration
%foreign "C:printStruct,libffisafe_test"
printStruct : TestStruct -> PrimIO ()

-- newRef creates reference with lifetime a'
--
-- dereferencing the reference occurs inside `safeFFI`,
-- such that typical users never have to realize an lifetime-less
-- pointer
test : IO ()
test = runScopedIO $ \a' => do
  x <- newRef { cty = TestStruct }
    ( the Bits8  101
    , the Bits16 10203
    , the Bits32 20405060
    , the Bits64 50404020205 )
  safeFFI printStruct [x]

-- references of an outer scope can seamlessly
-- used in a subscope
testScope1 : IO Int
testScope1 = runScopedIO $ \a' => do
  x <- newRef { cty = Int } $ the Int 10
  runSubScopedIO a' $ \b', _ => do
    readRef x

-- references can escape their subscope but
-- can't be used (as with the ST monad)
failing "Can't solve constraint"
  testScope2 : IO Int
  testScope2 = runScopedIO $ \a' => do
    x <- runSubScopedIO a' $ \b', _ => do
      newRef { cty = Int } $ the Int 10
    readRef x
```


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

