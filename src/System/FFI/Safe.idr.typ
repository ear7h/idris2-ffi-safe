/* idris
module System.FFI.Safe


import Data.Bits
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.List1
import Data.String
import Data.Vect
import System

*/

= Design

== Preventing memory leaks and use-after-free with scopes <sec-st-lifetimes>

The design of lifetimes in this library is heavily based on the `ST` (state
thread) monad @st-monad.  Informally, `ST` allows mutable state (generally
disallowed in pure functional programming) by keeping track of the
thread which the mutable state belongs to. Note, the "thread" here should
not confused with concurrency primitive.

#figure(
```idris
data ST : (s : Type) -> (a : Type) -> Type where
  MkSt : (s -> (a, s)) -> ST s a

data STRef : (s : Type) -> (a : Type) -> Type where
  MkRef : (s : Type) -> a -> STRef s a

newSTRef   : a -> ST s (STRef s a)
readSTRef  : STRef s a -> ST s a
writeSTRef : STRef s a -> a -> ST s ()

runST : ({ s : Type } -> ST s a) -> a
```,
  caption: [`ST`, `STRef`, and associated types as defined in @st-monad],
)

The important detail is that `runST` requires `{s : Type} -> ST s a`.
The `ST` value being run needs to be general over all types `s`.
Calling `runST` on an `ST` then "materializes" the general `s` into
a specific type, which we'll denote `s1`; `s1` marks the thread.
Thus, a call to `newSTRef` inside the `ST s1 _` becomes
`ST s1 (STRef s1 a)`. The above implementation
hides some category-theoretical magic (ie. Monads), but assume the
`STRef s1 a` inside `ST` is freely accessible; latter calls to
`readSTRef` and `writeSTRef` take up the materialized `s1` from their inputs into
their output `ST`s. These specific `ST s1 _` types cannot be used in a different `runST`
because the `s1` is no longer general enough for `runST`.

```idris
failing "When unifying"
  testRunSTBad : Int
  testRunSTBad = runST $ readSTRef (runST $ newSTRef 2)
```

This pattern has a couple useful properties. Firstly,
the computation inside an `ST` starts and ends within `runST`
function. If allocation were to occur inside the `ST`, this
is a convenient place for deallocating such memory.
Secondly, the specific `STRef s1 a`, is only usable within the thread
`s1`. If `STRef` held a pointer to memory allocated inside `ST`, it would
then not be accessible after being deallocated at the end of
`runST`. These two properties prevent the `free` related errors
as defined in @sec-memsafe.

Together, another interpretations of `ST` is that it behaves like a scope:
`STRef` s are only usable within the scope. This usability
is enforced by the type checker.

=== Lifetimes

Sadly, `ST` cannot be used as-is. One important pattern we'd like
to support is to freely allow a longer lived allocation to be used
where shorter a shorter lived allocation is expected. As demonstrated,
references in `ST`s are mutually exclusive. We'll have modify
`ST` such that they can have associated _subscopes_, and
a way to use this relation to shorten the lifetime of reference
from the parent scope into the lifetime of the subscope.

In order to support the sharing of references between subscopes
Rust treats lifetimes types with a _subtyping_ relationship @rust-subtyping-variance.
Using subtyping means these relationships are worked without automatically, and
a reference with longer lifetime can be used, without any extra
syntax, where shorter lifetimes are expected. Idris does not
explicitly feature subtyping. However, the combination of dependent
types and `auto` implicits allows programs to be written in
a similar way. Lifetimes and the type for subscoping
relations are described in @sec-lifetimes-impl.

== Preventing out of bounds access <sec-oob>

Another design goal is preventing out-of-bounds and uninitialized memory access.
This requires two separate pieces:
- Ensuring the correct amount of memory is allocated.
- Reading and writing to that memory in a controlled manner.

The `CType : Type -> Type` GADT is responsible for the former.
It behaves like a sealed interface @java-sealed restricting the set of Idris types
which need to be handled by FFI-related functions. In a Curry-Howard perspective
`CType a` is proposition that the type `a` can be represented in C.
The `CType a` itself does not specify what this representation is. Rather, the
representations are provided by functions such as `sizeof`, `alignof`,
and `Marshal`.  Ultimately this design means specifying valid C types and
allocating them can be done in plain Idris, without supporting code for each
possible C type (eg. each different `typdef`-ed `struct`).

Inspired by Haskell's `Storable` @haskell-ffi, the
`Marshal` and `Unmarshal` types are responsible for controlling memory access.
`Marshal` corresponds to memory writes, and Haskell's `poke`, while
`Unmarshal` corresponds to memory reads and Haskell's `peak`.

#figure(
  ```haskell
  -- haskell storable
  class Storable a where
    sizeOf      :: a -> Int
    alignment   :: a -> Int

    peekElemOff :: Ptr a -> Int      -> IO a
    pokeElemOff :: Ptr a -> Int -> a -> IO ()

    peekByteOff :: Ptr a -> Int      -> IO a
    pokeByteOff :: Ptr a -> Int -> a -> IO ()

    peek        :: Ptr a             -> IO a
    poke        :: Ptr a        -> a -> IO ()

    destruct    :: Ptr a             -> IO ()
  ```,
  caption: [
    The Haskell `Storable` typeclass from @haskell-ffi-proposal.
    Note that as a typeclass, each FFI-boundary-crossing
    type needs to implement it. That is, any programmer
    wishing to make a type cross FFI boundaries needs
    to write code making direct memory accesses.
  ]
)

== Leveraging dependent types and `auto` implicit search

One of the main developments of this work is that
this library employs `auto` implicit search for generating `Marshal`
instances for compound types (ie. `struct`) on the fly by
the compiler. This is an improvement over existing
techniques which require external tools for generating
this "glue" code (see @sec-related-boilerplate).

Additionally, dependent types are used throughout to define
memory safety properties which the compiler can verify.

= Implementation

== Preamble

Idris provides some types supporting FFI, namely the pointers `Ptr a` and
and `AnyPtr`, and `Struct`. Firstly I'll redefine the the
pointer types for clarity. The `[external]` pragma makes these
_phantom types_. Since they don't have constructors Idris
may make assumptions that a `Ptr a` and an `AnyPtr` have no
inhabitants (as in `Falsity`); with `[external]`, Idris
treats these types as inhabitable but _opaque_. `Ptr`
is the type of addresses, or _pointers_, which
point to the type `a` in memory. `AnyPtr`
is simply a memory address with no assumptions about
the pointee; this is equivalent to `void*` in C.

  ```idris
  public export
  data Ptr : Type -> Type where [external]

  public export
  data AnyPtr : Type where [external]
  ```

Next, `Struct`s are defined. Again, this is a phantom
type, which will be represented in Idris as a pointer to the
heap allocation of the `Struct`. That is, a variable of
type `Struct "t" [("f", Int)]` will contain
a memory address to a heap allocated `struct t`.
This may seem odd since the type is `Struct` and
not `Ptr (Struct ...)`, but this _boxing_ @box of
values is a common practice in function programming languages;
it is needed here because Idris does not expose the local variable stack.

/*
Since
all C types will be heap allocated, only pointers
to values of these types should exist in Idris code,
not the values themselves.
#footnote[This is a convenient lie
for now. In `safeFFI` we'll use non-pointed-to `CArray`
and `Struct` to tell the codegen backend that a
function needs to dereference the underlying pointer].
*/


```idris
public export
data Struct : String -> List (String, Type) -> Type where [external]
```

`Struct` is a dependent type indexed by a `String`, the
C `struct`'s name, and a list of fields. Fields have
a `String` field name and a `Type`. The `Struct`'s name and field names
won't be used here but it serves as documentation and a way
of differentiating between `Struct`s with similar types.

/* idris
public export
data CArray : Int -> Type -> Type where [external]

public export
data Float : Type where [external]

public export
data FFIFn : Type -> Type

public export
data Lifetime : Type

public export
data Ref : Lifetime -> Type -> Type
*/

== Allocation

The polymorphic types above have one major flaw; _any_ Idris can
be accepted where a `Type` is required. For example
`Struct "list" [("t", Type), ("values", AnyPtr)]`
is a valid Idris type, but C does not have a `Type` type because is not
even polymorphic! Thus `CType a` will serve as a proposition
than a type `a` can be represented in C. Its limited set of
constructors then serve as proofs that a limited set of `a`s
can be represented in C. This limited set can be
split into primitives like, `CInt` and `CDouble` and recursive
constructors `CPtr`, and `CStruct`.

More concretely, `CInt` is a proof that `Int` has a C representation.
The recursive definitions similarly state that, for example, given
a proof that some type `t` has a C representation, `Ptr t` has
a C representation.

The `CStruct` constructor uses the `All` list quantifier to
represent a proof of all fields in a `Struct` having proofs of C representation
(ie. `CType a` for all field types `a`).
This, in turn, can be used to prove that the `Struct` has a C representation.

For brevity, the rest of this section will only consider the types `Int`, `Double`,
`Ptr a` and `Struct name fields` as C types. But this can be extended to a
full range of C types including sized signed and unsigned integers, arrays,
and function types.

```idris
public export
data CType : Type -> Type where
  CInt    : CType Int
  CDouble : CType Double
  CPtr    : CType t -> CType (Ptr t)
  CStruct : All (CType . Builtin.snd) fields -> CType (Struct name fields)
```

/* idris
  CCArray  : (n : Int) -> CType t -> CType (CArray n t)
  CFloat : CType Float

  CBool : CType Bool

  CInt8  : CType Int8
  CInt16 : CType Int16
  CInt32 : CType Int32
  CInt64 : CType Int64

  CBits8  : CType Bits8
  CBits16 : CType Bits16
  CBits32 : CType Bits32
  CBits64 : CType Bits64

  CVoidPtr : CType AnyPtr
  CFnPtr   : FFIFn t -> CType (Ptr t)
*/

With the C types defined, the functions which actually define the representation
(ie. their size and alignment) can be defined. These can then be used for
allocation and deallocation.

```idris
sizeof  : (repr : CType a) -> Int64
alignof : (repr : CType a) -> Int64

alloc : (repr : CType a) -> IO (Ptr a)
free  : Ptr a -> IO ()

```

/* idris
alignof CInt       = 4
alignof CFloat     = 4
alignof CDouble    = 8
alignof CBool      = 1
alignof CInt8      = 1
alignof CInt16     = 2
alignof CInt32     = 4
alignof CInt64     = 8
alignof CBits8     = 1
alignof CBits16    = 2
alignof CBits32    = 4
alignof CBits64    = 8
alignof (CPtr _)   = 8
alignof (CVoidPtr) = 8
alignof (CFnPtr _) = 8
alignof (CCArray _ repr) = alignof repr
alignof (CStruct reprs)  = go reprs 1
  where
  go : All (CType . Builtin.snd) fields' -> Int64 -> Int64
  go Nil aln = aln
  go (x::xs) aln = go xs (max aln $ alignof x)

sizeof CInt             = 4
sizeof CFloat           = 4
sizeof CDouble          = 8
sizeof CBool            = 1
sizeof CInt8            = 1
sizeof CInt16           = 2
sizeof CInt32           = 4
sizeof CInt64           = 8
sizeof CBits8           = 1
sizeof CBits16          = 2
sizeof CBits32          = 4
sizeof CBits64          = 8
sizeof (CPtr _)         = 8
sizeof (CVoidPtr)       = 8
sizeof (CFnPtr _)       = 8
sizeof (CCArray n repr) = (cast n) * sizeof repr
sizeof (CStruct reprs)  =
  fst $ go reprs (0, 1)
  where
  -- https://github.com/libffi/libffi/blob/c93f9428d17cde4eb35517b58feeae6fb43aba5b/include/ffi_common.h#L118
  doAlign : Int64 -> Int64 -> Int64
  doAlign v a = ((v-1) .|. (a-1))+1

  -- https://github.com/libffi/libffi/blob/c93f9428d17cde4eb35517b58feeae6fb43aba5b/src/prep_cif.c#L38
  go : All (CType . Builtin.snd) fields' -> (Int64, Int64) -> (Int64, Int64)
  go Nil (siz, aln) = (doAlign siz aln, aln) -- add padding to the end of the struct
  go (x::xs) (siz, aln) =
    let alnx = alignof x
    in go xs
      ( (+)                -- the current total size is the sum of
        (doAlign siz alnx) -- * padding after previous field
        (sizeof x)         -- * size of this field
      , max aln alnx       -- maximum alignment
      )

public export
data FFIFn : Type -> Type where
  CFReturn     : CType t -> FFIFn (PrimIO t)
  CFReturnVoid : FFIFn (PrimIO ())
  CFParam : CType t -> FFIFn rest -> FFIFn (t -> rest)

%foreign "scheme:foreign-alloc"
prim__malloc : Int64 -> PrimIO AnyPtr


alloc repr = map prim__castPtr $ primIO $ prim__malloc (sizeof repr)

%foreign "scheme:foreign-free"
prim__free : AnyPtr -> PrimIO ()

free ptr = primIO $ prim__free $ prim__forgetPtr ptr

*/

== Lifetime and subscopes <sec-lifetimes-impl>

Lifetimes are implemented as a wrapper around the `s : Type` of `ST`.
The two constructors reflect the two ways of running
our desired scoped computation: it can run at the top level
`runScopedIO`, or it can run within a subscope `runSubScopedIO`
where the constructor references a parent scope.

```idris
public export
data Lifetime : Type where
  LRoot : (0 thr : Type) -> Lifetime
  LSub  : (0 thr : Type) -> (0 _ : Lifetime) -> Lifetime
```

The hiearnchy implicit in `Lifetime` is not enough to fully reason
about them. Another type `AtLeastAsLong` is needed, representing the proposition
that a lifetime `a'` is at least as long as `b'`. A proof of this propposition
can then be used to shorten a `Ref a'` into the shorter-lived `Ref b'`.
`AtLeastAsLong` type has two constructors
representing base cases and one recursive case. The base cases
are `ALALSame`, which serves as proof that a lifetime
is at least as long as itself, and `ALALParent`, which servers as
proof that a lifetime `a'` is at least as long as a direct descendant
of itself. Lastly, the recursive `ALALTrans` admits a transitive property
for the `AtLeastAsLong` relation.

```idris
public export
data AtLeastAsLong : Lifetime -> Lifetime -> Type where
  ALALSame   : AtLeastAsLong a' a'
  ALALParent : AtLeastAsLong a' (LSub b a')
  ALALTrans  : AtLeastAsLong a' b' -> AtLeastAsLong b' c' -> AtLeastAsLong a' c'
```

== Marshal/Unmarshal <sec-marshal>

The `Marshal` type is inspired by the `poke` function
in Haskell's `Storable` @haskell-ffi. They both take a pointer to a
C allocation, host value, and execute a side-effecting computation.
However, there a few differences. Primarily, in `Marshal` the
Idris type and C type do not have to be the same. This is necessary
for enforcing memory safety: `Ref a' a` can be marshaled into a
`Ptr a` without actually realizing the `Ptr a`. That is, it's written
to memory through a `Ptr (Ptr a)`. This is an important property, because
it means a programmer cannot stumble into a function which
creates a pointer from a reference #footnote[This functionality _is_ provided
but with an apt warning in the name: `unsafeRefPtr`]; this conversion
does have to happen but can be safely encapsulated inside
a `Marshal` instance and not exposed to the programmer.

Unmarshal follows in a similar manner. However, as a design choice,
unmarshaling of structures is not provided. The motivation behind
this decision is that entire structures should be passed around
as `Ref`s. Bringing the entire value into Idris suggests, incorrectly, that
they will be kept up to date according to the backing data, which is not
possible nor safe.

/* idris
export
%unsafe
unsafeRefPtr : Ref a' t -> Ptr t
unsafeRefPtr = believe_me

export
%unsafe
unsafePtrRef : Ptr t -> Ref a' t
unsafePtrRef = believe_me

%foreign "scheme: (lambda (a b) (+ a b))"
prim__offsetPtr : AnyPtr -> Int64 -> AnyPtr

%foreign "scheme:(lambda (erased x) (car x))"
prim__gcptrDeref : GCPtr a -> Ptr a

cgPtrWrite : Int -> String
cgPtrWrite bits = """
scheme:
(lambda (ptr value)
  (foreign-set! 'unsigned-\{ show bits } ptr 0 value)
  \{ show $ bits `div` 8 }

)
"""

%foreign (cgPtrWrite 8)
prim__ptrWrite8 : AnyPtr -> Bits8 -> PrimIO Int64

%foreign (cgPtrWrite 16)
prim__ptrWrite16 : AnyPtr -> Bits16 -> PrimIO Int64

%foreign (cgPtrWrite 32)
prim__ptrWrite32 : AnyPtr -> Bits32 -> PrimIO Int64

%foreign (cgPtrWrite 64)
prim__ptrWrite64 : AnyPtr -> Bits64 -> PrimIO Int64


cgPtrRead : Int -> String
cgPtrRead bits = """
scheme:
(lambda (ptr) (foreign-ref 'unsigned-\{ show bits }  ptr 0))
"""

%foreign (cgPtrRead 8)
prim__ptrRead8 : AnyPtr -> PrimIO Bits8

%foreign (cgPtrRead 16)
prim__ptrRead16 : AnyPtr -> PrimIO Bits16

%foreign (cgPtrRead 32)
prim__ptrRead32 : AnyPtr -> PrimIO Bits32

%foreign (cgPtrRead 64)
prim__ptrRead64 : AnyPtr -> PrimIO Bits64

%foreign """
scheme:
(lambda (x)
  (let
    ([ptr (foreign-alloc (ftype-sizeof float))])
    (foreign-set! 'single-float ptr 0 x)
    (let
      ([ret (foreign-ref 'unsigned-32 ptr 0)])
      (foreign-free ptr)
      ret
    )
  )
)
"""
prim__SingleToBits : Double -> Bits32

%foreign """
scheme:
(lambda (x)
  (let
    ([ptr (foreign-alloc (ftype-sizeof double))])
    (foreign-set! 'double-float ptr 0 x)
    (let
      ([ret (foreign-ref 'unsigned-64 ptr 0)])
      (foreign-free ptr)
      ret
    )
  )
)
"""
prim__DoubleToBits : Double -> Bits64

%foreign """
scheme:
(lambda (x)
  (let
    ([ptr (foreign-alloc (ftype-sizeof float))])
    (foreign-set! 'unsigned-32 ptr 0 x)
    (let
      ([ret (foreign-ref 'single-float ptr 0)])
      (foreign-free ptr)
      ret
    )
  )
)
"""
prim__SingleFromBits : Bits32 -> Double

%foreign """
scheme:
(lambda (x)
  (let
    ([ptr (foreign-alloc (ftype-sizeof double))])
    (foreign-set! 'unsigned-64 ptr 0 x)
    (let
      ([ret (foreign-ref 'double-float ptr 0)])
      (foreign-free ptr)
      ret
    )
  )
)
"""
prim__DoubleFromBits : Bits64 -> Double

prim__PtrToBits : AnyPtr -> Bits64
prim__PtrToBits = believe_me

prim__PtrFromBits : Bits64 -> AnyPtr
prim__PtrFromBits = believe_me
*/

#figure(
```idris
public export
data Marshal
  : Lifetime -> ity -> cty -> Type where
  MkMarshal :
    { auto repr : CType cty } ->
    (ity -> Ptr cty -> IO Int64) -> Marshal a' ity cty

export
%hint
marshalInt : Marshal a' Int Int
marshalInt = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite32 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalDouble : Marshal a' Double Double
marshalDouble = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite64 (prim__forgetPtr ptr) (prim__DoubleToBits x)

export
%hint
marshalRef :
  { auto repr : CType t } ->
  Marshal a' (Ref a' t) (Ptr t)
marshalRef = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite64
      (prim__forgetPtr ptr)
      (prim__PtrToBits $ prim__forgetPtr $ unsafeRefPtr x)
```,
  caption: [
    `Marshal` and non-recursive instances. The actual implementations are provided
    for demonstration. In these functions, `x` is the value to be written,
    and `ptr` is a pointer to the location they should be written to.
    These function ultimately end up writing to a raw pointer.
  ]
)

#figure(
```idris
export
%hint
marshalStructBase :
  { 0 ia : Type } ->
  { auto repr : CType ca} ->
  Marshal a' ia ca ->
  Marshal a' ia (Struct name [(f, ca)])

export
%hint
marshalStructRec :
  { auto repr : CType ca } ->
  { auto reprs : All (CType . Builtin.snd) cb } ->
  Marshal a' ia ca ->
  Marshal a' ib (Struct name cb) ->
  Marshal a' (Pair ia ib) (Struct name ((field, ca)::cb))
```,
  caption: [
    Recursive instances of `Marshal` for structs. Their implementations are not
    given here due to space constraints, but can be found in @code-marshal.
    In short, `marshalStructRec` writes one field
    to the destination, calculates an offset for the next field, while considering
    alignment, and recurses on the `Marshal` for the other fields (either a `marshalStructRec`
    or a `marshalStructBase`).
  ],
)


#figure(
```idris
public export
data Unmarshal
  : Lifetime -> ity -> cty -> Type where
  MkUnmarshal :
    { auto repr : CType cty } ->
    (Ptr cty -> IO ity) -> Unmarshal a' ity cty

export
%hint
unmarshalInt : Unmarshal a' Int Int

export
%hint
unmarshalDouble : Unmarshal a' Double Double
```,
  caption: [`Unmarshal` and instances],
)

/* idris

export
%hint
marshalInteger : Marshal a' Integer Int
marshalInteger = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite32 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalFloat : Marshal a' Double Float
marshalFloat = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite32 (prim__forgetPtr ptr) (cast $ prim__SingleToBits x)


export
%hint
marshalPtr : CType t => Marshal a' (Ptr t) (Ptr t)
marshalPtr = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite64 (prim__forgetPtr ptr) (prim__PtrToBits $ prim__forgetPtr x)

export
%hint
marshalGCPtr : CType t => Marshal a' (GCPtr t) (Ptr t)
marshalGCPtr = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite64 (prim__forgetPtr ptr) (prim__PtrToBits $ prim__forgetPtr $ prim__gcptrDeref x)

export
%hint
marshalBool : Marshal a' Bool Bool
marshalBool = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite8 (prim__forgetPtr ptr) (if x then 1 else 0)

export
%hint
marshalInt8 : Marshal a' Int8 Int8
marshalInt8 = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite8 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalInt16 : Marshal a' Int16 Int16
marshalInt16 = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite16 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalInt32 : Marshal a' Int32 Int32
marshalInt32 = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite32 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalInt64 : Marshal a' Int64 Int64
marshalInt64 = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite64 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalBits8 : Marshal a' Bits8 Bits8
marshalBits8 = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite8 (prim__forgetPtr ptr) x

export
%hint
marshalBits16 : Marshal a' Bits16 Bits16
marshalBits16 = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite16 (prim__forgetPtr ptr) x

export
%hint
marshalBits32 : Marshal a' Bits32 Bits32
marshalBits32 = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite32 (prim__forgetPtr ptr) x

export
%hint
marshalBits64 : Marshal a' Bits64 Bits64
marshalBits64 = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite64 (prim__forgetPtr ptr) x

-- integer instances

export
%hint
marshalInt8Integer : Marshal a' Integer Int8
marshalInt8Integer = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite8 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalInt16Integer : Marshal a' Integer Int16
marshalInt16Integer = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite16 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalInt32Integer : Marshal a' Integer Int32
marshalInt32Integer = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite32 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalInt64Integer : Marshal a' Integer Int64
marshalInt64Integer = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite64 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalBits8Integer : Marshal a' Integer Bits8
marshalBits8Integer = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite8 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalBits16Integer : Marshal a' Integer Bits16
marshalBits16Integer = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite16 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalBits32Integer : Marshal a' Integer Bits32
marshalBits32Integer = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite32 (prim__forgetPtr ptr) (cast x)

export
%hint
marshalBits64Integer : Marshal a' Integer Bits64
marshalBits64Integer = MkMarshal $ \x, ptr =>
    primIO $ prim__ptrWrite64 (prim__forgetPtr ptr) (cast x)

(.ctype) : Marshal a' ity cty -> CType cty
(.ctype) (MkMarshal { repr } _) = repr

padto : AnyPtr -> CType a -> Int64
padto ptr repr =
  let ptrBits = the Int64 $ believe_me ptr
  in cast $ (doAlign (cast ptrBits) (cast $ alignof repr)) - (cast ptrBits)
  where
  -- https://github.com/libffi/libffi/blob/c93f9428d17cde4eb35517b58feeae6fb43aba5b/include/ffi_common.h#L118
  doAlign : Bits64 -> Bits64 -> Bits64
  doAlign v a = ((v-1) .|. (a-1))+1

marshalStructBase ma = MkMarshal $ \x, ptr =>
  let MkMarshal f = ma
  in f x (prim__castPtr $ prim__forgetPtr ptr)

marshalStructRec ma mb = MkMarshal $ \(a, bs), ptr => do
  let anyptr = prim__forgetPtr ptr
  let pad = padto anyptr ma.ctype
  let MkMarshal maf = ma
  let MkMarshal mbf = mb
  siz <- (+ pad) <$> maf a (prim__castPtr $ prim__offsetPtr anyptr pad)
  (+ siz) <$> mbf bs (prim__castPtr $ prim__offsetPtr anyptr $ cast siz)

%foreign "C:memcpy,libc"
prim__memcpy : AnyPtr -> AnyPtr -> Int64 -> PrimIO AnyPtr

export
%hint
marshalDerefStructPtr:
  { auto reprs : All (CType . Builtin.snd) fields } ->
  Marshal a' (Ptr (Struct name fields)) (Struct name fields)
marshalDerefStructPtr = MkMarshal $ \x, ptr => do
  let len = sizeof (CStruct { name } reprs)
  _ <- primIO $ prim__memcpy (prim__forgetPtr ptr) (prim__forgetPtr x) len
  pure len

export
%hint
marshalDerefStructRef:
  { auto reprs : All (CType . Builtin.snd) fields } ->
  Marshal a' (Ref a' (Struct name fields)) (Struct name fields)
marshalDerefStructRef = MkMarshal $ \x, ptr => do
  let MkMarshal f = marshalDerefStructPtr { a' }
  f (unsafeRefPtr x) ptr

export
%hint
marshalAnyPtr: Marshal a' AnyPtr AnyPtr
marshalAnyPtr = MkMarshal $ \x, ptr =>
  primIO $ prim__ptrWrite64 (prim__forgetPtr ptr) (prim__PtrToBits x)


export
%hint
marshalFnPtr: FFIFn t -> Marshal a' (Ptr t) (Ptr t)
marshalFnPtr _ = MkMarshal $ \x, ptr => do
  let MkMarshal f = marshalAnyPtr { a' }
  f (prim__forgetPtr x) (prim__castPtr $ prim__forgetPtr ptr)

*/

/* idris
unmarshalInt = MkUnmarshal $ \ptr =>
  map cast $ primIO $ prim__ptrRead32 (prim__forgetPtr ptr)

unmarshalDouble = MkUnmarshal $ \ptr =>
  map prim__DoubleFromBits $ primIO $ prim__ptrRead64 (prim__forgetPtr ptr)

export
%hint
unmarshalFloat : Unmarshal a' Double Float
unmarshalFloat = MkUnmarshal $ \ptr =>
  map prim__SingleFromBits $ primIO $ prim__ptrRead32 (prim__forgetPtr ptr)

export
%hint
unmarshalPtr : CType t => Unmarshal a' (Ptr t) (Ptr t)
unmarshalPtr = MkUnmarshal $ \ptr =>
  map (prim__castPtr . prim__PtrFromBits) $ primIO $ prim__ptrRead64 (prim__forgetPtr ptr)


export
%hint
unmarshalBool : Unmarshal a' Bool Bool
unmarshalBool = MkUnmarshal $ \ptr =>
  map (/= 0) $ primIO $ prim__ptrRead8 (prim__forgetPtr ptr)

export
%hint
unmarshalBits8 : Unmarshal a' Bits8 Bits8
unmarshalBits8 = MkUnmarshal $ \ptr =>
  primIO $ prim__ptrRead8 (prim__forgetPtr ptr)

export
%hint
unmarshalBits16 : Unmarshal a' Bits16 Bits16
unmarshalBits16 = MkUnmarshal $ \ptr =>
  primIO $ prim__ptrRead16 (prim__forgetPtr ptr)

export
%hint
unmarshalBits32 : Unmarshal a' Bits32 Bits32
unmarshalBits32 = MkUnmarshal $ \ptr =>
  primIO $ prim__ptrRead32 (prim__forgetPtr ptr)

export
%hint
unmarshalBits64 : Unmarshal a' Bits64 Bits64
unmarshalBits64 = MkUnmarshal $ \ptr =>
  primIO $ prim__ptrRead64 (prim__forgetPtr ptr)

export
%hint
unmarshalInt8 : Unmarshal a' Int8 Int8
unmarshalInt8 = MkUnmarshal $ \ptr =>
  map cast $ primIO $ prim__ptrRead8 (prim__forgetPtr ptr)

export
%hint
unmarshalInt16 : Unmarshal a' Int16 Int16
unmarshalInt16 = MkUnmarshal $ \ptr =>
  map cast $ primIO $ prim__ptrRead16 (prim__forgetPtr ptr)

export
%hint
unmarshalInt32 : Unmarshal a' Int32 Int32
unmarshalInt32 = MkUnmarshal $ \ptr =>
  map cast $ primIO $ prim__ptrRead32 (prim__forgetPtr ptr)

export
%hint
unmarshalInt64 : Unmarshal a' Int64 Int64
unmarshalInt64 = MkUnmarshal $ \ptr =>
  map cast $ primIO $ prim__ptrRead64 (prim__forgetPtr ptr)
*/

== Scoped allocations <sec-scopedio-scope>

The `ScopedIO` monad can now be defined. The constructor
is convoluted, but in short: it is a wrapper around `IO`,
the type representing functions with side effects,
returning some `a` paired with a list of clean up functions
`List (IO ())`. An early implementation considered
returning a list of pointers for `free` to be called on.
However, it is often the case that additional code needs
to run before `free`-ing an object, this is known
as a _destructor_ @destructor-paper and part of a C++
design pattern called "resource acquisition is initialization" (RAII). Rust
captures this concept with the `Drop` @rust-drop trait.
In `System.ScopedIO`, a primitive function `defer` allows
programmers to add arbitrary actions to the scope which
will run at its end. `defer` is used in a following
section to build something the more closely resembles
destructors, `safeFFIDrop`.

`runScopedIO` looks similar to `runST`, but with a `Lifetime`
instead of arbitrary `Type`. Additionally there is a
`runSubScopedIO` which passes a proof of the subscope relationship,
a `AtLeastAsLong`, which can be used to `readRef` from the outer
scope.

=== Getting struct fields

As mentioned, reading entire `Struct`s is not supported. Instead
a `Ref` to a struct can be _projected_ to a `Ref` of one of its
fields. This requires a new type `Field` representing a
proposition that an `fname : String` is a valid field of the
struct. Additionally, a type level function `FieldType` uses a
proof of the proposition to extract the type of the field.
Note that `Field` is provided to `getField` as an `auto` implicit,
so when calling `getField` the proof of `Field` rarely has to be provided.


#figure(
columns(2)[
```idris
export
data ScopedIO : Lifetime -> Type -> Type where
  MkScopedIO :
    IO (Pair (List (IO ())) a) ->
    ScopedIO a' a

public export
data Ref : Lifetime -> Type -> Type where [external]

public export
runScopedIO :
  HasIO io =>
  ((0 a' : Lifetime) -> ScopedIO a' a) ->
  io a

public export
runSubScopedIO :
  (0 a' : Lifetime) ->
  (
    (0 b' : Lifetime) ->
    (0 p : AtLeastAsLong a' b') ->
    ScopedIO b' a
  ) -> ScopedIO a' a
```

#colbreak()

```idris
public export
newRef :
  { auto m : Marshal a' ity cty } ->
  ity ->
  ScopedIO a' (Ref a' cty)

public export
writeRef :
  { auto m : Marshal a' ity cty } ->
  ity -> Ref a' cty ->
  ScopedIO a' Int64

public export
readRef :
  { auto unm : Unmarshal a' ity cty } ->
  { auto 0 p : AtLeastAsLong a' b' } ->
  Ref a' cty ->
  ScopedIO b' ity

export
defer : IO () -> ScopedIO a' ()
```
],
  placement: auto,
  caption: [
    The full API for allocating, reading, writing, and automatically
    deallocating memory needed to do FFI
  ],
)

/* idris
export
Functor (ScopedIO a')

export
Applicative (ScopedIO a')

export
Monad (ScopedIO a')

export
HasIO (ScopedIO a')
*/

/* idris
-- NOTE: can't defined runScopedIO yet because Lifetime constructors
-- haven't been defined

Functor (ScopedIO a') where
  map f (MkScopedIO x) = MkScopedIO $ map f <$> x

Applicative (ScopedIO a') where
  pure x = MkScopedIO $ pure $ pure x

  (<*>) (MkScopedIO f) (MkScopedIO sf) = MkScopedIO [| f <*> sf |]

Monad (ScopedIO a') where
  join (MkScopedIO x) = MkScopedIO $ do
    (state', MkScopedIO x') <- x
    (state'', x'') <- x'
    pure (state'' <+> state', x'')

HasIO (ScopedIO a') where
  liftIO x = MkScopedIO $ map (neutral,) x
*/

/* idris


runScopedIO f = do
  let MkScopedIO f' = f $ LRoot Unit
  (cleanup, ret) <- liftIO f'
  liftIO $ sequence_ cleanup
  pure ret

runSubScopedIO a' f = do
  let MkScopedIO f' = f (LSub Unit a') ALALParent
  (cleanup, ret) <- liftIO f'
  liftIO $ sequence_ cleanup
  pure ret

newRef ity = do
  let MkMarshal { repr } f = m
  ret <- liftIO $ alloc repr
  _ <- liftIO $ f ity ret
  defer (free ret)
  pure $ unsafePtrRef ret

readRef @{ MkUnmarshal f } ref = liftIO $ f (unsafeRefPtr ref)

export
shortenRef :
  (0 b' : Lifetime) ->
  Ref a' cty ->
  { auto 0 p : AtLeastAsLong a' b' } ->
  Ref b' cty
shortenRef _ ref = believe_me ref

defer f = MkScopedIO $ pure ([f], ())
*/


#figure(
```idris
public export
data Field : String -> List (String, Type) -> Type where
  First : Field name ((name, ty)::fs)
  Later : Field name fs -> Field name (f::fs)

public export
0 FieldType : Field fname fs -> Type
FieldType (First { ty }) = ty
FieldType (Later l) = FieldType l

public export
getField :
  { auto reprs : All (CType . Builtin.snd) fields } ->
  Ref a' (Struct name fields) -> (fname : String) ->
  { auto f : Field fname fields } ->
  Ref a' (FieldType f)
```,
  caption: [The API for accessing `Struct` fields through a `Ref`. `Field` i],
)

/* idris
getField ref fname =
  unsafePtrRef $ prim__castPtr $ offset (prim__forgetPtr $ unsafeRefPtr ref) reprs f
  where
  offset :
    AnyPtr ->
    All (CType . Builtin.snd) fields' ->
    (_ : Field fname' fields') ->
    AnyPtr
  offset ptr (r::rs) (Later f) =
    let ptr' = prim__offsetPtr ptr $ (sizeof r) + (padto ptr r)
    in offset ptr' rs f
  offset ptr (r::_)  First    = prim__offsetPtr ptr (padto ptr r)
*/

/* idris
public export
0 Ptr2Ref : (a' : Lifetime) -> Type -> Type
Ptr2Ref a' (Ptr t) = Ref a' t
Ptr2Ref a' t = Ref a' t

export
getPtr :
  HasIO io =>
  { auto repr : CType t } ->
  Ref a' (Ptr t) ->
  io (Ref a' t)
-- point free steez
getPtr =
  map
    (unsafePtrRef . prim__castPtr . prim__PtrFromBits)
    .
    (primIO . prim__ptrRead64 . prim__forgetPtr . unsafeRefPtr)
*/

== Shimming existing FFI

There is one last problem to be solved. There are some misalignment
between `CType`s and the existing expectations of FFI. For example,
functions returning C's `void` are represented in Idris as returning `()`.
`()` should not be a valid `CType` since C does not
have tuples, nor should `void` as it cannot be field in a `struct`.
Another example is `Ref`s, with `Ref`s to `Struct`s being
particularly problematic: plain `Struct`s cannot be created
so a compiler backend intrinsic `prim__derefStruct` is necessary.
Recall that Idris does not give us access to the local variable stack,
so `prim__derefStruct` does not really do a dereference, the underlying
value is still a pointer. However, the plain `Struct` Idris type signals
to the backend that the _generated code_ should dereference
the pointer prior to making the function call to C, when the
stack can be accessed.

This shimming is done via the `FFICall` type, representing
yet another proposition. `FFICall` is a proposition that a
list of arguments can be used to call a function; the proofs
have slightly different types, ie. `Ref _ (Struct ...)` can
be provided to a function `Struct ... -> ...`.
This type is used in `safeFFI` function, again as an `auto` implicit,
to _shim_ or adjust the function call accordingly.

#figure(
columns(2)[
```idris
public export
data FFICall
  : (0 a' : Lifetime) ->
    List Type ->
    (fty : Type) ->
    Type where [search fty]

  FCReturn :
    { b : Type } ->
    CType b =>
    FFICall a' [] (PrimIO b)

  FCReturnVoid :
    FFICall a' [] (PrimIO ())

  FCSame :
    CType a =>
    FFICall a' args f ->
    FFICall a' (a::args) (a -> f)

  FCRefPtr :
    CType a =>
    FFICall a' args f ->
    FFICall a' ((Ref a' a)::args) (Ptr a -> f)

  FCDerefStructRef :
    All (CType . Builtin.snd) fields =>
    FFICall a' args f ->
    FFICall a' ((Ref a' (Struct name fields))::args) (Struct name fields -> f)
```
/* idris
  FCInteger :
    CType a =>
    Cast Integer a =>
    FFICall a' args f ->
    FFICall a' (Integer::args) (a -> f)

  FCDerefStructPtr :
    All (CType . Builtin.snd) fields =>
    FFICall a' args f ->
    FFICall a' ((Ptr (Struct name fields))::args) (Struct name fields -> f)

  FCGCPtr :
    CType a =>
    FFICall a' ((Ptr a)::args) f ->
    FFICall a' ((GCPtr a)::args) f
*/


#colbreak()

```idris
public export
FFICallRet : FFICall a' args f -> Type
FFICallRet (FCReturn { b }) = b
FFICallRet (FCReturnVoid) = ()
FFICallRet (FCSame rest) = FFICallRet rest
FFICallRet (FCRefPtr rest) = FFICallRet rest
FFICallRet (FCDerefStructRef rest) = FFICallRet rest
```

/* idris
FFICallRet (FCGCPtr rest) = FFICallRet rest
FFICallRet (FCInteger rest) = FFICallRet rest
FFICallRet (FCDerefStructPtr rest) = FFICallRet rest
*/
],
  caption: [
    `FFICall` proposition type which defines the how each type is shimmed.
    And `FFICallRet` for extracting the return value from an `FFICall` proof.
    @fig-fficall-table below explains each construtor.
  ]
)

#figure(
```idris
-- NOTE: chez specific!!
prim__derefStruct : Ptr (Struct name fields) -> Struct name fields
prim__derefStruct = believe_me

-- sanity check that our ref has the expected lifetime
checkRef : Ref a' x -> ScopedIO a' ()
checkRef _ = pure ()

export
safeFFI :
  { auto call : FFICall a' args f } ->
  f -> HList args -> ScopedIO a' (FFICallRet call)
safeFFI = go call
  where
  go :
    (call' : FFICall a' args' f') ->
    f' -> HList args' -> ScopedIO a' (FFICallRet call')
  go FCReturn        f _        = primIO f
  go FCReturnVoid    f _        = primIO f
  go (FCSame rest)   f (a::arg) = go rest (f a) arg
  go (FCRefPtr rest) f (a::arg) = do
    _ <- checkRef a
    go rest (f $ unsafeRefPtr a) arg
  go (FCDerefStructRef rest) f (a::arg) = do
    _ <- checkRef a
    go rest (f $ prim__derefStruct $ unsafeRefPtr a) arg
```,
  caption: [
    `safeFFI`, a function for making FFI call safely. Note that
    it does not use normal function application syntax, instead it uses
    an `HList`. The `Return`-related definitions simply return the value
    as it exsits. While the definitions take an `a` out of the argument
    `HList` and apply it to the function `f`, after shimming the
    argument as needed.
  ]
)

#figure(
  table(
    columns: 4,
    table.header(
      [*cons name*],
      [*value given to foreign function*],
      [*value expected by foreign function*],
      [*notes*],
    ),

    [`FCReturn`],
      [n/a],
      [n/a],
      [A proof for functions returning C types],

    [`FCReturnVoid`],
      [n/a],
      [n/a],
      [
        A proof for functions returning `void` in C,
        and `()` in Idris
      ],

    [`FCSame`],
      [A C-representable type, `a`],
      [The same type `a`],
      [These arguments are the status quo for Idris FFI],

    [`FCRefPtr`],
      [A `Ref` to a C-representable type `a`],
      [A pointer to `a`],
      [
        Converts a `Ref` to a pointer and applies the function to the
        pointer. Note that the lifetime `a'` of the `Ref` is
        observed in the return type of `FFICall`. That is,
        this proof carries the lifetime of the `Ref` and is
        used by `safeFFI` to make sure all `Ref` arguments
        are valid for the scope.
      ],

    [`FCDerefStructRef`],
      [A `Ref` to a C-representable `Struct`],
      [A pointer to the `Struct`],
      [
        Signal to the backend the the underlying `Struct`
        pointer will need to be dereferenced before calling
        the foreign function.
      ],
  ),
  caption: [An easier to understand mapping table of of the `FFICall` constructors],
) <fig-fficall-table>

/* idris

  go (FCInteger rest) f (a::arg) = go rest (f $ cast a) arg
  go (FCDerefStructPtr rest) f (a::arg) = go rest (f $ prim__derefStruct a) arg
  go (FCGCPtr rest) f (a::arg) = go rest f ((prim__gcptrDeref a)::arg)
*/

== Destructors Redux

Above, `ScopedIO` ensures the memory we allocate into a scope is deallocated
at the end of the scope; and, that this memory cannot be accessed outside of the scope.
However, some objects will not be directly allocated in Idris. Rather,
a foreign library may provide a constructor function for both
allocating and initializing the object. This would also be paired
with destructor,  described above in @sec-scopedio-scope.
`defer` is not enough to safely handle this lifecycle because the value
returned from the foreign constructor (and then destructed)
can still be used at the end of the scope. However,
if the value returned by the foreign constructor is a
pointer, it can be used as a `Ref`, as if returned from `alloc`/`prim__malloc`.

Safe destruction in this way, is provided by `safeFFIDrop`. It is similar to `safeFFI`, but with
the following differences:
- It requires a destruction function.
- The FFI function must return a pointer; enforced with the `IsPtr` type.
- `safeFFIDrop`, then, returns a `Ref` to the pointed-to value.
One unsolved problem that is that calling the destructor
via `safeFFI` within the body of the scope results in a double-free at
the end of scope, when the automatic destructor is run. That is to say two
"safe" operations, one `safeFFIDrop` and one `safeFFI`, can result in
memory corruption. This issue is discussed in @sec-future-safe-destructors.

/* idris
data IsPtr : Type -> Type

-- 0 UnPtr : (a : Type) -> { auto 0 prf : IsPtr a } -> Type

-- TODO: chez specific!!
prim__ptrDeref : Ptr a -> a
prim__ptrDeref = believe_me

*/


#figure(
```idris
public export
data IsPtr : Type -> Type where
  MkIsPtr : IsPtr (Ptr a)

-- A type-level funtion returning the pointed-to type of a pointer
public export
0 UnPtr : (a : Type) -> { auto 0 prf : IsPtr a } -> Type
UnPtr _ =
  case prf of
    MkIsPtr { a = b } => b
    _ => assert_total $ idris_crash "unreachable!!"

unsafeIsPtrRef : a -> { auto prf : IsPtr a } -> Ref a' (UnPtr a)
unsafeIsPtrRef x =
  case prf of
    MkIsPtr => unsafePtrRef x

export
safeFFIDrop:
  { auto call : FFICall a' args f } ->
  { auto isptr : IsPtr (FFICallRet call) } ->
  f ->
  (drop : FFICallRet call -> IO ()) ->
  HList args ->
  ScopedIO a' (Ref a' (UnPtr (FFICallRet call)))
safeFFIDrop fn drop args = do
  ret <- safeFFI fn args
  defer (drop ret)
  pure $ unsafeIsPtrRef ret
```,
  caption: [
    The function `safeFFIDrop` and helpers `IsPtr` and `UnPtr`.
    `IsPtr` is used to prove the return value of the foreign function is
    a poiner. `UnPtr` isused for getting the pointed-to type when
    describing the new returned `Ref`.
  ],
)

/* idris


%foreign "C:memcpy,libc"
prim__memcpyStr : AnyPtr -> String -> Int64 -> PrimIO ()

export
stringRef : String -> ScopedIO a' (Ref a' Bits8)
stringRef s = do
  let len = strLength s
  ptr <- primIO $ prim__malloc . (+ 1) $ cast len
  defer (primIO $ prim__free ptr)
  primIO $ prim__memcpyStr ptr s (cast len)
  -- i loooooove c strings <3
  _ <- primIO $ prim__ptrWrite8 (prim__offsetPtr ptr (cast len)) 0
  pure $ unsafePtrRef $ prim__castPtr ptr


testNewRefInt : ScopedIO a' (Ref a' Int)
testNewRefInt = newRef 25

testNewRefStruct1 : ScopedIO a' (Ref a' (Struct "hello" [("f", Int)]))
testNewRefStruct1 = newRef (the Int 25)

testNewRefStruct2 : ScopedIO a' (Ref a' (Struct "hello" [("f", Int), ("g", Int)]))
testNewRefStruct2 = newRef ((the Int 25), (the Int 50))

testNewRefStruct3 : ScopedIO a' (Ref a'
  (Struct "hello"
    [("f", Int), ("g", Ptr Int)]))
testNewRefStruct3 = newRef ((the Int 25), !testNewRefInt)

testNewRefStruct4 : ScopedIO a' (Ref a'
  (Struct "hello"
    [ ("f", Int)
    , ( "g" , Struct "world"
        [ ("h", Int)
        , ("i", Ptr Int)
      ])
    ])
  )
testNewRefStruct4 = newRef ((the Int 25), (the Int 50, !testNewRefInt))

testNewRefStruct5 : ScopedIO a' (Ref a'
  (Struct "hello"
    [ ("f", Int)
    , ( "g" , Struct "world"
        [ ("h", Int)
        , ("i", Int)
      ])
    ])
  )
testNewRefStruct5 = do
  newRef
    ( 25
    , !(newRef
      { cty = Struct "world" [("h", Int), ("i", Int)] }
      ( 50
      , 75
      ))
    )

testScope1 : IO Int
testScope1 = runScopedIO $ \a' => do
  x <- newRef { cty = Int } $ the Int 10
  runSubScopedIO a' $ \b', _ => do
    readRef x

failing "Can't solve constraint"
  testScope2 : IO Int
  testScope2 = runScopedIO $ \a' => do
    x <- runSubScopedIO a' $ \b', _ => do
      newRef { cty = Int } $ the Int 10
    readRef x

failing "Can't solve constraint"
  testScope3 : IO Int
  testScope3 = runScopedIO $ \a' => do
    x <- runSubScopedIO a' $ \b', _ => do
      newRef { cty = Int } $ the Int 10
    runSubScopedIO a' $ \b', _ => do
      readRef x

TestStruct : Type
TestStruct = Struct "TestStruct"
  [ ("a", Bits8)
  , ("b", Bits16)
  , ("c", Bits32)
  , ("d", Bits64) ]

%foreign "C:printStruct,libffisafe_test"
printStruct : TestStruct -> PrimIO ()

test : IO ()
test = runScopedIO $ \a' => do
  x <- newRef { cty = TestStruct }
    ( the Bits8  101
    , the Bits16 10203
    , the Bits32 20405060
    , the Bits64 50404020205 )
  safeFFI printStruct [x]
  -- primIO $ printStruct $ prim__ptrDeref $ unsafeRefPtr x

export
autoCType : (a : Type) -> { auto x : CType a } -> CType a
autoCType _ = x

export
autoMarshal : (cty : Type) -> { auto x : Marshal a' ity cty } -> Marshal a' ity cty
autoMarshal _ = x

*/
