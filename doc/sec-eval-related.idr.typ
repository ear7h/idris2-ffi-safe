/* idris2

import Data.String
import Data.List.Quantifiers
import System.FFI

import System.ScopedIO
import Graphics.WGPU
import Graphics.WGPU.Sys

%hide System.FFI.Struct

prim__malloc : Int64 -> PrimIO AnyPtr
prim__free : AnyPtr -> PrimIO ()
prim__memcpyStr : AnyPtr -> String -> Int64 -> PrimIO ()

*/

= Evalutation <sec-eval>

This section evaluates if, and to what extent, the work herin achieves the goals enumerated
in @sec-intro:
1. Improving Idris' FFI (@sec-eval-scopedio)
// 2. Developing idiomadic bindings to `wgpu` (@sec-eval-wgpu)
3. Demonstrating how improvments of practical details can
   "trickle up" into research domains. (@sec-eval-edsl)

/*
@sec-eval-dx outlines how well  subjective evaluation
of `ScopedIO`, detailing the benefits and issues encountered while
developing of the demos and `Graphics.WGPU` library for this thesis.
In @sec-eval-memsafe, memory safety is evaluated by inspection and
using dynamic analysis to empirically verify memory safety
as defined in @sec-memsafe: no uninitialized reads, no out-of-bounds
accesses, and no use-after-free.
*/

A snippet of the demo program, `src/Examples/TriangeSys.idr`, mentioned throughout this section is in @code-render.

== `System.ScopedIO` Evaluation <sec-eval-scopedio>

`System.ScopedIO`, is evaluated with respect to:
- The functionality provided beyond Idris' current FFI.
- How strongly memory safety is maintained

=== FFI <sec-eval-dx>

Firstly, `ScopedIO` cannot entirely remove the need for generating Idris
code. Especially in a large library, such as `wgpu`, a script was needed
to translate the definitions of a C header file into equivalent definitions
in Idris. This results in a large Idris file which needs to be parsed,
typechecked, and tracked by version control. Anecdotally, Idris'
incremental compilation handled this gracefully, only recompiling
when the cache folder was deleted or a change to the file was made.
Other possible approaches, with various tradeoffs, for
automatically binding to C are described in @sec-related-boilerplate.

#figure(
```idris
testScope1 : IO Int
testScope1 = runScopedIO $ \a' => do
  x <- newRef { cty = Int } $ the Int 10
  runSubScopedIO a' $ \b', _ => do
    runSubScopedIO b' $ \c', _ => do
      readRef x

failing "Can't solve constraint"
  testScope2 : IO Int
  testScope2 = runScopedIO $ \a' => do
    x <- runSubScopedIO a' $ \b', _ => do
      newRef { cty = Int } $ the Int 10
    readRef x
```,
  caption: [
    A correct and incorrect usage of `ScopeIO` and `Ref`s. In `testScope1`,
    the outer `Ref`, `x`, is automatically shortened via `auto` implicit search
    of `AtLeastAsLong a' c'`. Such a proof is found for the `readRef` and it
    is immediately returned to the outer scope(s). In `testScope2`, the inner
    scope smuggles a `Ref` out of the scope, but fails to `readRef` on it
    in the outer scope.
  ]
)

The `ScopedIO` library minimizes the amount of code required to use FFIs in
Idris. With direct access to memory allocation and shim provided by
`FFICall`, no C glue code is needed to allocate, read, or write structs.
Instead, we leverge the compiler's `auto` implicit mechanism is able to write some of
this glue code and extend Idris' current FFI to call foreign functions
using our memory safe references.


#figure(
```idris
TestStruct : Type
TestStruct = Struct "TestStruct"
  [ ("a", Bits8)
  , ("b", Bits16)
  , ("c", Bits32)
  , ("d", Bits64) ]

%foreign "C:printStruct,mylib"
printStruct : TestStruct -> PrimIO ()

testSafeFFI : IO ()
testSafeFFI = runScopedIO $ \a' => do
  x <- newRef { cty = TestStruct }
    ( 101
    , 10203
    , 20405060
    , 50404020205 )
  safeFFI printStruct [x]
```,
  caption: [
    Example usage of `safeFFI` using a `Ref _ (Struct ...)` to call
    a foreign function `printStruct` which takes the `Struct` by
    value.
  ]
)

One downside of over-using `auto` implicits in this way, is that it has
detrimental effect on compile times. The demo program used in a following
@sec-eval-memsafe, is around 500 lines of code but takes 10 seconds
to compile on an Apple MacBook Pro with an M2 10-core CPU.
One reason for this may be that `auto` implicit
search does not only look for a _single_ construction satisfying the
type, but also a sort of "trivial uniqueness" of the
implementation @edwin-auto-search-convo. This means, Idris continues to
search the entire, bounded, search space even if a solution is found.
The Idris compiler provides some timing statistics via the `--timing`
flag but it did not provide enough granularity to implicate `auto`
implicits precisely.

During development of the demo program I found explicit type annotations
were sometimes needed in calls to `newRef` as the typechecker could not
mange the ambiguity of `Marshal`. The particular case which triggered
this is the allocation of a `Struct` which has a field with another `Struct`
type (see @fig-nested-newref). Creating this type requires "nested"
calls to `newRef`; the parent `Struct` is created using a tuple where
one of the elements is also created by `newRef`.  In this scenario,
the typechecker needs to find a single type that is a suitable output
of the inner `newRef` and a suitable input to the outer `newRef`; that
is to say the compiler has no information about this type from either
the function that produces it (the inner `newRef`) or the function
consuming it (the outer `newRef`).  Not having sufficient information,
the typechecker gives up. Annotating the inner `newRef` function call with the
expected C type resolves the ambiguity.


#figure(
```idris
failing "Can't find an implementation"
  nestedNewRef : ScopedIO a'
    (Ref a'
      (Struct "hello"
        [ ("f", Int)
        , ( "g" , Struct "world" [ ("h", Int) , ("i", Int) ])
        ])
    )
  nestedNewRef = do
    newRef
      ( 25
      , !(newRef
        -- uncommenting the following line fixes the
        -- ambiguity issue
        -- { cty = Struct "world" [("h", Int), ("i", Int)] }
        ( 50
        , 75
        ))
      )
```,
  caption: [
    This function fails to type check with the error
    `Can't find an implementation for Marshal a' ...`
  ]
) <fig-nested-newref>

In a similar vein, resolving type errors in calls `safeFFI` and `newRef`
can be difficult. When an incorrect argument is passed, the typechecker
complains that a `Marshal` instance can't be found and may dump
all of the expected input and output types. This is a worse experience
in comparison to plain function calls or record construction, where
the typechecker can tell the user exactly which argument is incorrect.

Idris has a feature for resolving some of these issues called
"determining arguments" @idris-determining-parameters, but I could
not find a way to use them to fully eliminate type annotations.
Ultimately, while `auto` implicits result in code that is easier to read,
it comes with the cost of making it harder to write.

=== Memory safety <sec-eval-memsafe>

#figure(
  image(height: 200pt, "img/rest-energy.jpg"),
  caption: [
    No matter how well `ScopedIO` may protect _us_ from making mistakes
    around memory usage, building software requires
    trusting the developers of external libraries to not make the
    same mistakes. This idea was depicted in _Rest Energy_ @rest-energy,
    a performance where Marina Abramović and Ulay drew a bow using their
    body weight, with an arrow loaded and pointed at Abramović's heart.
  ]
)

In order to verify the logic of `ScopedIO`, a small demo program
was run under `valgrind`'s `memcheck` tool. `valgrind` is
"a framework for building dynamic analysis tools" @valgrind;
that is, tools which inspect the behavior of a program as it
runs. The `memcheck` tool in particular tracks program allocations
and memory accesses to identify errors. `valgrind`'s coverage of
our safety criteria (defined in @sec-memsafe) is as follows:
- Unitialized memory in general is not reported, rather
  an error is reported when uninitialized memory
  "affect[s] your program's externally-visible behaviour" @valgrind-memcheck.
  For example, if a jump or move CPU instruction depends on
  the uninitialized value.
- Out-of-bound access is tracked in two ways. The simple case of unallocated memory
  is tracked using "V" bits (ie. "valid" bits) for the address space @valgrind-memcheck.
  The more complicated case of misusing a pointer to access an arbitrary allocation is
  not handled in general. However, `memcheck` can identify some of these errors
  by througha a _redzone_: by default the tool will allocate 16 bytes
  before and after an allocation, and set the "V" bits to invalid @valgrind-cli.
  This means linear access which are off-by-one will be caught, rather than
  possibly continuing to an adjacent chunk of allocated memory.
- Free-related errors, again, come with a caveat. `memcheck` can track
  that memory allocations are `free`-ed exactly once. However, a chunk
  of memory may be reallocated such that a new _variable_ happens to hold
  the same address value as an old variable. `free`-ing this allocation with
  the old variable is incorrect but `memcheck` cannot distinguish betwen
  variables.

In order to focus on the design of `ScopedIO`, the demo
program uses `Graphics.WGPU.Sys` rather than the higher-level `Graphics.WGPU`.
The demo program can be found in `src/Example/TriangleSys.idr` in the artifacts repository.
An inital run of the program resulted in hundreds of errors. These
were mostly memory leaks originating from transient
dependencies #footnote[ie. Dependencies of `wgpu`]. These
are out of our control and were thus suppressed via
`valgrind`'s `--suppressions` flag. Further, some memory
leaks originated from initialization functions for Linux's
graphics drivers; these leaks persisted despite double-checking
the de-initialization functions were being called.

Once external errors were suppressed, `valgrind` illuminated
two issues with `ScopedIO`. An out-of-bounds access of one byte,
and memory leaks from `wgpu` resources. The out of bounds read
was caused by the following helper function which creates
a manually managed string from an Idris `String`:

```idris
stringRef : String -> ScopedIO a' (Ref a' Bits8)
stringRef s = do
  let len = strLength s
  ptr <- primIO $ prim__malloc . (+ 1) $ cast len
  defer (primIO $ prim__free ptr)
  primIO $ prim__memcpyStr ptr s (cast len)
  pure $ unsafePtrRef $ prim__castPtr ptr
```

The mistake present in this function is negligence of
of the `NUL`-terminator. In C, strings are expected to
end in a `NUL` ASCII character represented by byte
with value 0. Below is a diff of `stringRef` which fixes the issue.

```diff
-  ptr <- primIO $ prim__malloc $ cast len
+  ptr <- primIO $ prim__malloc . (+ 1) $ cast len
   defer (primIO $ prim__free ptr)
   primIO $ prim__memcpyStr ptr s (cast len)
+  _ <- primIO $ prim__ptrWrite8 (prim__offsetPtr ptr (cast len)) 0
```

The leaked `wgpu` resources were caused by forgotten destructors.
Detailed in @sec-scopedio-scope /* and @sec-wgpu-idr */, objects
returned by `wgpu` functions need to call a destructor function
once no longer needed. The destructor updates a reference count
to the object, deallocating if no references are left. This
construct does not exist in the C language (yet? @c-defer).
Thus, only documentation can communicate these requirements to a
programmer. The implemented fix for this issue is adding
the destructor calls manually or with `ScopedIO`'s `defer` function.
However, this introduces the potential for use-after-frees since the
return values are not protected by `Ref`s.
Potential mechanisms for safe, ie. without potential use-after-free, and
automatic destructors is discussed in @sec-future-safe-destructors.

No further errors were found via `valgrind`. However,
`ScopedIO` was not perfect on its first try. Rather, fixing
the issues that manifested as visible runtime errors
(ie. segmentation faults and failing allocator `assert`s)
earlier in the development cycle resulted in a correct
implementation of `ScopedIO`. This does not obviate the
need for dynamic analysis from tools like `valgrind`.
Not only is external code liable to errors but, as shown by
both examples in this section, the type system cannot
capture all correctness requirements and mistakes will
slip through. Dynamic analysis proves valuable in catching such
mistakes.

Ultimately, `System.ScopedIO` accomplishes the goal of enforcing
memory safety where possible (ie. with `newRef` and `safeFFIDrop`),
without significant additional burden to the developer.

/*

== `Graphics.WGPU` Evaluation <sec-eval-wgpu>

/*
- one major issue is long compile times and difficult debugging
  arrising from the use of `auto` implicits
- both of these issues can be fixed by borrowing another
  design pattern from Rust, namely  `*-sys` crates @rust-sys-crates
- This section of the these usees the `*-sys` pattern to create the
  following two modules:
  - `Graphics.WGPU.Sys` will be created for the
  sole purpose of informing Idris about `wgpu`'s functions and types. And
  this module will be used to create another module `Graphics.WGPU`, which
  exposes a more idiomadic interface.
  - `Graphics.WGPU.Sys` which only informs Idris of `wgpu`s C functions
    and types (described in @sec-wgpu-sys)
  - `Graphics.WGPU` which uses `Graphics.WGPU.Sys` to build an idiomadic
    Idris API for `wgpu` (@sec-wgpu-idr)
    */

Only the function and types necessary for the demonstration in @sec-graphics
were implemented as part of `Graphics.WGPU`. As such, the expected improvement
of compile times cannot be evaluated, since a demo program would be dominated
by direct `Syste.ScopedIO` calls. However, @fig-wgpu-idr-example what a typical call
to `.beginRenderPass` would look like. This indeed looks like idiomadic Idris,
without overbearing lifetimes thanks to the dynamic memory management of `GCPtr`.
Further, there is only basic type inference proof seearch needed to typecheck the
expression and no `auto` implicit search.

#figure(
```idris
testBeginRenderPass : GC WGPUCommandEncoder -> GC WGPUTextureView -> IO (GC WGPURenderPassEncoder)
testBeginRenderPass enc dest = do
  enc.beginRenderPass $
    MkRenderPassDescriptor
      (Just "render-pass")
      [ MkRenderPassColorAttachment
          dest
          0xffffffff -- depth slice undefined macro
          Nothing
          WGPULoadOp_Load
          WGPUStoreOp_Store
          (0.0, 1.0, 0.0, 1.0) -- full green
      ]
      Nothing
      Nothing
      Nothing
```,
  caption: [
    Example usage of `Graphics.WGPU`; `.beginRenderPass` hides all the details
    of `ScopedIO` and `Marshal` behind normal Idris function application. This
    is easier to understand, debug, and compile.
  ]
)<fig-wgpu-idr-example>

While this did not materialize in a production-ready, or even test-ready,
library the design work has been completed and implementation can move forward.

*/

==  Evaluation <sec-eval-edsl>

The concrete goal of an embeded domain specific language
for GPU-accelerated mathematics did not surpass the research
stage. Possible design are discussed in @sec-future-edsl. Despite
this failure, the work in this thesis is not far from being
built upon. While not formally evaluated here,
`System.ScopedIO` can be used with minimal, but non-zero, changes
to the Idris compiler.

/*
On this track, @annex-contrib-idr outlines various contributions I've made, in
discussion and patches, to the Idris ecosystem.
*/

= Related Work <sec-related>

== Memory Safety <sec-related-memsafe>

In recent years, government and industry organizations have
called for the computing community to adopt memory safe languages
and approaches @ms-memsafe @google-memsafe @cisa-memsafe. Rust @rust
has been mentioned repeatedly in this document for good reason, it
demonstrates an optimal combination of memory safety and performance
which was not thought possible. Rust is not the first to work
in this domain, inspired by Cyclone @cyclone a memory safe
"dialect" of C. Since then, a similar endevor is being developed,
Fil-C @fil-c, is a garbage-collected version of C with the
goal of maximal compatibility with existing C code.


== Boilerplate <sec-related-boilerplate>

An unexpected focus of this dissertation was on boilerplate and
exploring the various approaches that could be described as
code or proof generation.

=== Damas-Hindely-Milnder Type Inference

While I was not aware of the connection before building
`System.ScopedIO`, it turns out the connection between
meta-programming and type inference was motivating
factor in the creation of ML. #footnote[I probably should
have realized this earlier, having known the name ML
stood for "meta language" @stdml-history].

#quote(
  attribution: [The History of StandardML @stdml-history],
)[
  When Milner began his project to develop the Edinburgh LCF system,
  his plan was to replace Lisp, the metalanguage in the first generation
  Stanford LCF system, with a logically secure metalanguage, where a
  bug in the metalanguage code could not lead to an invalid proof.
]

This work by Milner eventually led to the type system which
underlies Haskell and Rust, dubbed Damas-Hindley-Milner type
system. The core of this type system is a decideable inferece
algorithm which frees programmers from the need explicitly
write type annotations. This feature is a ancestor
of Idris' `auto` implicits by way of _type class resolution_ @idris-general-purpose @impl-typeclass.

=== Contemporary Approaches to Code Generation

Modern approaches tend to fall into three categories:
- _Macros_ or _meta-programming_ where the _abstract syntax tree_ is manipulated
  and transformed.
- _Program synthesis_ @synthesis which exhaustively searches for a program
  given examples input/out pairs or a specification.
- What I call "program generation" or the approach so simple it doesn't have
  name: a script or program which outputs source code, usually from a configuration
  or data file.

`auto` implicit search falls most closely to program synthesis, though it should
be noted, Idris has a seprate program synthesizer in its `:ps` REPL command.
This implements type-driven program synthesis @synth-poly. Another approach
rooted in type theory is called _staging_ @two-level-tt.

The following sections provide more detail in the state-of-the art
for macros and program synthesis.

#{
  set par(justify: false)
  let checkmark = sym.checkmark
  figure(
    table(
      columns: 5,
      table.header(
        [],
          [*Program Synthesis*],
          [*Meta-programming*],
          [*Binding Generation*],
          [*Dep. Type Proof Search*],
      ),
      [*Compiler Integration*],
        [Usually external tools],
        checkmark,
        [External Tools],
        checkmark,
      [*Correctness/Verification*],
        checkmark,
        [
          Generally none beyond host languge, problems such as
          _macro hygiene_ @hygienic-macros exist, some approaches
          guarantee well typed macros @metaocaml
        ],
        [Generally none beyond target language],
        checkmark,
      [*Generality*],
        [Synthesis tools tend to be domain specific, domain logic needs to be implemented],
        checkmark,
        [Only for FFI],
        checkmark
    ),
    caption: [An overview of the design space for boilerplate-avoiding methods],
  )
}

==== Macros

Early Haskell proposals @haskell-ffi @awk-squad laid robust rules
for FFI but did not commit to a marshalling approach. Modern
approaches such as @hs-bindgen still follow the principle
as the original proposal of generating Haskell code using
external tools.

An approach with similar ergonomics as
the use of auto-implicits is `derive-storable` @derive-storable module
which uses the `DeriveGeneric` Haskell language extension
#footnote[It also provides an optional compiler plugin as a workaround
for performance issues]. `Generic` in Haskell is a metaprogramming
approach which resembles macros.

Idris itself has a mechanism resembling macros, called "elaborator reflection" @elab-reflection.
In elaborator reflection, user code can create and manipulate Idris' internal representation
of programs @stefan-elabrefl.

/*
- scrap your boilerplate @scrap-boilerplate
- elabreflection
*/

==== Program Synthesis <sec-prog-synth>

/* - currently exists in Idris as proof search

In the context of program synthesis, `ScopedIO` and `safeFFI` for

code, requires more work from the programmer than existing
systems. Appropriate data structures
and `%hint`-ed functions need to be specified such that
the search space is sufficiently small. However,
*/

Program synthesis is an established area of research
on program generation. Some of these approaches
incorporate external tooling or languages for specifying the
desired behavior of a program. Specification
may be provided:
- "by-example" as actions to be recorded @eager or specific input-output pairs @live-pbe
- as a specification, either specified in a domain-specific logic language @sketch
  or in the host language @rust-synthesis.
The system presented in @rust-synthesis integrates naturally with
non-generated source code via Rust's procedural macros; further, the
synthesizer presented leverages Rust's strong types for minimizing
the program search space and implements a logic system incorporating
Rust-specific safety rules.

Similar to @rust-synthesis, LiquidHaskell @liquid-haskell allows programmers
to annotate Haskell functions with properties to be verified through refinement
types @refinement-types. LiquidHaskell only verifies the written implementation matches
a specification; though, the annotations can provide information for synthesis,
it is not explored much @liquid-haskell-holes.

== GPU-Accelerated Mathematics <sec-future-edsl>

My original intention with the dissertaion was to build
an embdded domain-specific language (EDSL) for mathematics within
Idris. The idea was inspired by various approaches to
formalizing _automatic differentiation_ @original-ad @ad-survey @chad @correct-ad
within functional programming concepts.

This EDSL could then be compiled into a GPU shader program or executed
in a GPU byte code interpreter, as in @parallel-surfaces. This is not
particularly performant but would allow, for example, GPU accelleration
in a dynamic environment like a REPL without the cost of shader
recompilation.

= Future work <sec-future>

== Safe Destructors <sec-future-safe-destructors>

As is, a `Ref` created from `safeFFIDrop` can be used in another call to
`safeFFI` on the destructor again. Idris' implementes linear types
or _multiplicities_ which allow the programmer to specify a
value should be used 0 or 1 times at runtime @idris-multiplicities.
This can be used to ensure a destructor-requiring calls its
destructor exactly once. However, only pushes off the primary
issue that C does not have a way of distinguishing
a destructor from a regular function. That is, with
multiplicities, how does a destructor consume the
single value while a regular function does not?

== Performance <sec-future-const>

As described, functions like `sizeof` need to recalculate sizes
each time they are called, however Idris' multiplicities may
be used again @idris-multiplicities,
this time to force these computations to happen 0 times at runtime,
and only at compile time.

Another avenue for better performance is the use of lifetimes
and borrowing. Rust differentiates `&` from `&mut` not only for
correctness but also for performance @stacked-borrows.
In particular, the optimizer can better reason about
_aliasing_ @pointer-aliasing, which enables compiler
optimizations @pointer-aliasing-perf.  `ScopedIO` does not
distinguish between mutable and immutable `Ref`s, thus
alias analysis-based optimizations cannot occur. A fuller
version of the borrowing system has been implemented in Haskell @pure-borrow
which can serve as inspiration.

Compiling this with a backend like `RefC` or the LLVM backend @rapid would
make Idris a high level interface to C. A programmer could gradually push
down performance critical code into manual memory management, ie. not
garbage collected, and explicit layouts within Idris before needing to
fully break into C code.

/*
In the area of memory management, Pure Borrow @pure-borrow is a more
complete implementation of Rust-like ownership using the `LinearTypes` Haskell
extension. It features owned types as well as distinct
mutable and immutable references, and is backed by formal semantics.
However, its focus is on containing
and specifying mutation for safe parallel processing rather
than memory safety of foreign allocation; as such, references are expected
expected to contain normal Haskell values, ie. subject to
garbage collection. Consequently, it's leak-freedom property
is theoretical and manual memory management is not discussed.
TODO: `&` vs `&mut` and `restrict` and performance

As mentioned in @sec-eval this would require
differentiating mutable and immutable references at the type level
as in @pure-borrow (this is further described in @sec-related-memsafe).

- giving access to stack-allocated memory can lead to
  a different class of memory corruption with slightly
  different characteristics, namely overwriting the
  return address of a function. This class of
  bugs is well-known, and `memcheck` could still be
  used to empirically verify correctness.


This
paper also glosses over the platform-dependence of
of a function like `sizeof`, it is not immediately
clear how this information needs to be communicated in Idris.

== Union types

One key missing functionality is C `union` types, similarly
is `transmute` @rust-transmute or `reinterpret_cast` @reinterpret-cast.
This functionality creates some problems around alignment of nested
members and use of uninitialized memory. However, it may be possible
to do this safely by proving that fields have the same alignment
constraints and pointer fields live at the same offsets and
are somehow compatible.

== Generating Optimizer-Friendly Code
*/



