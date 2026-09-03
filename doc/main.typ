#import "@preview/hydra:0.6.3": hydra
// #import "@preview/wordometer:0.1.5": word-count, total-words

#set text(font: "CMU Serif")

#show raw.where(lang: "idris"): set raw(
  syntaxes: "idris.sublime-syntax",
)

#show raw: it => {
  set text(font: "Go Mono", fill: luma(20))
  set block(
    fill: luma(245),
    inset: 0.5em,
    radius: 0.2em,
    width: 100%,
  )
  it
}

#show raw.where(block: true) : set block(breakable: false)
#show raw.where(block: false) : it => {
  set text(fill: luma(70))
  box(
    fill : luma(240),
    inset: 0.2em,
    radius: 0.2em,
    it,
  )
}

#set par(
  justify: true,
  first-line-indent: (amount: 1em, all: true),
)

#show figure: it => {
  show figure.caption : it => {
    block(
      width: 90%,
      it
    )
  }

  it
}

#set page(
  header: context {
    if calc.odd(here().page()) {
      align(left, [ #here().page() #h(30pt) #emph(hydra(1)) ])
    } else {
      align(right, [ #emph(hydra(skip-starting: false, 2)) #h(30pt) #here().page()])
    }
  }
)

#let sec(offset: 1, file) = {
  [
    #set heading(offset: offset)
    #include file
    #set heading(offset: offset)
  ]
}


// #show: word-count.with(exclude: (raw, bibliography))
// #show: word-count.with(exclude: (bibliography))

// #set heading(numbering: none)

#let centered(it) = {
  set align(center + horizon)
  it
  set align(left + top)
}


#set heading(numbering: "1.")

= Introduction <sec-intro>

/* abstract

In this dissertation I will demonstrate how the features of a dependently
typed language can be used in low-level or _systems_ programming. This
is done primarily by implementing an Idris library, `ScopedIO`, which
uses novel and known idioms to enforce memory safety when interfacing
with C foreign functions. The properties of `ScopedIO` are tested by
binding to the `wgpu` graphics library and evaluating a demo program.
An Idris library `Graphics.WGPU` is also produced, which exposes the
`wgpu` to other Idris programs. Overall, this work contributes bringing
academic and theoretical approaches to practical applications.

*/


/*
What is now known as Damas-Hindley-Milner type inference
can be traced to academic research from 1958 @curry-feys-cl,
1969 @hindley, 1978 @milner, and 1982 @damas. The latter
two breakthroughs occurring down the road from St. Andrews, at the University of
Edinburgh, as a precursor the ML family of programming
languages @std-ml-history. ML eventually became a platform for
programming language research with many dialects representing the various avenues of
research. Hoping to coalesce these fractured approaches into a single language,
researchers were meeting in the west coast, at the University
of Glasgow @haskell-history, to build the Haskell programming language
which was first released in 1990 @haskell-report.
*/

In 2006, Graydon Hoare started writing a programming language which
he described as "technology from the past come to save the
future from itself". Hoare's inspirations were diverse such
as CLU @clu, an early object oriented language; Erlang @erlang, a language
focusing on concurrency; and St. Andrew's own Napier @napier language, which
features polymorphism and persistence. What he came up with was the
Rust language @rust, first released to the public in 2012 as version 0.1
and a stable version 1.0 released in 2015.

Rust has become synonymous with it's most novel feature: borrowing. This
idea is not completely novel in itself: it combines _ownership types_,
first described in 1998 @ownership, with _subtyping_, which dates back to the
70s @simula. However, the application of these ideas to memory safety
was novel. In a similar vein, this dissertation aims to bring contemporary
research of functional programming and dependent types into the domain
of memory safety.

The primary goal of this thesis is to improve the ways in which
Idris developers call or _bind to_ foreign libraries (ie. libraries
written in C). An Idris module, `System.ScopedIO`, was developed to
support this goal by:
1. Embedding Rust-like lifetime rules within Idris' dependent type system
2. Leveraging Idris' `auto` implicit search to avoid "glue" code
Such that memory safety can be enforced by the compiler without having
to reach for external tools or meta-languages. The design and
implementation of `System.ScopedIO` is given in @sec-scopedio.

The secondary goal of this work is to build idiomatic Idris bindings to
the `wgpu` graphics library. This would enable Idris developers
to write graphical or massively parallel applications without
having to dig into the details of FFI.
// The design and implementation of this library is described in @sec-graphics.

A tertiary goal is to demonstrate how tackling practical, low-level details
can support theoretical research by developing an embedded domain-specific
language on top of the Idris `wgpu` bindings. This goal is discussed in @sec-eval-edsl
and @sec-future-edsl.

The rest of this dissertation is organized as follows.
// @sec-background provides background information on the topics of functional programming, memory safety, and computer graphics.
@sec-scopedio /* and @sec-graphics */ describe the design and implementation of
Idris modules supporting the goals above. @sec-eval contains an evaluation
of the implementations. And @sec-related covers additional related
developments in memory safety, language approaches to removing
boilerplate, and graphics programming.

== Memory safety <sec-memsafe>

_Pointers_ are memory addresses with some additional type information describing
the data at the pointed-to memory. Low-level languages, such as C, allow the programmer
to treat pointers as integers; with arithmetic operations and conversion
between different pointer @cppref-ptr. Misuse of these pointer operations,
and dynamic memory allocation, can lead to _memory corruption_.

/*
#figure(
  image(
    height: 150pt,
    "./img/ptr.png",
  ),
  caption: [
    A version of the _Two soyjaks pointing_ meme explaining pointer @two-soyjaks. Memes
    such as this one originate from questionable places on the internet and, much
    like the pointers they explain, should be handled with caution.
  ],
)
*/


For this paper, memory "safety" is defined as the absence of the the following three forms
of memory corruption #footnote[
  These classifications are taken from @google-memsafe and @rs-maybe-uninit.
]:
- Uninitialized memory read - `malloc`-ed memory and local variables do not
  have a defined default value. They may contain sensitive data from
  previous allocations; or if the value is a pointer, they likely point
  to invalid regions of memory.
- Out of bounds read/write - reading and writing to an address past what was asked for
  in `malloc`. This may lead to exposure of sensitive data, unrelated values
  being manipulated, or program crashes. It should be noted that the out-of-bounds
  address could be a valid allocation, for example if `malloc` returned adjacent chunks
  of memory in separate calls, but this is still considered unsafe.
- Use after free, double free #footnote[These generally fall under the
  class of _dangling pointers_, however this super-class also includes pointers
  to program stack memory; for the purposes of this paper this is not considered
  since the targeted Idris backend, `chez` scheme, only gives the programmer
  access to heap allocation (ie. `malloc`/`free`)], and memory leaks #footnote[Memory leaks are
  not always considered unsafe @rust-leak, it's mentioned here as prevention is useful
  and is solved along with the other forms.] - `free(3)` @man-free marks an allocation
  as no longer used, so the chunk of memory can be reallocated to a user program
  or used for bookkeeping. Thus, using memory after a `free` can read or write
  unknown data or corrupt the allocator itself.

Each of these issues can be solved by language design decisions. However,
solving correct use of `free` generally incurs a performance penalty.
Respectively, the accepted solutions for the above forms of memory corruption are:
- Uninitialized reads can be solved by the language defining default values
  (as in Go) or by enforcing all variables to be initialized with a value (as in Java).
- Out of bounds reads can also be solved relatively easily by bounds checking
  array access and disallowing pointer arithmetic. In C, they are both equivalently
  used to access arbitrary memory relative to a pointer. The runtime cost of bounds
  is eased by CPU branch prediction or avoided entirely by compiler
  optimizations @avoid-bounds-check. The methods for avoiding out-of-bounds
  memory access is described in @sec-oob and implemented in @sec-marshal.
- `free`-related bugs are not as easy to solve. Historically, they're only avoided with
  costly _garbage collection_ #footnote[Garbage collection involves automatically tracking
  and scanning objects in the heap for liveness, this adds significant overhead
  both in memory use and CPU usage.] (eg. Go, Java, C\#) or avoiding dynamic allocation
  entirely. However, Rust has broken this Pareto frontier, being memory safe
  without incurring the cost of garbage collection through its concept of ownership
  and borrowing. A full description is out of scope of this work, but in
  short Rust values _owned_ by certain parts of the program,
  and may be _borrowed_ as _references_ to the owned value. Importantly, references
  have _lifetimes_ which cannot be longer than the owned object they reference.
  Lifetimes are checked at compile time such that references never refer
  to memory that has been `free`-ed or gone out of scope. Lifetimes are further
  described in @sec-st-lifetimes and an implementation is described
  in @sec-lifetimes-impl.

High-level languages such as Idris are usually memory safe,
employing the methods above. However, FFI punches a hole through these safety
mechanisms; there's no guarantee the foreign code will maintain the invariants
and bookkeeping of the host language. Having a safety gap isolated to FFI is better
than an entire language, but the severity and frequency of memory corruption
bugs @cisa-memsafe @ms-memsafe @google-memsafe motivates further exploration
of memory safety in FFI. In @sec-scopedio, I present such an exploration,
resulting in a library for building memory safe FFI bindings.
// In @sec-graphics I describe how the library is used to write Graphics applications using `wgpu` @wgpu.

= `System.FFI.Safe` <sec-scopedio>

#sec("../src/System/FFI/Safe.idr.typ")

#sec("./sec-eval-related.idr.typ", offset: 0)

= Appendix

== Code Listings

#show raw.where(block: true) : set block(breakable: true)

=== Struct marshaling <code-marshal>

Implementation for `marshalStructBase` and `marshalStructRec`

```idris
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
```

== `Example.TriangleSys` <code-render>

A code snippet from the demo program used in @sec-eval.

```idris
render :
    (0 b' : Lifetime) ->
    (Ref a' GLFWwindow) ->
    (Ref a' (UnPtr WGPUAdapter)) ->
    (Ref a' (UnPtr WGPUSurface)) ->
    (Ref a' WGPUTexture) ->
    (Ref a' (UnPtr WGPUDevice)) ->
    (Ref a' (UnPtr WGPUQueue)) ->
    (Ref a' (UnPtr WGPURenderPipeline)) ->
    { auto 0 p : AtLeastAsLong a' b' } ->
    ScopedIO b' ()
render b' window adapter surface texture device queue pipeline = do
    enc <-
      safeFFIDrop
      wgpuDeviceCreateCommandEncoder
      (primIO . wgpuCommandEncoderRelease)
      [ shortenRef b' device
      , !(newRef
          { cty = WGPUCommandEncoderDescriptor }
          ( mkNULL WGPUChainedStruct
          , !(wgpuStringRef "command-encoder")
          ))
      ]

    putStrLn $ "wgpuTextureCreateView"

    view <- safeFFIDrop
      wgpuTextureCreateView
      (primIO . wgpuTextureViewRelease)
      [ !(getPtr (shortenRef b' texture))
      , mkNULL WGPUTextureViewDescriptor
      ]

    putStrLn $ "wgpuCommandEncoderBeginRenderPass"

    -- _ <- safeFFI prim__printf [ !(wgpuStringRef "\n\nrender-pass\n\n %d") ]

    pass <- safeFFIDrop
      wgpuCommandEncoderBeginRenderPass
      (primIO . wgpuRenderPassEncoderRelease)
      [ enc
      , !(newRef
        { cty = WGPURenderPassDescriptor }
        ( mkNULL WGPUChainedStruct
        , !(wgpuStringRef "render-pass")
        , 1
        , !(newRef
          { cty = WGPURenderPassColorAttachment }
          ( mkNULL WGPUChainedStruct
          , view
          , 0xffffffff -- depth slice undefined macro
          , the WGPUTextureView NULL
          , WGPULoadOp_Load
          , WGPUStoreOp_Store
          , !(newRef
            { cty = WGPUColor }
            (0.0, 1.1, 0.0, 1.0))
          ))
        , mkNULL WGPURenderPassDepthStencilAttachment
        , the WGPUQuerySet NULL
        , mkNULL WGPURenderPassTimestampWrites
        ))
      ]

    putStrLn $ "wgpuRenderPassEncoderSetPipeline"

    safeFFI
      wgpuRenderPassEncoderSetPipeline
      [pass, shortenRef b' pipeline]

    putStrLn $ "wgpuRenderPassEncoderDraw"

    safeFFI
      wgpuRenderPassEncoderDraw
      [ pass
      , 3, 1
      , 0, 0
      ]

    putStrLn $ "wgpuRenderPassEncoderEnd"

    safeFFI wgpuRenderPassEncoderEnd [pass]

    putStrLn $ "wgpuCommandEncoderFinish"

    cbd <- newRef
        { cty = WGPUCommandBufferDescriptor }
        ( mkNULL WGPUChainedStruct
        , dbg' (dbg !wgpuStringNULL) -- !(wgpuStringRef "command-buffer")
        )

    putStrLn $ "after cbd"
    putStrLn $ "dbg enc"
    _ <- pure $ dbg enc
    putStrLn $ "after dbg enc"

    buf <- safeFFIDrop
      wgpuCommandEncoderFinish
      (primIO . wgpuCommandBufferRelease)
      [ enc
      , cbd
      ]

    putStrLn $ "new buffer"

    bufbuf <- newRef { cty = WGPUCommandBuffer } buf

    putStrLn "wgpuQueueSubmit"
    safeFFI
      wgpuQueueSubmit
      [ shortenRef b' queue
      , 1
      , bufbuf
      ]

    _ <- safeFFI wgpuSurfacePresent [shortenRef b' surface]

    pure ()
```


#pagebreak()

#bibliography("./refs.bib", title: "References", style: "association-for-computing-machinery")
