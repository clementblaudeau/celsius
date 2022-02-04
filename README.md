[![Docker CI](https://github.com/clementblaudeau/celsius/workflows/Docker%20CI/badge.svg?branch=master)](https://github.com/clementblaudeau/celsius/actions?query=workflow:"Docker%20CI")

![Celsius logo](https://github.com/clementblaudeau/celsius/blob/master/logo.png)

# Celsius Coq formalization

Accessing uninitialized data during object initialization is a common and subtle programming error. This
error is either not prevented by mainstream languages, like in Java, C++, Scala, or it is prevented by greatly restricting initialization patterns, like in Swift. The Celsius model for safe and modular initialization of objects aims at solving this issue, via a light annotation mechanism (*cold*, *warm*, *hot*). This repository contains the Coq formalization of a small object-oriented language with *celsius* annotations. Several results are proved on the semantic model and the typing is shown sound.

## Build

To build the coq project, you'll need `coq` ( >= 8.14). From the top-level directory, run :
```sh
make Makefile.coq
make
```

## Project structure
The project has three main parts:
1. **Basics**: Language definition, helpers, notations (in the files `Language.v`, `Helpers.v` and `Notations.v`). The big-step semantics are given in `Semantics.v`. A step-indexed evaluator is defined and shown equivalent to the semantics in `Eval.v`. The typing rules are given in `Typing.v`.
2. **Local reasoning**: The properties of the state of memory (named a `Store`) during initialization are defined and studied in `PartialMonotonicity.v`, `Wellformedness.v`, `Stackability.v` and `Scopatibility.v`. They all converge to the *local reasoning* theorem in `LocalReasoning.v`. More details below.
3. **Typing**: The properties of the *abstract* state of memory (named a `StoreTyping`) used for typing are defined in `MetaTheory.v`. They are used to show the soundness of typing (in `Soundness.v`)

## Local reasoning
We first explore the properties of the state of memory during evaluation of an expression.

### Reachability : `σ ⊨ l ⇝ l'`
Defines the reachability relationship. A location `l'` is reachable from `l` in a store `σ` if either `l = l'` or, by hoping from pointers to pointers we can go from `l` to `l'`.

### Wellformedness : `wf σ`
Technical guaranties. A wellformed store `σ` contains only locations that are within the store, and object have a number of fields bounded by their definition.

### PartialMonotonicity : `σ ⪯ σ'`
Defines the partial monotonicity between stores. Store `σ` and `σ'` are in a _partial monotonicity_ relationship if `σ'` has more fields in every local environments associated with a stored object. The evaluator's initial and result stores are in a partial monotonicity relationship (`pM_theorem`).

### Stackability : `σ ≪ σ'`
Defines the stackability relationship. Stores `σ` and `σ'` are _stackable_ if all objects that are in `σ'` are either `warm` (all fields initialized), or were already in `σ`. This captures the idea that *newly created objects have initialized fields*. The evaluator's initial and result stores are stackable (`stk_theorem`).

### Scopability: `(σ, L)  ⋖  (σ', L')`
A more suble relation that allows to control the set of reachable locations. A set of location `L` and a store `σ` are scoping another set `L'` and store `σ` if all the locations reachable in `σ'` from a point in `L'` are also reachable from `L` in `σ`. This allows us to control what objects can be reached during initialization.

### Local reasoning
All the previous properties are used to show that when initializing an object, we get an object with fields that are all initialized and pointing towards fully initialized objects (an hot object). This is a key property of the semantic.

## Typing
Here we state the properties of the abstract representation of memory (store typing) during evaluation. (to be expanded)
