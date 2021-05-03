[![Docker CI](https://github.com/clementblaudeau/celsius/workflows/Docker%20CI/badge.svg?branch=master)](https://github.com/clementblaudeau/celsius/actions?query=workflow:"Docker%20CI")

![Celsius logo](https://github.com/clementblaudeau/celsius/blob/master/logo.png)

# Celsius Coq formalization

Accessing uninitialized data during object initialization is a common and subtle programming error. This
error is either not prevented by mainstream languages, like in Java, C++, Scala, or it is prevented by greatly restricting initialization patterns, like in Swift. In this paper, we propose a model called Celsius for safe and modular initialization of objects, and prove its soundness. We extend the model and implement a prototype in Scala. The experiments on several real-world Scala projects show that the design requires few programmer annotations.

This repo contains the Coq formalization of the language and results. The main theorem is in the file `LocalReasonning.v`

## Project structure
### Trees.v
Contains the inductive definition of the language and other structures used:

 - `Expr`: language expressions
 - `Method`, `Field`, `Class`, `Program`: Constructors of language structures
 - `Result` : result type for the evaluator

### Eval.v
Defines the evaluator and helpers

### Reachability.v
Defines the reachability relationship. A location `l2` is reachable from `l1` in a store `s` if either `l2 = l1` or, by hoping from pointers to pointers we can go from `l1` to `l2`.

### Compatibility.v
Defines the compatibility relationship. Store are *compatible* if they have the same objects at the same locations, regardless of the local environments.
The evaluator's initial and result stores are compatible (`compatibility_theorem`).

### PartialMonotonicity.v
Defines the partial monotonicity relationship. Store `s1` and `s2` are in a *partial monotonicity* relationship if `s2` has more elements in every local environments associated with a stored object. The evaluator's initial and result stores are in a partial monotonicity relationship (`partialMonotonicity_theorem`).

### Stackability.v
Defines the stackability relationship. Stores `s1` and `s2` are *stackable* if all objects that are in `s2` and not in `s1` are `warm` (all fields initialized). The evaluator's initial and result stores are stackable (`stackability_theorem`).

### Scopability.v
By far the most involved file. A set of location `L1` and a store `s1` are scoping another set `L2` and store `s2` if all the locations reachable in `s2` from a point in `L2` are also reachable from `L1` in `s1`.
