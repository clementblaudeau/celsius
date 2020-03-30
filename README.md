# Celsius Coq formalization

Accessing uninitialized data during object initialization is a common and subtle programming error. This
error is either not prevented by mainstream languages, like in Java, C++, Scala, or it is prevented by greatly restricting initialization patterns, like in Swift. In this paper, we propose a model called Celsius for safe and modular initialization of objects, and prove its soundness. We extend the model and implement a prototype in Scala. The experiments on several real-world Scala projects show that the design requires few programmer annotations.

This repo contains the Coq formalization of the language and results.

## Project structure
### Trees.v
Contains the inductive definition of the language and other structures used:

 - `Expr`: language expressions
 - `Method`, `Field`, `Class`, `Program`: Constructors of language structures
 - `Result` : result type for the evaluator

### Eval.v
Defines the evaluator and helpers