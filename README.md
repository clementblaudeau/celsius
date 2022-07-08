[![Docker CI](https://github.com/clementblaudeau/celsius/workflows/Docker%20CI/badge.svg?branch=master)](https://github.com/clementblaudeau/celsius/actions?query=workflow:"Docker%20CI")

![Celsius logo](https://github.com/clementblaudeau/celsius/blob/master/logo.png)

# Celsius Coq formalization

This repository contains the Coq formalization of the paper:
* A Conceptual framework for Safe Object initialization, (submitted to OOPSLA 2022)
  Clément Blaudeau and Fengyun Liu

## Install/Build
See [INSTALL.md](INSTALL.ml)

## Project structure

### Preliminaries
* [src/LibTactics](src/LibTactics.v): tactics borrowed from [Software Foundations](https://www.cis.upenn.edu/~cis500/cis500-f17/sf/plf-current/LibTactics.html)
* [src/Tactics](src/Tactics.v): additional tactics adapted from [SystemFr](https://github.com/epfl-lara/SystemFR)

### Language
* [src/Language.v](src/Language.v): definition of the Celsius calculus and global parameters.
* [src/Notations.v](src/Notations.v): all notations are reserved in this file, with type classes for overloaded notations.
* [src/Helpers.v](src/Helpers.v): basic functions, lemmas and tactics for getters, updates, assignments, etc.

### Semantics
* [src/Semantics.v](src/Semantics.v): big-step semantic rules and custom induction predicate on the rules.
* [src/Eval.v](src/Eval.v): definitional interpreter for the language and equivalence result with the big step rules.

### Local reasoning
* [src/Reachability.v](src/Reachability.v): definition of the accessibility inside a store, and the semantic meaning of modes
* [src/PartialMonotonicity.v](src/PartialMonotonicity.v): (semantic) partial monotonicity definition and theorem
* [src/Wellformedness.v](src/Wellformedness.v): wellformedness conditions and theorem
* [src/Stackability.v](src/Stackability.v): (semantic) stackability definition and theorem
* [src/Scopatibility.v](src/Scopatibility.v): scopatibility definition and theorem
* [src/LocalReasoning.v](src/LocalReasoning.v): semantic local reasoning, promotion and local reasoning for typing theorems.

### Soundness
* [src/Typing.v](src/Typing.v): Typing rules and inversion lemmas
* [src/MetaTheory.v](src/MetaTheory.v): Typing definition of the core principles, store typing definition and lemmas
* [src/Soundness.v](src/Soundness.v): Soundness theorem (and helper lemmas)


## Paper-formalization correspondence

### Definitions
The powerful notation mechanism of Coq allowed us to have notations that match the paper quite directly.
|                          | Paper **and** Coq notation        | Coq term                             | File                                                                              |
| ------------------------ | -------------------------------------- | ------------------------------------ | --------------------------------------------------------------------------------- |
| Reachability             | $\sigma ⊨ l ⇝ l'$                      | `reachability`                       | [src/Reachability.v](src/Reachability.v)                                          |
| Semantic modes           | $\sigma ⊨ l : \mu$                     | `semantic_mode`                      | [src/Reachability.v](src/Reachability.v)                                          |
| BS semantics             | $⟦e⟧(σ, ρ, ψ) \longrightarrow (v, σ')$ | `evalP`                              | [src/Semantics.v](src/Semantics.v)                                                |
| Partial monotonicity     | $σ \preceq σ'$                         | `partial_monotonicity`               | [src/PartialMonotonicity.v](src/PartialMonotonicity.v)                            |
| Monotonicity             | $Σ ≼ Σ'$                               | `monotonicity`                       | [src/MetaTheory.v](src/MetaTheory.v)                                              |
| Authority                | $σ ▷ σ'$ and $Σ ▷ Σ'$                  | `authority` and `authority_st`       | [src/Authority.v](src/Authority.v) and [src/MetaTheory.v](src/MetaTheory.v)       |
| Stackability             | $σ ≪ σ'$ and $Σ ≪ Σ'$                  | `stackability` and `stackability_st` | [src/Stackability.v](src/Stackability.v) and [src/MetaTheory.v](src/MetaTheory.v) |
| Scopability              | $(σ,L)⋖(σ',L')$                        | `scopability`                        | [src/Scopability.v](src/Scopability.v)                                            |
| Typing                   | $(Γ,T_\mathtt{this})⊢e:T$              | `expr_typing`                        | [src/Typing.v](src/Typing.v)                                                      |
| Object typing            | $Σ⊨(C,ω):(C, cold)$                    | `object_typing`                      | [src/MetaTheory.v](src/MetaTheory.v)                                              |
| Store typing abstraction | $Σ⊨σ$                                  | `store_typing`                       | [src/MetaTheory.v](src/MetaTheory.v)                                              |
| Env typing               | $Σ⊨𝜌:Γ$                                | `env_typing`                         | [src/MetaTheory.v](src/MetaTheory.v)                                              |

### Theorems correspondence
| Theorem, lemma, statement            | Coq term                     | File                                                   |
| ------------------------------------ | ---------------------------- | ------------------------------------------------------ |
| Partial monotonicity theorem         | `pM_theorem`                 | [src/PartialMonotonicity.v](src/PartialMonotonicity.v) |
| Authority theorem                    | `aty_theorem`                | [src/Authority.v](src/Authority.v)                     |
| Stackability theorem                 | `stk_theorem`                | [src/Stackability.v](srv/Stackability.v)               |
| Scopability theorem                  | `scp_theorem`                | [src/Scopability.v](srv/Scopability.v)                 |
| Local reasoning                      | `Local_reasoning`            | [src/LocalReasoning.v](src/LocalReasoning.v)           |
| Promotion lemma                      | `promotion`                  | [src/MetaTheory.v](src/MetaTheory.v)                   |
| Local reasoning for typing           | `Local_reasoning_for_typing` | [src/LocalReasoning.v](src/LocalReasoning.v)           |
| Soundness statement (expressions)    | `expr_soundness`             | [src/Soundness.v](src/Soundness.v)                     |
| Soundness statement (initialization) | `init_soundness`             | [src/Soundness.v](src/Soundness.v)                     |
| Soundness theorem                    | `Soundness`                  | [src/Soundness.v](src/Soundness.v)                     |
| Program soundness corollary          | `Program_soundness`          | [src/Soundness.v](src/Soundness.v)                     |

### Implementation details and assumptions
Our implementation makes some assumptions and representation choices, which we believe are without loss of generality:
* We represent variables, fields, locations (and thus, values) as integers.
* We represent stores and (local) environments as lists.
* We assume a globally accessible class table `ct` (defined as a `Parameter`) and an entry class `EntryClass`.
* We added the axiom of classical logic:
```coq
Axiom classicT : forall (P : Prop), {P} + {~ P}.
```
* For the soundness result, we assume the classtable is well typed : `Parameter typable_classes: T_Classes.`
