(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)

(* This file gathers all the notations used in the project. Some notations are overloaded, which we
achieve by using type classes, instantiated when necessary. The levels are chosen carefully to allow
notations with the same prefix to co-exist peacefully. *)

(* ------------------------------------------------------------------------ *)
From Celsius Require Export Language.
Require Export PeanoNat.
Export ListNotations.
Global Open Scope nat_scope.
Global Open Scope list_scope.

(* ------------------------------------------------------------------------ *)
(** ** Overloaded notations *)

Class notation_dash (A B: Type) :=
  dash_ : A -> B -> Prop.
Notation "s ⊨ x" := (dash_ s x ) (at level 60, x at level 98).

Class notation_dash_colon (A B C: Type) :=
  dash_colon_ : A -> B -> C -> Prop.
Notation "s ⊨ x : y" := (dash_colon_ s x y) (at level 60, x at level 98, y at level 98).

Class notation_dash_arrow (A B C: Type) :=
  dash_arrow_ : A -> B -> C -> Prop.
Notation "s ⊨ x ⇝ y" := (dash_arrow_ s x y) (at level 60, x at level 98, y at level 98).

Class notation_stackability (A: Type) :=
  stackability_ : A -> A -> Prop.
Notation "s ≪ s'" := (stackability_ s s') (at level 60).

Class notation_authority (A: Type) :=
  authority_ : A -> A -> Prop.
Notation "s ▷ s'" := (authority_ s s') (at level 60).

Class notation_big_step (A B : Type) :=
  big_step_ : A -> Store -> Env -> Loc -> B -> Store -> Prop.
Notation "'⟦' x '⟧' '(' σ ',' ρ ',' ψ ')'  '-->'  '(' y ',' σ' ')'" :=
  (big_step_ x σ ρ ψ y σ') (at level 80, ψ at level 98).

Global Hint Unfold dash_: notations.
Global Hint Unfold dash_arrow_: notations.
Global Hint Unfold dash_colon_: notations.
Global Hint Unfold stackability_: notations.
Global Hint Unfold big_step_: notations.

(* ------------------------------------------------------------------------ *)
(** ** Non-overloaded notations *)

(* Monotonicity *)
Reserved Notation "Σ1 ≼ Σ2" (at level 60).

(* Partial monotonicity *)
Reserved Notation "s ⪯ s'" (at level 60).

(* Typing *)
Reserved Notation "m1 ⊑ m2" (at level 40).
Reserved Notation "T1 <: T2" (at level 40).
Reserved Notation "( Γ , Tthis )  ⊢ e : T " (at level 0, e, T at level 98).
Reserved Notation "( Γ , Tthis )  ⊩ es : Ts" (at level 0, es, Ts at level 98).

(* Scoping *)
Reserved Notation "( σ1 , L1 )  ⋖  ( σ2 , L2 )" (at level 0).
Reserved Notation "( σ1 , { l } )  ⋖  ( σ2 , L2 )" (at level 0).
Reserved Notation "( σ1 , L1 )  ⋖  ( σ2 , { l } )" (at level 0).
Reserved Notation "( σ1 , { l1 } )  ⋖  ( σ2 , { l2 } )" (at level 0).

(* Updates *)
Reserved Notation "[ x ↦  y ] σ" (at level 0).
Reserved Notation "[ x ⟼ y ] σ" (at level 0).
Notation "'dom' x" := (length x) (at level 0, x at level 1).

(* Sets of locations *)
Reserved Notation "L ⪽ σ" (at level 80).
Notation "l ∈ L" := (Ensembles.In Loc L l) (at level 80).
Notation "L ⊆ L'" := (Included Loc L L') (at level 60).
Notation "L ∪ L'" := (Union Loc L L') (at level 80, L' at next level).
Notation "{ l }" := (Singleton Loc l) (at level 0, l at level 99).
Notation "L ∪ { l }" := (Union Loc L (Singleton Loc l)) (at level 80).
Notation "{ l } ∪ L" := (Union Loc (Singleton Loc l) L) (at level 80).

(* Store subsets *)
Reserved Notation "L ⪽ σ" (at level 80).
Reserved Notation "{ l } ⪽ σ" (at level 80).

(* Definitional interpreter *)
Reserved Notation "⟦ e ⟧ ( σ , ρ , ψ , n )"   (at level 80, ψ at level 98, n at level 98).
Reserved Notation "⟦_ e _⟧ ( σ , ρ , ψ , n )" (at level 80).
