From Celsius Require Import Language.
Import List Ensembles.

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

Class notation_big_step (A B : Type) :=
  big_step_ : A -> Store -> Env -> Value -> B -> Store -> Prop.
Notation "'⟦' x '⟧' '(' σ ',' ρ ',' ψ ')'  '-->'  '(' y ',' σ' ')'" := (big_step_ x σ ρ ψ y σ') (at level 80).

Global Hint Unfold dash_: notations.
Global Hint Unfold dash_arrow_: notations.
Global Hint Unfold dash_colon_: notations.
Global Hint Unfold stackability_: notations.
Global Hint Unfold big_step_: notations.


(** ** Non-overloaded notations *)

(** *** Store typing properties *)
Reserved Notation "Σ1 ▷ Σ2" (at level 60). (* Authority *)
Reserved Notation "Σ1 ≼ Σ2" (at level 60). (* Monotonicity *)

(** *** Store properties *)
Reserved Notation "σ ⪨ σ'" (at level 60). (* Compatibility *)
Reserved Notation "s ⪯ s'" (at level 60). (* Partial monotonicity *)
Reserved Notation "s ⊵ s'" (at level 60). (* Strong authority *)

(** *** Typing *)
Reserved Notation "m1 ⊑ m2" (at level 40).
Reserved Notation "T1 <: T2" (at level 40).
Reserved Notation "( Γ , T )  ⊢ e : U " (at level 0, e, U at level 98).
Reserved Notation "( Γ , T )  ⊩ es : Us" (at level 0, es, Us at level 98).

(** *** Scoping *)
Reserved Notation "( σ1 , L1 )  ⋖  ( σ2 , L2 )" (at level 0).
Reserved Notation "( σ1 , { l } )  ⋖  ( σ2 , L2 )" (at level 0).
Reserved Notation "( σ1 , L1 )  ⋖  ( σ2 , { l } )" (at level 0).
Reserved Notation "( σ1 , { l1 } )  ⋖  ( σ2 , { l2 } )" (at level 0).
Reserved Notation "σ1  ⇝ σ2 ⋖ L" (at level 99).


(** *** Updates *)
Reserved Notation "[ x ↦  v ] σ" (at level 0).
Reserved Notation "[ x ⟼ v ] σ" (at level 0).
Notation "'dom' x" := (length x) (at level 0, x at level 1).


(** *** Sets of locations *)
Reserved Notation "L ⪽ σ" (at level 80).
Notation "l ∈ L" := (Ensembles.In Loc L l) (at level 80).
Notation "L ⊆ L'" := (Included Loc L L') (at level 60).
Notation "L ∪ L'" := (Union Loc L L') (at level 80, L' at next level).
Notation "{ l }" := (Singleton Loc l) (at level 0, l at level 99).
Notation "L ∪ { l }" := (Union Loc L (Singleton Loc l)) (at level 80).
Notation "{ l } ∪ L" := (Union Loc (Singleton Loc l) L) (at level 80).

(** *** Store subsets *)
Reserved Notation "L ⪽ σ" (at level 80).
Reserved Notation "{ l } ⪽ σ" (at level 80).
