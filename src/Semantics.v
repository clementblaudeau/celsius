(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the evaluator as a predicate and shows the equivalence with the functional version *)

From Celsius Require Export Language Notations Helpers LibTactics .
Require Import ssreflect ssrbool  Coq.Program.Tactics.
Import List Psatz Arith.
Import ListNotations.
Open Scope nat_scope.

(* Notation only used for the definition *)
Reserved Notation "'⟦'  e  '⟧p' '(' σ ',' ρ ',' v ')'  '-->'  '(' v0 ',' σ0 ')'" (at level 80).
Reserved Notation "'⟦_' e '_⟧p' '(' σ ',' ρ ',' v ')'  '-->'  '(' vl ',' σl ')'" (at level 80).
Inductive evalP : Expr -> Store -> Env -> Value -> Value -> Store -> Prop :=

(** variable *)
| e_var : forall σ x ρ ψ l,
    getVal ρ x = Some l ->
    ⟦ var x ⟧p (σ, ρ, ψ) --> (l, σ)

(** this *)
| e_this : forall σ ρ ψ,
    ⟦ this ⟧p (σ, ρ, ψ) --> (ψ, σ)

(** field access *)
| e_fld : forall σ ρ ψ e f v1 σ1 C ω v,
    ⟦ e ⟧p (σ, ρ, ψ) --> (v1, σ1) ->
    getObj σ1 v1 = Some (C, ω) ->
    getVal ω f = Some v ->
    ⟦ (fld e f) ⟧p (σ, ρ, ψ) --> (v, σ1)

(** method call : e0.m(args) *)
| e_mtd : forall σ e0 m el e2 ρ ψ l1 vl2 l3 σ1 σ2 σ3 C Args Flds Mtds f argsM T μ,
    ⟦ e0 ⟧p (σ, ρ, ψ) --> (l1, σ1) ->
    getObj σ1 l1 = Some (C, f) ->
    ⟦_ el _⟧p (σ1, ρ, ψ) --> (vl2, σ2) ->
    ct C = class Args Flds Mtds  ->
    Mtds m = Some (method μ argsM T e2) ->
    ⟦ e2 ⟧p (σ2, vl2, l1) --> (l3, σ3) ->
    ⟦ mtd e0 m el ⟧p (σ, ρ, ψ) --> (l3, σ3)

(** new class *)
| e_new : forall σ ρ ψ C Args Flds Mtds args vl__args σ1 σ3,
    ⟦_ args _⟧p (σ, ρ, ψ) --> (vl__args, σ1) ->
    ct C = class Args Flds Mtds ->
    let I := (length σ1) in
    initP C Flds I vl__args (σ1 ++ [(C, [])]) σ3 ->
    ⟦ new C args ⟧p (σ, ρ, ψ) --> (I, σ3)

(** assignment *)
| e_asgn : forall σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3,
    ⟦ e1 ⟧p (σ, ρ, ψ) --> (v1, σ1) ->
    ⟦ e2 ⟧p (σ1, ρ, ψ) --> (v2, σ2) ->
    ⟦ e' ⟧p ((assign v1 x v2 σ2), ρ, ψ) --> (v3, σ3) ->
    ⟦ asgn e1 x e2 e' ⟧p (σ, ρ, ψ) --> (v3, σ3)

where "'⟦' e '⟧p' '(' σ ',' ρ ',' v ')' '-->' '(' v0 ',' σ0 ')' "  := (evalP e σ ρ v v0 σ0)

with evalListP : list Expr -> Store -> Env -> Value -> list Value -> Store -> Prop :=
| el_nil : forall σ ρ ψ,
    ⟦_ [] _⟧p (σ, ρ, ψ) --> ([], σ)
| el_cons : forall σ ρ ψ e el l1 σ1 vl σ2,
    ⟦ e ⟧p (σ, ρ, ψ) --> (l1, σ1) ->
    ⟦_ el _⟧p (σ1, ρ, ψ) --> (vl, σ2) ->
    ⟦_ (e::el) _⟧p (σ, ρ, ψ) --> (l1::vl, σ2)
where "'⟦_' el '_⟧p' '(' σ ',' ρ ',' v ')' '-->' '(' vl ',' σ0 ')' "  := (evalListP el σ ρ v vl σ0)

with initP : ClN -> list Field -> Var -> Env -> Store -> Store -> Prop :=
| init_nil : forall C I ρ σ,
    initP C [] I ρ σ σ
| init_cons : forall C I ρ σ v T e flds σ1 σ2 σ3,
    ⟦ e ⟧p (σ, ρ, I) --> (v, σ1) ->
    assign_new I v σ1 = Some σ2 ->
    initP C flds I ρ σ2 σ3 ->
    initP C (field T e :: flds) I ρ σ σ3.


Global Instance notation_big_step_list_expr : notation_big_step (list Expr) (list Value) :=
  { big_step_ := evalListP }.

Global Instance notation_big_step_expr : notation_big_step Expr Value :=
  { big_step_ := evalP }.

Section evalP_ind.
  Variable P : forall e σ ρ ψ v σ', (evalP e σ ρ ψ v σ') -> Prop.
  Variable Pl : forall el σ ρ ψ vl σ', (evalListP el σ ρ ψ vl σ') -> Prop.
  Variable Pin : forall C flds ψ ρ σ σ', (initP C flds ψ ρ σ σ') -> Prop.

  Variable P_var : forall σ x ρ ψ l Hget,
      P (var x) σ ρ ψ l σ (e_var σ x ρ ψ l Hget).

  Variable P_this : forall σ ρ ψ,
      P this σ ρ ψ ψ σ (e_this σ ρ ψ).

  Variable P_fld : forall σ ρ ψ e f v1 σ1 C ω v EH__e0 H__getObj H__getVal
    (IH__e0: P e σ ρ ψ v1 σ1 (EH__e0)),
    P (fld e f) σ ρ ψ v σ1 (e_fld σ ρ ψ e f v1 σ1 C ω v EH__e0 H__getObj H__getVal).

  Variable P_mtd : forall σ e0 m el e2 ρ ψ v1 vl2 v3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj H__el Hct Hmth  H__e2
    (IH__e0: P e0 σ ρ ψ v1 σ1 H__e0)
    (IH__el: Pl el σ1 ρ ψ vl2 σ2 H__el)
    (IH__e2: P e2 σ2 vl2 v1 v3 σ3 H__e2),
    P( mtd e0 m el) σ ρ ψ v3 σ3 (e_mtd σ e0 m el e2 ρ ψ v1 vl2 v3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj H__el Hct Hmth H__e2).

  Variable P_new : forall σ ρ ψ C args vl__args σ1 σ3 Args Flds Mtds H__args H__ct H__init
    (IH__args: Pl args σ ρ ψ vl__args σ1 H__args)
    (IH__init: Pin C Flds (length σ1) vl__args (σ1 ++ [(C, [])]) σ3 H__init),
    P (new C args) σ ρ ψ (length σ1) σ3 (e_new σ ρ ψ C Args Flds Mtds args vl__args σ1 σ3 H__args H__ct H__init).

  Variable P_asgn :  forall σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e'
    (IH__e1: P e1 σ ρ ψ v1 σ1 H__e1)
    (IH__e2: P e2 σ1 ρ ψ v2 σ2 H__e2)
    (IH__e': P e' (assign v1 x v2 σ2) ρ ψ v3 σ3 H__e'),
    P (asgn e1 x e2 e') σ ρ ψ v3 σ3 (e_asgn σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e').

  Variable Pl_nil : forall σ ρ ψ, Pl [] σ ρ ψ [] σ (el_nil σ ρ ψ).

  Variable Pl_cons : forall σ ρ ψ e el v1 σ1 vl σ2 H__e H__el
      (IH__e: P e σ ρ ψ v1 σ1 H__e)
      (IH__el: Pl el σ1 ρ ψ vl σ2 H__el),
      Pl (e::el) σ ρ ψ (v1::vl) σ2 (el_cons σ ρ ψ e el v1 σ1 vl σ2 H__e H__el).

  Variable Pin_nil: forall C I ρ σ, Pin C [] I ρ σ σ (init_nil C I ρ σ).

  Variable Pin_cons : forall C I ρ σ v T e flds σ1 σ2 σ3 H__e H__assign H__flds
      (IH__e: P e σ ρ I v σ1 H__e)
      (IH__flds: Pin C flds I ρ σ2 σ3 H__flds),
      Pin C (field T e :: flds) I ρ σ σ3 (init_cons C I ρ σ v T e flds σ1 σ2 σ3 H__e H__assign H__flds).

  Fixpoint evalP_ind2 e σ ρ ψ v σ' (eval : evalP e σ ρ ψ v σ') : P e σ ρ ψ v σ' eval :=
    match eval with
    | e_var σ x ρ ψ v Hget => P_var σ x ρ ψ v Hget
    | e_this σ ρ ψ => P_this σ ρ ψ
    | e_fld σ ρ ψ e0 x l1 σ1 C f v1 H__e0 Hobj Hval =>
        P_fld σ ρ ψ e0 x l1 σ1 C f v1 H__e0 Hobj Hval (evalP_ind2 e0 σ ρ ψ l1 σ1 H__e0)
    | e_mtd σ e0 m el e2 ρ ψ l1 vl2 l3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj H__el Hct Hmth H__e2 =>
        P_mtd σ e0 m el e2 ρ ψ l1 vl2 l3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj H__el Hct Hmth H__e2
              (evalP_ind2 e0 σ ρ ψ l1 σ1 H__e0)
              (evalListP_ind2 el σ1 ρ ψ vl2 σ2 H__el)
              (evalP_ind2 e2 σ2 vl2 l1 l3 σ3 H__e2)
    | e_new σ ρ ψ C Args Flds Mtds args vl__args σ1 σ3 H__args H__ct H__init =>
        P_new σ ρ ψ C args vl__args σ1 σ3 Args Flds Mtds H__args H__ct H__init
              (evalListP_ind2 args σ ρ ψ vl__args σ1 H__args)
              (initP_ind2 C Flds (length σ1) vl__args (σ1 ++ [(C, [])]) σ3 H__init)
    | e_asgn σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e' =>
        P_asgn σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e'
               (evalP_ind2 e1 σ ρ ψ v1 σ1 H__e1)
               (evalP_ind2 e2 σ1 ρ ψ v2 σ2 H__e2)
               (evalP_ind2 e' (assign v1 x v2 σ2) ρ ψ v3 σ3 H__e')
    end

  with evalListP_ind2 el σ ρ ψ vl σ' evalList : Pl el σ ρ ψ vl σ' evalList :=
         match evalList  with
         | el_nil σ ρ ψ  => Pl_nil σ ρ ψ
         | el_cons σ ρ ψ e el l1 σ1 vl σ2 H__e H__el =>
             Pl_cons σ ρ ψ e el l1 σ1 vl σ2 H__e H__el
                     (evalP_ind2 e σ ρ ψ l1 σ1 H__e)
                     (evalListP_ind2 el σ1 ρ ψ vl σ2 H__el)
         end

  with initP_ind2 C flds ψ (ρ:Env) (σ σ':Store) H__init: Pin C flds ψ ρ σ σ' H__init :=
         match H__init with
         | init_nil C ψ ρ σ => Pin_nil C ψ ρ σ
         | init_cons C ψ ρ σ v T e flds σ1 σ2 σ3 H__e H__assign H__flds =>
             Pin_cons C ψ ρ σ v T e flds σ1 σ2 σ3 H__e H__assign H__flds
                      (evalP_ind2 e σ ρ ψ v σ1 H__e)
                      (initP_ind2 C flds ψ ρ σ2 σ3 H__flds)
         end.

  Lemma evalP_multi_ind:
    (forall e σ ρ ψ v σ' H__eval, P e σ ρ ψ v σ' H__eval) /\
      (forall el σ ρ ψ vl σ' H__evalList, Pl el σ ρ ψ vl σ' H__evalList) /\
      (forall C flds ψ ρ σ σ' H__init, Pin C flds ψ ρ σ σ' H__init).
  Proof.
    splits; intros.
    + apply evalP_ind2.
    + apply evalListP_ind2.
    + apply initP_ind2.
  Qed.

End evalP_ind.


(** ** Conservation result *)
(** The monotonicity on the size of the store is easy to obtain via induction *)
Theorem dom_theorem:
  (forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> dom σ <= dom σ') /\
    ( forall el σ ρ ψ vl σ',
        ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> dom σ <= dom σ') /\
    ( forall C fls ψ ρ σ σ',
        initP C fls ψ ρ σ σ' -> dom σ <= dom σ').
Proof.
  eapply evalP_multi_ind;
    unfold assign, assign_new;
    steps; updates; try lia.
Qed.

Corollary evalP_dom:
  forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> dom σ <= dom σ'.
Proof.
  apply dom_theorem.
Qed.

Corollary evalListP_dom:
   forall el σ ρ ψ vl σ',
      ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> dom σ <= dom σ'.
Proof.
  apply dom_theorem.
Qed.

Corollary initP_dom:
  forall C fls ψ ρ σ σ',
      initP C fls ψ ρ σ σ' -> dom σ <= dom σ'.
Proof.
  apply dom_theorem.
Qed.

Ltac eval_dom :=
  repeat match goal with
         | H: ⟦ ?e ⟧p (?σ, ?ρ, ?ψ) --> (?v, ?σ') |- _ =>
             let fresh := fresh "H_dom" in
             add_hypothesis fresh (evalP_dom e σ ρ ψ v σ' H)
         | H: ⟦_ ?el _⟧p (?σ, ?ρ, ?ψ) --> (?vl, ?σ') |- _ =>
             let fresh := fresh "H_dom" in
             add_hypothesis fresh (evalListP_dom el σ ρ ψ vl σ' H)
         | H: initP ?C ?fls ?ψ ?ρ ?σ ?σ' |- _ =>
             let fresh := fresh "H_dom" in
             add_hypothesis fresh (initP_dom C fls ψ ρ σ σ' H)
         end.
