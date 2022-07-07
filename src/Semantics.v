(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(* This files defines the big step semantics and an induction predicate on the rules *)

From Celsius Require Export Helpers.


(* ------------------------------------------------------------------------ *)
(** ** Big step semantics *)

(* Notation only used for the definition *)
Reserved Notation "'⟦'  e  '⟧p' '(' σ ',' ρ ',' v ')'  '-->'  '(' v0 ',' σ0 ')'" (at level 80).
Reserved Notation "'⟦_' e '_⟧p' '(' σ ',' ρ ',' v ')'  '-->'  '(' vl ',' σl ')'" (at level 80).

(* Big step semantics for an expression *)
Inductive evalP : Expr -> Store -> Env -> Loc -> Loc -> Store -> Prop :=

(* Variable : we retrieve the value of x in the local environment ρ *)
| bs_var : forall σ x ρ ψ l,
    getVal ρ x = Some l ->
    ⟦ e_var x ⟧p (σ, ρ, ψ) --> (l, σ)

(* This : we return the current this pointer ψ *)
| bs_this : forall σ ρ ψ,
    ⟦ e_this ⟧p (σ, ρ, ψ) --> (ψ, σ)

(* Field access : we compute the object e, and fetch the value of the field in the resulting
object *)
| bs_fld : forall σ ρ ψ e f v1 σ1 C ω v,
    ⟦ e ⟧p (σ, ρ, ψ) --> (v1, σ1) ->
    getObj σ1 v1 = Some (C, ω) ->
    getVal ω f = Some v ->
    ⟦ (e_fld e f) ⟧p (σ, ρ, ψ) --> (v, σ1)

(* Method call : we first compute the object on which the method will be called, then the arguments,
and then we fetch the body of the method which we execute with the arguments as local environment *)
| bs_mtd : forall σ e0 m el e2 ρ ψ l1 vl2 l3 σ1 σ2 σ3 C Args Flds Mtds f argsM T μ,
    ⟦ e0 ⟧p (σ, ρ, ψ) --> (l1, σ1) ->
    getObj σ1 l1 = Some (C, f) ->
    ⟦_ el _⟧p (σ1, ρ, ψ) --> (vl2, σ2) ->
    ct C = class Args Flds Mtds  ->
    Mtds m = Some (method μ argsM T e2) ->
    ⟦ e2 ⟧p (σ2, vl2, l1) --> (l3, σ3) ->
    ⟦ e_mtd e0 m el ⟧p (σ, ρ, ψ) --> (l3, σ3)

(* New instance : we compute the arguments and call the special procedure [initP] to initialize the
new instance *)
| bs_new : forall σ ρ ψ C Args Flds Mtds args vl__args σ1 σ3,
    ⟦_ args _⟧p (σ, ρ, ψ) --> (vl__args, σ1) ->
    ct C = class Args Flds Mtds ->
    let I := (length σ1) in
    initP C I 0 vl__args (σ1 ++ [(C, [])]) σ3 ->
    ⟦ e_new C args ⟧p (σ, ρ, ψ) --> (I, σ3)

(* Assignment : we compute the object, the value and update the field x. Then we compute the other
expression e' *)
| bs_asgn : forall σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3,
    ⟦ e1 ⟧p (σ, ρ, ψ) --> (v1, σ1) ->
    ⟦ e2 ⟧p (σ1, ρ, ψ) --> (v2, σ2) ->
    ⟦ e' ⟧p ((assign v1 x v2 σ2), ρ, ψ) --> (v3, σ3) ->
    ⟦ e_asgn e1 x e2 e' ⟧p (σ, ρ, ψ) --> (v3, σ3)

where "'⟦' e '⟧p' '(' σ ',' ρ ',' v ')' '-->' '(' v0 ',' σ0 ')' "  := (evalP e σ ρ v v0 σ0)

(* Big step semantics for a list of expressions (mainly a fold left) *)
with evalListP : list Expr -> Store -> Env -> Loc -> list Loc -> Store -> Prop :=

| bs_nil : forall σ ρ ψ,
    ⟦_ [] _⟧p (σ, ρ, ψ) --> ([], σ)

| bs_cons : forall σ ρ ψ e el l1 σ1 vl σ2,
    ⟦ e ⟧p (σ, ρ, ψ) --> (l1, σ1) ->
    ⟦_ el _⟧p (σ1, ρ, ψ) --> (vl, σ2) ->
    ⟦_ (e::el) _⟧p (σ, ρ, ψ) --> (l1::vl, σ2)

where "'⟦_' el '_⟧p' '(' σ ',' ρ ',' v ')' '-->' '(' vl ',' σ0 ')' "  := (evalListP el σ ρ v vl σ0)

(* Initialization procedure: we compute the mandatory field initializers for the fields between x
and (length Flds) *)
with initP : ClN -> Var -> nat -> Env -> Store -> Store -> Prop :=

(* No fields left to initialize *)
| init_nil : forall C I ρ σ Args Flds Mtds,
    ct C = class Args Flds Mtds ->
    initP C I (dom Flds) ρ σ σ

(* We compute the value of the defining expression, then update the store (which can already a value
for x) and proceed *)
| init_cons : forall C I x ρ σ v T e Args Flds Mtds σ1 σ2 σ3,
    ct C = class Args Flds Mtds ->
    nth_error Flds x = Some (field T e) ->
    ⟦ e ⟧p (σ, ρ, I) --> (v, σ1) ->
    assign_new I x v σ1 = Some σ2 ->
    initP C I (S x) ρ σ2 σ3 ->
    initP C I x ρ σ σ3.

(* Overloaded notations between expressions and lists of expressions *)
Global Instance notation_big_step_list_expr : notation_big_step (list Expr) (list Loc) :=
  { big_step_ := evalListP }.
Global Instance notation_big_step_expr : notation_big_step Expr Loc :=
  { big_step_ := evalP }.
Global Hint Unfold big_step_: core.
Global Hint Unfold notation_big_step_expr: core.
Global Hint Unfold notation_big_step_list_expr: core.

(* ------------------------------------------------------------------------ *)
(** ** Induction predicate *)

Section evalP_ind.
  (* We define a custom induction predicate *)

  Variable P : forall e σ ρ ψ v σ', (evalP e σ ρ ψ v σ') -> Prop.
  Variable Pl : forall el σ ρ ψ vl σ', (evalListP el σ ρ ψ vl σ') -> Prop.
  Variable Pin : forall C ψ x ρ σ σ', (initP C ψ x ρ σ σ') -> Prop.

  Variable P_var : forall σ x ρ ψ l Hget,
      P (e_var x) σ ρ ψ l σ (bs_var σ x ρ ψ l Hget).

  Variable P_this : forall σ ρ ψ,
      P e_this σ ρ ψ ψ σ (bs_this σ ρ ψ).

  Variable P_fld : forall σ ρ ψ e f v1 σ1 C ω v EH__e0 H__getObj H__getVal
    (IH__e0: P e σ ρ ψ v1 σ1 (EH__e0)),
    P (e_fld e f) σ ρ ψ v σ1 (bs_fld σ ρ ψ e f v1 σ1 C ω v EH__e0 H__getObj H__getVal).

  Variable P_mtd : forall σ e0 m el e2 ρ ψ v1 vl2 v3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj H__el Hct Hmth  H__e2
    (IH__e0: P e0 σ ρ ψ v1 σ1 H__e0)
    (IH__el: Pl el σ1 ρ ψ vl2 σ2 H__el)
    (IH__e2: P e2 σ2 vl2 v1 v3 σ3 H__e2),
    P( e_mtd e0 m el) σ ρ ψ v3 σ3 (bs_mtd σ e0 m el e2 ρ ψ v1 vl2 v3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj H__el Hct Hmth H__e2).

  Variable P_new : forall σ ρ ψ C args vl__args σ1 σ3 Args Flds Mtds H__args H__ct H__init
    (IH__args: Pl args σ ρ ψ vl__args σ1 H__args)
    (IH__init: Pin C (length σ1) 0 vl__args (σ1 ++ [(C, [])]) σ3 H__init),
    P (e_new C args) σ ρ ψ (length σ1) σ3 (bs_new σ ρ ψ C Args Flds Mtds args vl__args σ1 σ3 H__args H__ct H__init).

  Variable P_asgn :  forall σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e'
    (IH__e1: P e1 σ ρ ψ v1 σ1 H__e1)
    (IH__e2: P e2 σ1 ρ ψ v2 σ2 H__e2)
    (IH__e': P e' (assign v1 x v2 σ2) ρ ψ v3 σ3 H__e'),
    P (e_asgn e1 x e2 e') σ ρ ψ v3 σ3 (bs_asgn σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e').

  Variable Pl_nil : forall σ ρ ψ, Pl [] σ ρ ψ [] σ (bs_nil σ ρ ψ).

  Variable Pl_cons : forall σ ρ ψ e el v1 σ1 vl σ2 H__e H__el
      (IH__e: P e σ ρ ψ v1 σ1 H__e)
      (IH__el: Pl el σ1 ρ ψ vl σ2 H__el),
      Pl (e::el) σ ρ ψ (v1::vl) σ2 (bs_cons σ ρ ψ e el v1 σ1 vl σ2 H__e H__el).

  Variable Pin_nil: forall C I ρ σ Args Flds Mtds H__ct,
      Pin C I (length Flds) ρ σ σ (init_nil C I ρ σ Args Flds Mtds H__ct).

  Variable Pin_cons : forall C I x ρ σ v T e Args Flds Mtds σ1 σ2 σ3 H__ct H__fld H__e H__assign H__init
      (IH__e: P e σ ρ I v σ1 H__e)
      (IH__init: Pin C I (S x) ρ σ2 σ3 H__init),
      Pin C I x ρ σ σ3 (init_cons C I x ρ σ v T e Args Flds Mtds σ1 σ2 σ3 H__ct H__fld H__e H__assign H__init).

  Fixpoint evalP_ind2 e σ ρ ψ v σ' (eval : evalP e σ ρ ψ v σ') : P e σ ρ ψ v σ' eval :=
    match eval with
    | bs_var σ x ρ ψ v Hget => P_var σ x ρ ψ v Hget
    | bs_this σ ρ ψ => P_this σ ρ ψ
    | bs_fld σ ρ ψ e0 x l1 σ1 C f v1 H__e0 Hobj Hval =>
        P_fld σ ρ ψ e0 x l1 σ1 C f v1 H__e0 Hobj Hval (evalP_ind2 e0 σ ρ ψ l1 σ1 H__e0)
    | bs_mtd σ e0 m el e2 ρ ψ l1 vl2 l3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj H__el Hct Hmth H__e2 =>
        P_mtd σ e0 m el e2 ρ ψ l1 vl2 l3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj H__el Hct Hmth H__e2
              (evalP_ind2 e0 σ ρ ψ l1 σ1 H__e0)
              (evalListP_ind2 el σ1 ρ ψ vl2 σ2 H__el)
              (evalP_ind2 e2 σ2 vl2 l1 l3 σ3 H__e2)
    | bs_new σ ρ ψ C Args Flds Mtds args vl__args σ1 σ3 H__args H__ct H__init =>
        P_new σ ρ ψ C args vl__args σ1 σ3 Args Flds Mtds H__args H__ct H__init
              (evalListP_ind2 args σ ρ ψ vl__args σ1 H__args)
              (initP_ind2 C (length σ1) 0 vl__args (σ1 ++ [(C, [])]) σ3 H__init)
    | bs_asgn σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e' =>
        P_asgn σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e'
               (evalP_ind2 e1 σ ρ ψ v1 σ1 H__e1)
               (evalP_ind2 e2 σ1 ρ ψ v2 σ2 H__e2)
               (evalP_ind2 e' (assign v1 x v2 σ2) ρ ψ v3 σ3 H__e')
    end

  with evalListP_ind2 el σ ρ ψ vl σ' evalList : Pl el σ ρ ψ vl σ' evalList :=
         match evalList  with
         | bs_nil σ ρ ψ  => Pl_nil σ ρ ψ
         | bs_cons σ ρ ψ e el l1 σ1 vl σ2 H__e H__el =>
             Pl_cons σ ρ ψ e el l1 σ1 vl σ2 H__e H__el
                     (evalP_ind2 e σ ρ ψ l1 σ1 H__e)
                     (evalListP_ind2 el σ1 ρ ψ vl σ2 H__el)
         end

  with initP_ind2 C ψ x (ρ:Env) (σ σ':Store) H__init: Pin C ψ x ρ σ σ' H__init :=
         match H__init with
         | init_nil C ψ ρ σ Args Flds Mtds H__ct => Pin_nil C ψ ρ σ Args Flds Mtds H__ct
         | init_cons C ψ x ρ σ v T e Args Flds Mtds σ1 σ2 σ3 H__ct H__fld H__e H__assign H__init  =>
             Pin_cons C ψ x ρ σ v T e Args Flds Mtds σ1 σ2 σ3 H__ct H__fld H__e H__assign H__init
                      (evalP_ind2 e σ ρ ψ v σ1 H__e)
                      (initP_ind2 C ψ (S x) ρ σ2 σ3 H__init)
         end.

  Lemma evalP_multi_ind:
    (forall e σ ρ ψ v σ' H__eval, P e σ ρ ψ v σ' H__eval) /\
      (forall el σ ρ ψ vl σ' H__evalList, Pl el σ ρ ψ vl σ' H__evalList) /\
      (forall C ψ x ρ σ σ' H__init, Pin C ψ x ρ σ σ' H__init).
  Proof.
    splits; intros.
    + apply evalP_ind2.
    + apply evalListP_ind2.
    + apply initP_ind2.
  Qed.

End evalP_ind.

(* ------------------------------------------------------------------------ *)
(** ** Conservation result *)
(* The monotonicity on the size of the store is easy to obtain via induction *)

Theorem dom_theorem:
  (forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> dom σ <= dom σ') /\
    ( forall el σ ρ ψ vl σ',
        ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> dom σ <= dom σ') /\
    ( forall C ψ x ρ σ σ',
        initP C ψ x ρ σ σ' -> dom σ <= dom σ').
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
  forall C ψ x ρ σ σ',
      initP C ψ x ρ σ σ' -> dom σ <= dom σ'.
Proof.
  apply dom_theorem.
Qed.

Lemma init_field:
  forall C ψ x ρ σ σ' Args Flds Mtds,
    ct C = class Args Flds Mtds ->
    initP C ψ x ρ σ σ' ->
    x <= length Flds.
Proof.
  intros. move: Args Flds Mtds H.
  induction H0; intros; cross_rewrites => //.
  apply IHinitP in H. lia.
Qed.


Ltac eval_dom :=
  repeat match goal with
         | H: ⟦ ?e ⟧p (?σ, ?ρ, ?ψ) --> (?v, ?σ') |- _ =>
             let fresh := fresh "H_dom" in
             add_hypothesis fresh (evalP_dom e σ ρ ψ v σ' H)
         | H: ⟦_ ?el _⟧p (?σ, ?ρ, ?ψ) --> (?vl, ?σ') |- _ =>
             let fresh := fresh "H_dom" in
             add_hypothesis fresh (evalListP_dom el σ ρ ψ vl σ' H)
         | H: ⟦ ?e ⟧ (?σ, ?ρ, ?ψ) --> (?v, ?σ') |- _ =>
             let fresh := fresh "H_dom" in
             add_hypothesis fresh (evalP_dom e σ ρ ψ v σ' H)
         | H: ⟦?el ⟧ (?σ, ?ρ, ?ψ) --> (?vl, ?σ') |- _ =>
             let fresh := fresh "H_dom" in
             add_hypothesis fresh (evalListP_dom el σ ρ ψ vl σ' H)
         | H: initP ?C ?ψ ?x ?ρ ?σ ?σ' |- _ =>
             let fresh := fresh "H_dom" in
             add_hypothesis fresh (initP_dom C ψ x ρ σ σ' H)
         end.
