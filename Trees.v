(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines all the basic structures (as inductive types) of the project. Then some tools (for updating envs) are provided. *)

Require Import ssreflect ssrbool Sets.Ensembles Celsius.Tactics Coq.Lists.List Psatz.
Import ListNotations.

(** ** Language structures *)
(** *** Type modifiers *)
Inductive mode: Set := hot | warm | cold.
Notation "'@' u " := (u) (at level 20).

(** *** Basic types *)
Definition Var : Type := nat.
Definition Mtd : Type := nat.
Definition ClN : Type := nat.
Definition Tpe : Type := (ClN * mode).
Definition Loc : Type := nat.

(** *** Expression constructors *)
Inductive Expr: Type :=
| var   : Var -> Expr
| this
| fld   : Expr -> Var -> Expr
| mtd   : Expr -> Mtd -> (list Expr) -> Expr
| new   : ClN -> (list Expr) -> Expr
| asgn  : Expr -> Var -> Expr -> Expr -> Expr.

Inductive Method: Type :=
| method(μ: mode)(args: list Tpe)(out_type: Tpe)(body: Expr).

Inductive Field: Type :=
| field(type: Tpe)(expr: Expr).

Inductive Class: Type :=
| class(args: list Tpe)(fields: list Field)(methods: Mtd -> (option Method)).

Inductive Program: Type :=
| program(C: list Class)(entry: Expr).

(** *** Constructs *)
Definition Value : Type := Loc.
Definition ClassTable: Type := (ClN -> option Class).
Definition Env: Type   := list Value.
Definition Obj: Type   := (ClN * Env).
Definition Store: Type := list Obj.

Definition LocSet := (Ensemble Loc).
Notation "l ∈ L" := (Ensembles.In Loc L l) (at level 80).
Notation "L ⊆ L'" := (Included Loc L L') (at level 80).
Notation "L ∪ L'" := (Union Loc L L') (at level 80, L' at next level).
Notation "{ l }" := (Singleton Loc l).
Notation "L ∪ { l }" := (Union Loc L (Singleton Loc l)) (at level 80).
Notation "{ l } ∪ L" := (Union Loc (Singleton Loc l) L) (at level 80).


(** ** Helper functions *)
Definition dom {X: Type} (x: list X) : nat := (length x).
Definition getObj (l : list Obj):= nth_error l.
Definition getVal (l : list Value) := nth_error l.

Fixpoint removeTypes (l : list (Var*Tpe)) : (list Var) :=
  match l with
  | [] => []
  | ((v, t) :: l') => (v::(removeTypes l')) end.

Fixpoint update_one {X : Type} (position : nat) (value : X)(l : list X) : list X :=
  match (l, position) with
  | ([], _) => []
  | (_::t, 0) => value::t
  | (h::l', S n) => h::(update_one n value l')
  end.

Fixpoint update_list {X : Type} (positions : list nat) (values : list X) (l : list X) : list X :=
  match (positions, values) with
  | (x::xt, v::vt) => update_list xt vt (update_one x v l)
  | (_, _) => l end.

Notation "[ x ↦ v ] σ" := (update_one x v σ) (at level 0).
Notation "[ x ⟼ v ] σ" := (update_list x v σ) (at level 0).


(** ** Basic results on helper functions *)
(** We then have multiple easy results on those helper functions *)
Lemma getObj_last :
  forall σ C ρ,
    getObj (σ++[(C,ρ)]) (length σ) = Some (C, ρ).
Proof.
  induction σ; steps.
Qed.

Lemma getObj_last2 :
  forall σ C ρ l,
    l < dom σ ->
    getObj (σ++[(C,ρ)]) l = getObj σ l.
Proof.
  induction σ; simpl; intros; try lia.
  destruct l;
    steps;
    eauto with lia.
Qed.

Lemma getObj_last_empty :
  forall σ C C' ω l f v,
    getObj (σ++[(C,[])]) l = Some (C', ω) ->
    getVal ω f = Some v ->
    getObj σ l = Some (C', ω) /\ l < dom σ.
Proof.
  intros.
  assert (l < dom (σ ++ [(C,[])])).
  {
    unfold getObj, dom in *.
    eapply nth_error_Some.
    rewrite H; steps.
  }
  unfold dom in H1;
    rewrite app_length in H1 ;
    simpl in H1;
    fold (dom σ) in H1;
    rewrite_anywhere PeanoNat.Nat.add_1_r.
  apply Lt.le_lt_or_eq in H1 as [H1 | H1].
  + rewrite getObj_last2 in H; eauto using Lt.lt_S_n.
  + inversion H1; subst.
    rewrite getObj_last in H.
    invert_constructor_equalities; steps;
      destruct f; steps.
Qed.


Lemma update_one1 :
  forall X p v (l: list X),
    p < (length l) ->
    (nth_error [p ↦ v]l p) = Some v.
Proof.
  intros X p v; generalize dependent p.
  induction p; steps; eauto with lia.
Qed.

Lemma update_one2 :
  forall X p p' v (l: list X),
    p <> p' ->
    (nth_error [p ↦ v]l p') = (nth_error l p').
Proof.
  induction p; intros; destruct l ; destruct p' => //.
  simpl; eauto.
Qed.

Lemma update_one3 :
  forall X p v (l: list X),
    length ([p ↦ v]l) = length l.
Proof.
  intros X.
  induction p; steps.
Qed.

Lemma update_dom :
  forall (σ:Store) p v,
    dom [p ↦ v]σ = dom σ.
Proof.
  unfold dom; eauto using update_one3.
Qed.

Lemma update_one4 :
  forall X p (v v': X) l,
    nth_error [p ↦ v]l p = Some v' -> v = v'.
Proof.
  intros.
  assert (p < length l). {
    pose proof (nth_error_Some [p↦v]l p).
    rewrite update_one3 in H0; apply H0.
    rewrite H. discriminate.
  }
  rewrite update_one1 in H; eauto. injection H => //.
Qed.

Lemma dom_app:
  forall σ (C: ClN) (ω:Env),
    dom (σ ++ ((C, ω)::nil)) = S (dom σ).
Proof.
  intros.
  unfold dom; rewrite app_length; simpl; lia.
Qed.

Global Hint Resolve update_one1: updates.
Global Hint Resolve update_one2: updates.
Global Hint Resolve update_one3: updates.
Global Hint Resolve update_one4: updates.

Lemma getVal_update1 :
  forall ω o x,
    x < length ω -> (getVal [x ↦ o]ω x) = Some o.
Proof.
  unfold getVal; eauto with updates.
Qed.

Lemma getVal_update2 :
  forall ω o x x',
    x < length ω ->
    x <> x' ->
    getVal [x ↦ o]ω x' = getVal ω x'.
Proof.
  unfold getVal; eauto with updates.
Qed.


Lemma getObj_update1 :
  forall (σ: Store) o x,
    x < dom σ -> (getObj [x ↦ o]σ x) = Some o.
Proof.
  unfold getObj; eauto with updates.
Qed.

Lemma getObj_update2 :
  forall (σ: Store) o x x',
    x < dom σ ->
    x <> x' ->
    (getObj [x ↦ o]σ x') = (getObj σ x').
Proof.
  unfold getObj; eauto with updates.
Qed.

Lemma getObj_update3:
  forall σ o o' x x',
    getObj [x ↦ o]σ x' = Some o' ->
    x < dom σ ->
    ((x = x' /\ o = o') \/ (x <> x' /\ (getObj σ x' = Some o'))).
Proof.
  steps;
    destruct (PeanoNat.Nat.eq_dec x x') as [Heq | Hneq]; subst;
      [ rewrite getObj_update1 in H |
        rewrite getObj_update2 in H ]; steps.
Qed.

Lemma getObj_dom :
  forall (σ: Store) o l,
    (getObj σ l) = Some o ->
    l < (dom σ).
Proof.
  intros σ o.
  induction σ ; destruct l; steps; eauto with lia.
  apply (Lt.lt_n_S _ _ (IHσ _ H)) .
Qed.

Lemma nth_error_Some2 :
  forall {T:Type} e (v:T) f l,
    nth_error (e ++ [v]) f = Some l ->
    v = l \/ nth_error e f = Some l.
Proof.
  intros.
  assert (f < length (e++[v])) by (apply nth_error_Some; rewrite H; discriminate).
  move: H0; rewrite app_length; simpl; rewrite PeanoNat.Nat.add_1_r => H0.
  apply Lt.le_lt_or_eq in H0. destruct H0 as [H0 | H0].
  + right.
    apply Lt.lt_S_n in H0.
    rewrite nth_error_app1 in H => //.
  + left.
    injection H0 => H1; subst.
    rewrite nth_error_app2 in H => //.
    rewrite <- Minus.minus_diag_reverse in H.
    simpl in H. injection H => //.
Qed.

Lemma getVal_add:
  forall ω l l' f,
    getVal (ω ++ [l]) f = Some l' ->
    (f = length ω /\ l = l') \/ (f < length ω /\ getVal ω f = Some l').
Proof.
  unfold getVal.
  steps.
  assert (f < length ω \/ f = length ω) as [Hf | Hf];
    [
      apply Lt.le_lt_or_eq, Lt.lt_n_Sm_le;
      pose proof (nth_error_Some (ω ++ [l]) f) as Hf;
      rewrite app_length PeanoNat.Nat.add_1_r in Hf;
      apply Hf
    | rewrite_anywhere nth_error_app1
    | rewrite_anywhere nth_error_app2 ] ;
    steps;
    rewrite_anywhere PeanoNat.Nat.sub_diag; steps.
Qed.

Lemma getVal_update:
  forall ω l l' f f',
    getVal ([f ↦ l] ω) f' = Some l' ->
    (f = f' /\ l = l') \/ (f <> f' /\ getVal ω f' = Some l').
Proof.
  unfold getVal; steps.
  destruct (PeanoNat.Nat.eq_dec f f') as [Heq | Hneq]; subst.
  + apply update_one4 in H ; steps.
  + rewrite update_one2 in H; eauto ; steps.
Qed.

Global Hint Resolve getObj_dom: updates.

(** ** Tactics *)
(** Finally some tactics : *)

Ltac getObj_update :=
  match goal with
  | H: getObj [?x ↦ ?o] (?σ) ?x' = Some ?o' |- _ => eapply getObj_update3 in H; eauto with updates
  end.
Ltac getVal_update :=
  match goal with
  | H: getVal [?x ↦ ?o] (?σ) ?x' = Some ?o' |- _ => eapply getVal_update in H; eauto with updates
  end.


Ltac update_dom :=
  repeat rewrite_anywhere update_dom;
  repeat rewrite update_dom.


Ltac inSingleton :=
  match goal with
  | H: ?a ∈ Singleton Loc ?b |- _ => induction H
  | H: {?x} ?y |- _ => induction H
  end.
