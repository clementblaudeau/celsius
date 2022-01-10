From Celsius Require Import Language Notations Tactics.
Import List ListNotations Psatz Ensembles.
Require Import ssreflect ssrbool.
Open Scope list_scope.

(** ** Helper functions *)
Definition getObj (l : list Obj)    : Loc -> option Obj := nth_error l.
Definition getVal (l : list Value)  : Loc -> option Value := nth_error l.
Definition getType (Σ: StoreTyping) (l: Loc): option Tpe := option_map snd (find (fun '(l', _) => Nat.eqb l l') Σ).
Definition typeLookup (Γ: EnvTyping): Loc -> option Tpe := nth_error Γ.
Definition in_dom (Σ: StoreTyping) (l: Loc) := Exists (fun '(l', _) => Nat.eqb l l') Σ.


Fixpoint removeTypes (l : list (Var*Tpe)) : (list Var) :=
  match l with
  | [] => []
  | ((v, t) :: l') => (v::(removeTypes l'))
  end.

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

Notation "[ x ↦  v ] σ" := (update_one x v σ) (at level 0).
Notation "[ x ⟼ v ] σ" := (update_list x v σ) (at level 0).

(** Update store with new value in local env : adds a new field to an existing object *)
Definition assign_new (obj: Value) (v: Value) (σ: Store) : option Store :=
  match (getObj σ obj) with
  | Some (C, fields) => Some ([ obj ↦ (C, fields++[v])] σ)
  | None => None (* ? *)
  end.

(** Update store with update in local env : update an already-existing field of an existing object*)
Definition assign (obj: Value) (f: Var) (v: Value) (σ: Store) : Store :=
  match (getObj σ obj) with
  | Some (C, fields) => ([ obj ↦ (C, [f ↦ v]fields)] σ)
  | None => σ (* ? *)
  end.

(** Update store with new values : update already existing fields of an existing object*)
Definition assign_list (v0: Value) (x: list Var) (v: list Value) (σ: Store) : Store :=
  match (getObj σ v0) with
  | Some (C, fields) => [v0 ↦ (C, [x ⟼ v]fields)] σ
  | None => σ
  end.

Definition fieldType C f :=
  match ct C with
  | None => None
  | Some (class _ flds _ ) =>
    match nth_error flds f with
    | Some (field (T, μ) _) => Some (T, μ)
    | _ => None
    end
  end.

Definition methodInfo C m :=
  match ct C with
  | None => None
  | Some (class _ _ methods) =>
    match methods m with
    | None => None
    | Some (method μ Ts retT e) => Some (μ, Ts, retT, e)
    end
  end.



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
    l < (dom σ) ->
    getObj (σ++[(C,ρ)]) l = getObj σ l.
Proof.
  induction σ; simpl; intros; try lia.
  destruct l;
    steps;
    eauto with lia.
Qed.

Lemma getObj_last_empty :
  forall (σ: Store) C C' ω l f v,
    getObj (σ++[(C,[])]) l = Some (C', ω) ->
    getVal ω f = Some v ->
    getObj σ l = Some (C', ω) /\ l < dom σ.
Proof.
  intros.
  assert (l < dom (σ ++ [(C,[])])).
  {
    unfold getObj in *.
    eapply nth_error_Some.
    rewrite H; steps.
  }
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
   eauto using update_one3.
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
  rewrite update_one1 in H; eauto.
Qed.

Lemma dom_app:
  forall (σ: Store) (C: ClN) (ω:Env),
    dom (σ ++ ((C, ω)::nil)) = S (dom σ).
Proof.
  intros.
   rewrite app_length; simpl; lia.
Qed.

Lemma length_plus_1:
  forall (ρ:Env) v,
    length(ρ ++ [v]) = S(length(ρ)).
Proof.
  intros.
  rewrite app_length; simpl; lia.
Qed.


#[export] Hint Extern 1 => rewrite (update_one3): updates.
#[export] Hint Extern 1 => rewrite (update_dom): updates.
#[export] Hint Extern 1 => rewrite (length_plus_1): updates.
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

(*
Lemma getType_dom:
  forall (Σ: StoreTyping) l T,
    getType Σ l = Some T -> l < dom Σ.
Proof.
  intros.
  unfold getType in *.
  destruct (find (fun '(l', _) => Nat.eqb l l') Σ) eqn:H__e; steps.
  apply find_some in H__e; steps.
  Search (nth _ _ _ = _ -> _).
  apply  in H; steps.

  apply nth_error_Some.
  unfold getType in *; eauto.
Qed. *)
Lemma getType_in_dom:
  forall (Σ: StoreTyping) l T,
    getType Σ l = Some T -> in_dom Σ l.
Proof.
  intros.
  unfold getType, option_map in H; steps.
  apply find_some in matched; steps.
  unfold in_dom.
  apply Exists_exists; eauto.
Qed.

Lemma in_dom_map:
  forall (Σ: StoreTyping) l f,
    in_dom (map (fun '(l, T) => (l, f l T)) Σ) l <-> in_dom Σ l.
Proof.
  unfold in_dom.
  induction Σ; steps; eauto.
  - inversion H; steps; eauto using Exists.
    eapply Exists_cons_tl, IHΣ; eauto.
  - inversion H; steps; eauto using Exists.
    eapply Exists_cons_tl, IHΣ; eauto.
Qed.

Lemma in_dom_dec:
  forall Σ l,
    {in_dom Σ l} + {~ in_dom Σ l}.
Proof.
  intros.
  unfold in_dom in *.
  eapply Exists_dec.
  intros [l' _].
  destruct (Nat.eqb l l'); steps.
Qed.


Lemma getType_in_dom_map:
  forall (Σ: StoreTyping) l T f,
    getType (map (fun '(l, T) => (l, f l T)) Σ) l = Some T -> in_dom Σ l.
Proof.
  intros. eapply in_dom_map, getType_in_dom; eauto.
Qed.

Lemma getType_none:
  forall (Σ: StoreTyping) l,
    in_dom Σ l ->
    getType Σ l <> None.
Proof.
  intros.
  unfold getType, option_map, in_dom in *; steps.
  clear H0. move: l H matched.
  induction Σ; steps; eauto; inversion H; steps; eauto.
Qed.

Lemma getType_map:
  forall (Σ: StoreTyping) f l T,
    getType Σ l = Some T ->
    getType (map (fun '(l, T) => (l, f l T)) Σ) l = Some (f l T).
Proof.
  induction Σ; steps.
  unfold getType, option_map in H.
  destruct_match; try invert_constructor_equalities; subst; try discriminate.
  steps.
  - apply PeanoNat.Nat.eqb_eq in matched0; steps.
    unfold getType; steps.
    apply PeanoNat.Nat.eqb_neq in matched; steps.
  - unfold getType, option_map in IHΣ.
    specialize (IHΣ f l t0).
    rewrite matched in IHΣ. simpl in *.
    specialize (IHΣ eq_refl).
    steps.
    unfold getType, option_map. steps.
Qed.


Lemma getVal_dom:
  forall ρ f l,
    getVal ρ f = Some l -> f < dom ρ.
Proof.
  intros.
  apply nth_error_Some.
  unfold getVal in *; eauto.
Qed.


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
