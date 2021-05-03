(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of stackability between stores. When we evaluate expressions, it might have the effect of creating new objects. If we are in the middle of the creation of a new object, the newly added objects might point to the current [this], which might be not fully initialized. So those newly created objects might not be hot. However, they have to be fully initialized, and thus, warm. Stackability states exactly this: two stores [σ] and [σ'] are stackable if the new objects in [σ'] are warm. To prove this, we use the evaluator results of Eval.v, whith a custom proof the initialization case *)

From Celsius Require Export Trees Eval PartialMonotonicity Reachability Compatibility.
Require Import ssreflect ssrbool Psatz List.
Import ListNotations.
Open Scope nat_scope.

Global Hint Resolve partialMonotonicity_warm_monotone: stk.

(** ** Definitions and notations *)
Definition stackability (σ σ' : Store) :=
  forall l, l < (dom σ') -> ((σ' ⊨ l : warm) \/ (l < (dom σ))).
Notation "σ ≪ σ'" := (stackability σ σ') (at level 80).

(** ** Basic results *)
(** Reflexivity: *)
Lemma stackability_reflexivity:
  forall σ, σ ≪ σ.
Proof.
  unfold stackability. right => //.
Qed.
Global Hint Resolve stackability_reflexivity: stk.

(** The transitivity relation requires additional conditions between [σ2] and [σ3]: *)
Lemma stackability_transitivity:
  forall σ1 σ2 σ3,
    σ1 ≪ σ2 ->
    σ2 ≪ σ3 ->
    σ2 ⪯ σ3 ->
    σ2 ⊆ σ3 ->
    σ1 ≪ σ3.
Proof.
  unfold stackability; steps.
  specialize (H l). specialize (H0 l).
  steps; eauto with stk.
Qed.
Global Hint Resolve stackability_transitivity: stk.

(** Assignment *)
Lemma stackability_assignment :
  forall σ σ' l C ω ω',
    getObj σ l = Some (C, ω) ->
    length ω <= length ω' ->
    σ' = [l ↦ (C, ω')]σ ->
    σ ≪ σ'.
Proof.
  unfold stackability, dom; steps.
  rewrite_anywhere update_one3; steps.
Qed.
Global Hint Resolve stackability_assignment: stk.

(** ** Initialization results *)
(** Here we show a custom initialization result. Stackability does not verify [Freshness], as we cannot add any object to the store (it has to be a warn object). Here, we show that during the initialization process (foldleft of fields), the stores grows and the number of initialized fields grows too. Doing this, when we reach the end, we get a store with all initialized fields for the new object. We show it in the context of a strong induction. *)
(** Here is the technical result with [fold_left] *)
Lemma stackability_init_warm :
  forall F n args_val I s1 s2 C ρ,
    I < dom s1 ->
    getObj s1 I = Some (C, ρ) ->
    (forall k, k < n -> EvalMaintained stackability k) -> (**r strong induction *)
    fold_left (init_field args_val I n) F (Some s1) = Some s2 ->
    s1 ⊆ s2 /\ s1 ≪ s2 /\ s1 ⪯ s2 /\
    (exists ρ', getObj s2 I = Some (C, ρ') /\ (length F + length ρ <= length ρ')).
Proof.
  unfold EvalMaintained.
  move => F n args_val I s1 s2 C ρ H H0 H_strong H1.
  move : H1 H H0. move: ρ s1 s2 C.
  induction F; simpl; intros.
  + (**r [fields = []] *)
    invert_constructor_equalities.
    repeat rewrite_any || split ; eauto with stk pM cmpt.
  + (**r [fields = f::fields] *)
    destruct n; simpl in *; try solve [rewrite foldLeft_constant in H1 => //].
    destruct a as [ t e ] eqn:fieldEq.
    destruct_eval_with_name E.
    rewrite {2}/assign_new in H1.
    destruct (getObj s I) eqn:G ; try solve [rewrite foldLeft_constant in H1 => //].
    destruct o.
    eapply IHF in H1 as [H1_cmp1 [H_stk1 [H_pm1 [ ρ' [H_obj H_flen]]]]];
      eauto using getObj_update1, getObj_dom.
    assert ( length e0 <= length (e0 ++ [v])) as H_len_e0 by (rewrite app_length; lia).
    remember (e0 ++ [v]) as ω'.
    repeat split; eauto with pM cmpt stk.
    ++ eapply stackability_transitivity;
         [eapply H_strong | | |]; eauto with cmpt pM.
       eapply stackability_transitivity;
         [| eapply H_stk1 | |]; eauto with stk pM cmpt.
    ++ exists ρ' ; split.
       +++ assert (s1 ⊆ s) as H_cmpt2 by eauto with cmpt.
           assert (C = c) ; [eapply H_cmpt2 in H0 |]; steps.
       +++ steps; repeat rewrite_anywhere app_length.
           assert (s1 ⪯ s) as H_pm2 by eauto with pM.
           assert (length ρ <= length e0) as H_len_ρ. {
             specialize (H_pm2 I).
             unfold initializedFields in H_pm2.
             repeat rewrite_any.
             specialize (H_pm2 (repeat (field t e) (length ρ))).
             rewrite repeat_length in H_pm2; eauto.
           }
           steps; lia.
Qed.

(** Here is the wrapped up result, where technical verifications are made *)
Lemma stackability_init_fresh :
  forall n l0 (s: Store) σ' c,
    (forall k, k < n -> EvalMaintained stackability k) ->
    init (length s) l0 c (s ++ [(c, [])]) n = Some σ' -> s ≪ σ'.
Proof.
  destruct n; intros => //.
  simpl in *. repeat destruct_match => //.
  eapply stackability_init_warm in H0 ; eauto using getObj_last with stk pM cmpt.
  + steps; intros l1 Hl1.
    destruct (H0 l1 Hl1) as [H_warm | H_len] ; [left => // |].
    rewrite_anywhere dom_app.
    destruct_eq (l1 = dom s).
    ++ steps. left. repeat eexists || split ; eauto; lia.
    ++ eapply Lt.le_lt_or_eq in H_len as [H_len | H_len];
         [eauto using Lt.lt_S_n | steps].
  + unfold dom; rewrite app_length; simpl; lia.
Qed.
Global Hint Resolve stackability_init_fresh: stk.

(** ** Main stackability theorem *)
(** Using the custom initialization result, we get the main result: stackability is maintained by the evaluator *)
Theorem stackability_theorem :
  forall n, forall e σ σ' ρ v v',
      ⟦e⟧(σ, ρ, v)(n) = (Success v' σ') ->
      σ ≪ σ'.
Proof.
  apply (EvalMaintainedProp (fun σ σ' => σ ⪯ σ' /\ σ ⊆ σ' /\ σ ≪ σ')); (**r custom property *)
    unfoldProps; steps; eauto with pM cmpt stk.
  (* Initialization custom result : *)
  + eapply FreshnessInitMaintained; unfoldProps; eauto with pM.
  + eapply FreshnessInitMaintained; unfoldProps; eauto with cmpt.
  + eapply stackability_init_fresh; unfoldProps; eauto.
    intros. eapply_anywhere H; steps; lia.
Qed.
