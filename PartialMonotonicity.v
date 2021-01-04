From Celsius Require Export Trees Eval Reachability Tactics Compatibility strongInduction.
Require Import ssreflect ssrbool.


Require Import List.
Import ListNotations.
Open Scope nat_scope.

Module PartialMonotonicity.
  Import Reachability.Reachability.
  Import Eval.Evaluator.
  Import Compatibility.Compatibility.
  Create HintDb pM.
  Hint Extern 1 => unfold dom in *: dm.

  (* Definitions and notations : *)
  Definition initializedFields (σ: Store) (l: Loc) (f: list Field) : Prop :=
    match (getObj σ l) with
    | Some (C, ω) => ((length f) <= (length ω))
    | _ => False
    end.
  Notation "σ ⊨ l : f" := (initializedFields σ l f) (at level 80, l at level 80, f at level 80).

  Definition partialMonotonicity (σ σ': Store) :=
    forall l f, (σ ⊨ l : f) -> (σ' ⊨ l : f).
  Notation "σ ⪯ σ'" := (partialMonotonicity σ σ') (at level 80).


  (* Results : *)

  Lemma partialMonotonicity_reflexivity : forall (σ : Store), σ ⪯ σ.
  Proof. unfold partialMonotonicity => //. Qed.
  Hint Resolve partialMonotonicity_reflexivity: pM.

  Lemma initializedFields_dom : forall (σ: Store) (l: nat) (f: list Field), (σ ⊨ l : f) -> (l < (dom σ)).
  Proof.
    unfold initializedFields, getObj.
    induction σ; repeat light || destruct l as [|l'] || eauto.
      apply (PeanoNat.Nat.lt_0_succ).
      apply (Lt.lt_n_S).
      apply IHσ in H => //.
  Qed.
  Hint Resolve initializedFields_dom: pM.

  Lemma initializedFields_exists : forall (σ: Store) (c: ClN) (e: Env), exists (f: list Field), ((c,e)::σ) ⊨ (dom σ) : f.
  Proof.
    unfold initializedFields.
    intros. exists [].
    induction σ; intros ; simpl ; eauto using le_0_n.
    - destruct σ, a => //. apply le_0_n.
  Qed.

  Lemma partialMonotonicity_domains : forall (σ σ': Store), σ ⪯ σ' -> (dom σ) <= (dom σ').
  Proof.
    intros.
    unfold partialMonotonicity in H.
    move : (initializedFields_dom σ') => Hσ'.
    destruct (σ) eqn:Σ; eauto using le_0_n.
    - destruct o.
      case : (initializedFields_exists s c e) => f Hf.
      eauto using Lt.lt_le_S.
  Qed.
  Hint Resolve partialMonotonicity_domains: pM.


  Lemma partialMonotonicity_transitivity : forall (σ1 σ2 σ3 : Store), (σ1 ⪯ σ2) -> (σ2 ⪯ σ3) -> (σ1 ⪯ σ3).
  Proof.
    unfold partialMonotonicity; auto.
  Qed.
  Hint Resolve partialMonotonicity_transitivity: pM.


  Lemma partialMonotonicity_assignment : forall (σ σ': Store) (l: Loc) (C: ClN) (ω ω': Env),
      getObj σ l = Some (C, ω) ->
      length ω <= length ω' ->
      σ' = [l ↦ (C, ω')]σ ->
      σ ⪯ σ'.
  Proof.
    unfold partialMonotonicity, initializedFields.
    intros.
    move: (PeanoNat.Nat.eq_dec l l0) => [H4 | H4].
    - rewrite H1 H4 getObj_update1 => //.
      apply (initializedFields_dom _ _ f H2).
      unfold initializedFields in H2.
      rewrite -H4 H in H2 => //.
      apply: (PeanoNat.Nat.le_trans _ _ _ H2 H0).
    - move: (getObj_update2 σ (C, ω') l l0 ((getObj_dom σ (C,ω) l) H) H4)=>H5.
      rewrite H1 H5 => //.
  Qed.
  Hint Resolve partialMonotonicity_assignment: pM.


  Lemma partialMonotonicity_freshness : forall (σ: Store) (c: ClN) (ρ: Env),
      σ ⪯ σ ++ [(c, ρ)].
  Proof.
    unfold partialMonotonicity.
    unfold initializedFields.
    induction σ ; destruct l => //.
    apply IHσ => //.
  Qed.
  Hint Resolve partialMonotonicity_freshness: pM.

  Lemma partialMonotonicity_InitMaintained: forall n,  InitMaintained partialMonotonicity n.
  Proof.
    intros. apply freshnessInitMaintained; unfold Reflexive, Transitive, Assignment, Freshness; eauto with pM.
  Qed.
  Hint Resolve partialMonotonicity_InitMaintained: pM.

  Theorem partialMonotonicity_theorem: forall (n : nat), forall (e: Expr) (σ σ': Store) (ρ: Env) (v v': Value),
      ⟦e⟧(σ, ρ, v)(n) = (Success v' σ') -> σ ⪯ σ'.
  Proof.
    apply (eval_prop partialMonotonicity); unfold Reflexive, Transitive, Assignment, Freshness; eauto with pM.

  Qed.


  Theorem partialMonotonicity_theorem_dom: forall (n : nat), forall (e: Expr) (σ σ': Store) (ρ: Env) (v v': Value),
      ⟦e⟧(σ, ρ, v)(n) = (Success v' σ') -> (dom σ) <= (dom σ').
  Proof.
    intros. apply partialMonotonicity_theorem in H.
      by apply partialMonotonicity_domains.
  Qed.



  Lemma partialMonotonicity_warm_monotone: forall σ σ' l, σ ⪯ σ' -> σ ⊆ σ' -> (σ ⊨ l : warm) -> (σ' ⊨ l : warm).
  Proof.
    unfold reachable_warm.
    intros σ σ' l H_pm H_c [C [ω [args [fields[ methods [H2 [H3 H4]] ]]]]].
    unfold partialMonotonicity, initializedFields in H_pm.
    move /(_ l fields):H_pm => H_pm.
    rewrite H2 in H_pm.
    move /(_ H4):H_pm => H_pm.
    unfold compatible in H_c.
    move /(_ l C ω H2):H_c => [ω' H_c].
    rewrite H_c in H_pm.
    exists C, ω', args, fields, methods => //.
  Qed.




End PartialMonotonicity.
