From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
From Celsius Require Export Reachability.
From Celsius Require Export Compatibility.
Require Import ssreflect ssrbool.
Require Import Psatz.


Require Import List.
Import ListNotations.
Open Scope nat_scope.


Module Stackability.
  Import Eval.Evaluator.
  Import Reachability.Reachability.
  Import PartialMonotonicity.PartialMonotonicity.
  Import Compatibility.Compatibility.

  Definition stackability (σ σ' : Store) :=
    forall l, l < (dom σ') -> ((σ' ⊨ l : warm) \/ (l < (dom σ))).
  Notation "σ ≪ σ'" := (stackability σ σ') (at level 80).

  Lemma stackability_reflexivity: forall σ, σ ≪ σ.
  Proof.
    unfold stackability. right => //.
  Qed.

  Lemma stackability_transitivity: forall σ1 σ2 σ3,
      σ1 ≪ σ2 ->
      σ2 ≪ σ3 ->
      σ2 ⪯ σ3 ->
      σ2 ⊆ σ3 ->
      σ1 ≪ σ3.
  Proof.
    unfold stackability.
    intros.
    case /(_ l H3):H0 => H0.
    - left => //.
    - case /(_ l H0):H => H.
      + left. apply: (partialMonotonicity_warm_monotone σ2 σ3 l H1 H2 H) => //.
      + right => //.
  Qed.

  Lemma stackability_assignment : forall (σ σ': Store) (l : Loc) (C: ClN) (ω ω': Env),
      (getObj σ l) = Some (C, ω) ->
      length ω <= length ω' ->
      σ' = [l ↦ (C, ω')]σ ->
      σ ≪ σ'.
  Proof.
    unfold stackability, dom.
    intros.
    right.
    pose proof (update_one3 _ l (C,ω') σ).
    subst.
    rewrite -H3 => //.
  Qed.



    Lemma stackability_init_warm : forall (F: list Field) (n: nat) (args_val: list Var) (I: Loc) (s1 s2: Store) (C: ClN) (ρ: Env),
      I < dom s1 ->
      (getObj s1 I) = Some (C, ρ) ->
      (forall (k: nat), (k < n) -> EvalMaintained stackability k) ->
      fold_left (init_field args_val I n) F (Some s1) = Some s2 ->
      s1 ⊆ s2 /\ s1 ≪ s2 /\ s1 ⪯ s2 /\
      (exists ρ', (getObj s2 I) = Some (C, ρ') /\ ((length F + length ρ) <= length ρ')).
    Proof.
      unfold EvalMaintained.
    move => F n args_val I s1 s2 C ρ H H0 H_strong H1.
    move : H1 H H0. move: ρ s1 s2 C.
    induction F.
    + (* fields = [] *)
      simpl; intros.
      invert_constructor_equalities.
      rewrite -H3 H0.
      repeat eauto using stackability_reflexivity with pM cmpt || split || exists ρ.
    + (* fields = f::fields *)
      simpl.
      intros.
      destruct n; simpl in H1; try solve [rewrite foldLeft_constant in H1 => //].
      ++ destruct a as [ t e ] eqn:fieldEq.
         destruct ( ⟦ e ⟧ (s1, args_val, I)( n)) eqn:E; try solve [rewrite foldLeft_constant in H1 => //].
         rewrite {2}/assign_new in H1.
             destruct (getObj s I) eqn:G; try solve [rewrite foldLeft_constant in H1 => //].
             destruct o.
             pose proof (getObj_dom _ (c, e0) _ G) as H_doms2.
             assert (I < dom [I ↦ (c, e0 ++ [v])] (s)) as H_doms. {
               unfold dom.
               rewrite update_one3.
               apply H_doms2.
             }
             move: (getObj_update1 s (c,e0++[v]) I H_doms2) => H_sobj.
             move: (IHF (e0++[v]) ([I ↦ (c, e0 ++ [v])] (s)) s2 c H1 H_doms H_sobj).
             rewrite app_length PeanoNat.Nat.add_1_r -plus_n_Sm.
             move => [H1_cmp1 [H_stk1 [H_pm1 [ ρ' [H_obj H_flen]]]]].
             assert ( length e0 <= length (e0 ++ [v])) as H_len_e0.
             rewrite app_length PeanoNat.Nat.add_1_r.
             apply PeanoNat.Nat.le_succ_diag_r.
             assert (length ρ <= length e0) as H_len_ρ.
             {
               move: (partialMonotonicity_theorem n e _ _ _ _ _ E I).
               unfold partialMonotonicity, initializedFields.
               rewrite H0 G.
               move => H_len_ρ. move /(_ (repeat a (length ρ))):H_len_ρ => H_len_ρ.
               rewrite repeat_length in H_len_ρ => //.
               apply H_len_ρ => //.
             }
             move : (stackability_assignment s ([I ↦ (c, e0 ++ [v])] (s)) I c e0 (e0++[v]) G H_len_e0 eq_refl) => H_stk2.
             move: (partialMonotonicity_assignment _ _ I c e0 (e0++[v]) G H_len_e0 eq_refl) => H_pm2.
             move: (compatibility_assignment _ _ I c e0 (e0++[v]) G eq_refl) => H_cmp2.
             move: (partialMonotonicity_theorem n e _ _ _ _ _ E) => H_pm3.
             move: (compatibility_theorem n e _ _ _ _ _ E) => H_cmp3.
             move: (H_strong n (PeanoNat.Nat.lt_succ_diag_r n) e _ _ _ _ _ E) => H_stk3.
             repeat split; eauto using stackability_transitivity with pM cmpt.
             exists ρ' ; split; try (eauto || lia).
             +++ unfold compatible in H_cmp3.
                  move /(_ I C ρ H0):H_cmp3 => [ω' H_cmp3].
                  rewrite G in H_cmp3. invert_constructor_equalities.
                  rewrite H_obj H3 => //.
  Qed.

    (* fold_left (init_field l0 (length s) n) fields (Some (s ++ [(c, [])])) = Some σ' *)

    Lemma stackability_init_fresh : forall (n: nat) (l0: list Var) (s σ': Store) (c: ClN),
      (forall (k: nat), (k < n) -> EvalMaintained stackability k) ->
      init (length s) l0 c (s ++ [(c, [])]) n = Some σ' -> s ≪ σ'.
    Proof.
      intros.
      destruct n => //.
      simpl in H0.
      destruct (ct c) eqn:C => //.
      destruct c0 eqn:C0 => //.
      pose proof stackability_init_warm.
      assert (length s < dom (s ++ [(c, [])])) as H_len. {
        unfold dom; rewrite app_length. simpl. lia. }
      assert ((forall k : nat, k < n -> EvalMaintained stackability k)) as H_strong2. {
        intros. apply H. lia. }
      move: (stackability_init_warm fields n l0 (length s) (s++[(c,[])]) σ' c [] H_len (getObj_last _ _ _) H_strong2 H0) => [H_cmp1 [H_stk1 [H_pm1 [ρ' [H_obj2 H_flen]]]]].
    simpl in H_flen. rewrite PeanoNat.Nat.add_0_r in H_flen.
      move :H_stk1. unfold stackability, dom => H_stk1 l H_l.
      move /(_ l H_l):H_stk1 => H_stk1.
      case: H_stk1; auto.
      rewrite app_length. simpl. rewrite PeanoNat.Nat.add_1_r => H_l'.
      move:(Lt.le_lt_or_eq _ _  (Lt.lt_n_Sm_le _ _ H_l') ) => [ H_l'' | H_l'' ].
      right => //.
      left. rewrite H_l''. unfold reachable_warm.
      exists c, ρ', args, fields, methods. repeat split => //.
    Qed.






  Theorem stackability_theorem : forall (n : nat), forall (e: Expr) (σ σ': Store) (ρ: Env) (v v': Value),
      ⟦e⟧(σ, ρ, v)(n) = (Success v' σ') -> σ ≪ σ'.
  Proof.
    apply (eval_prop (fun σ σ' => σ ⪯ σ' /\ σ ⊆ σ' /\ σ ≪ σ')).
    + unfold Reflexive. eauto using stackability_reflexivity with pM cmpt.
    + unfold Transitive. intros. repeat destruct_and. split ; eauto using stackability_transitivity with pM cmpt.
    + unfold Assignment. intros. split; eauto using stackability_assignment with pM cmpt.
    + intros n H_strong. intros.
      assert ((forall k : nat, k < n -> EvalMaintained partialMonotonicity k) /\ (forall k : nat, k < n -> EvalMaintained compatible k) /\ (forall k : nat, k < n -> EvalMaintained stackability k)) as [Hpart [Hcmpt Hstck]]. {
        repeat split; unfold EvalMaintained in *; intros.
        all: move:(H_strong k0 H1 e σ σ'0 ρ v v' H2) => [H3 [H4 H5]] => //.
      }
      pose proof (partialMonotonicity_InitMaintained n Hpart k H _ _ _ _ H0).
      pose proof (compatibility_InitMaintained n Hcmpt k H _ _ _ _ H0).
      pose proof (stackability_init_fresh k l0 s σ' c).
      repeat split ; eauto using stackability_init_fresh with pM cmpt.
      apply H3 => //.
      intros. apply Hstck. lia.
  Qed.

End Stackability.
