From Celsius Require Export Trees Eval Reachability Tactics.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.

Module Compatibility.
  Import Eval.Evaluator.
  Create HintDb cmpt.
  
  (* Definitions and notations : *)
  Definition compatible (σ σ': Store) : Prop := forall l C ω,
      getObj σ l  = Some (C, ω) ->
      (exists ω', getObj σ' l = Some (C, ω')).
  Notation "σ ⊆ σ'" := (compatible σ σ') (at level 80).

  Lemma compatibility_reflexivity : forall σ, σ ⊆ σ.
  Proof.
    unfold compatible. eauto. Qed. 
  Hint Resolve compatibility_reflexivity : cmpt.
  
  Lemma compatibility_transitivity : forall s1 s2 s3, s1 ⊆ s2 -> s2 ⊆ s3 -> s1 ⊆ s3.
  Proof.
    unfold compatible. intros.
    move /(_ l C ω H1):H => [ω' H].
    move /(_ l C ω' H):H0 => [ω'' H0].
    eauto.
  Qed.  
  Hint Resolve compatibility_transitivity : cmpt. 

  Lemma compatibility_assignment : forall (σ σ': Store) (l: Loc) (C: ClN) (ω ω': Env),
      getObj σ l = Some (C, ω) ->
      σ' = [l ↦ (C, ω')]σ ->
      σ ⊆ σ'.
  Proof.
    intros.
    unfold compatible. intros.
    move: (PeanoNat.Nat.eq_dec l l0) => [H4 | H4].
    + rewrite H4 H1 in H.
      invert_constructor_equalities.
      rewrite H0 H4.
      rewrite getObj_update1.
      apply (getObj_dom _ _ _ H1).      
      exists ω' => //.
    + rewrite H0.
      rewrite getObj_update2.
      apply (getObj_dom _ _ _ H).
      eauto.
      exists ω0 => //.
  Qed.
  Hint Resolve compatibility_assignment.
    
  Lemma compatibility_freshness : forall (σ: Store) (c: ClN) (ρ: Env),
      σ ⊆ σ ++ [(c, ρ)].
  Proof.
    unfold compatible.
    induction σ; destruct l; simpl ; eauto => //. 
  Qed.
  
  
  
  Definition compatibility_prop (k: nat):= forall (e: Expr) (σ σ': Store) (ρ: Env) (v v': Value),
      (⟦e⟧(σ, ρ, v)(k) = Success v' σ') -> σ ⊆ σ'.
  
  Definition compatibility_prop_init (k : nat) :=  forall (I: Var) (v: list Var) (C: ClN) (σ σ_res: Store),
      (init I v C σ k) = Some σ_res -> σ ⊆ σ_res.
 
  Definition compatibility_prop_list (k: nat):= forall el (σ σ': Store) (ρ: Env) (v: Value) vl,
      (⟦_ el _⟧(σ, ρ, v)(k) = Success_list vl σ') -> σ ⊆ σ'.
  
  Definition compatibility_prop_list2 (k : nat) :=  forall (l: list Expr) (σ1 σ2 σ3: Store) (ρ: Env) (v : Value) (v_list1 v_list2 : list Value),
      fold_left (eval_list_aux σ1 ρ v k) l (Success_list v_list1 σ2) = (Success_list v_list2 σ3) -> σ2 ⊆ σ3.

  Lemma compatibility_rec_step_list2 : forall (n : nat),
      (* Strong induction *)
      (forall (k: nat), (k < n) -> compatibility_prop k) ->
      (forall (k: nat), (k < n) -> compatibility_prop_list2 k).
  Proof.
    unfold compatibility_prop. 
    unfold compatibility_prop_list2.
    intros n H k H_bound.
    induction l as [| e l].
    + (* case [] *)
      intros. simpl in H0. invert_constructor_equalities. eauto with cmpt. 
    + (* case e::l *)
      intros. simpl in H0. destruct k => //.
      ++ (* k = 0, timeout *)
        simpl in H0. rewrite foldLeft_constant in H0 => //.
      ++ (* k > 0 *)
        simpl in H0.
        destruct (⟦ e ⟧ (σ2, ρ, v )( k)) eqn: E.
        +++ rewrite foldLeft_constant in H0 => //.  
        +++ rewrite foldLeft_constant in H0 => //.  
        +++ simpl in IHl.
            apply (IHl σ1 s σ3 ρ v (v0::v_list1) v_list2) in H0.
            apply H in E.
            apply (compatibility_transitivity σ2 s σ3) => //.
            apply PeanoNat.Nat.lt_succ_l => //.
        +++ move : (eval_not_success_list k e σ2 s ρ v l0)=> E_not => //.
  Qed.

  Lemma compatibility_rec_step_list : forall (n : nat),
      (* Strong induction *)
      (forall (k: nat), (k < n) -> compatibility_prop k) ->
      (forall (k: nat), (k < n) -> compatibility_prop_list k).
  Proof.
    unfold compatibility_prop_list.
    intros.
    destruct k => //.
    simpl in H1.
    apply PeanoNat.Nat.lt_succ_l in H0.
    apply (compatibility_rec_step_list2 n H k H0 el σ σ σ' ρ v [] vl H1). 
  Qed.

 
  Lemma compatibility_rec_step_init : forall (n : nat),
      (* Strong induction *)
      (forall (k: nat), (k < n) -> compatibility_prop k) ->
      (forall (k: nat), (k < n) -> compatibility_prop_init k).
  Proof.
    intros n H_strong k H_bound.
    unfold compatibility_prop_init => I args_val C σ σ_res H.
    destruct k ; simpl in H => //.
    destruct k ; simpl in H ; destruct (ct C) => //. 
    - destruct c. destruct fields ; simpl in H.
      + invert_constructor_equalities. eauto with cmpt.
      + rewrite foldLeft_constant in H => //.
    - destruct c.
      generalize dependent σ.
      generalize dependent σ_res.
      induction fields.
      + repeat light || invert_constructor_equalities || auto with cmpt.
      + intros.  
        destruct a as [ f e] eqn:A.
        simpl in H.
        destruct ((⟦ e ⟧ (σ, args_val, I )( k))) eqn:E.
        ++ rewrite foldLeft_constant in H => //. (* Timeout *)
        ++ rewrite foldLeft_constant in H => //. (* Error *)
        ++ (* Success *)
          unfold assign_new in H.
          destruct (getObj s I) eqn:O => //.
          +++ destruct o.
              apply IHfields in H.
              move : (PeanoNat.Nat.lt_succ_l _ _ (PeanoNat.Nat.lt_succ_l (S k) n H_bound)) => H_bound2.
              move : (H_strong k H_bound2 e σ s args_val I v E) => H2.
              apply (compatibility_transitivity σ s σ_res) => //.
              apply (compatibility_transitivity s [I ↦ (c, e0 ++ [v])] (s) σ_res) => //.
              apply (compatibility_assignment _ _ I c e0 (e0 ++ [v]) O eq_refl).
          +++ rewrite foldLeft_constant in H => //.
        ++ rewrite foldLeft_constant in H => //. (* Success_list *)
  Qed.

 
  Lemma compatibility_theorem_rec_step : forall (n : nat),
      (* Strong induction *)
      (forall (k : nat), (k < n ) -> compatibility_prop k) ->
      (compatibility_prop n).

    (* To get one step of the evaluator, we destruct n *)
    destruct n.
    (* n = 0 - Timeout *)
    unfold compatibility_prop => //.
    (* n > 0 - case analysis over e *)
    unfold compatibility_prop.
    intros H_strong; intros.
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    destruct e;
      (* Trivial cases are handled automatically *)
      repeat light || invert_constructor_equalities || destruct_match || eauto with cmpt.
    - (* case e = e0.m(ē) *)
      move : (compatibility_rec_step_list (S n) H_strong n Hn l s s0 ρ v l0 matched3)=> H1.
      eauto using compatibility_transitivity.
    - (* case e = new C(l) *)
      move : (compatibility_rec_step_init (S n) H_strong n Hn (length s) l0 c _ σ' matched0) => H3.
      move : (compatibility_rec_step_list (S n) H_strong n Hn l σ s ρ v l0 matched) => H4.
      eauto using compatibility_transitivity, compatibility_freshness.
    - (* case e1.v0 = e2 ; e3 *)
      apply (compatibility_transitivity σ s σ'); eauto.
      + apply (compatibility_transitivity s (assign v1 v0 v2 s0) σ'); eauto.
        ++ unfold assign.
           move: (H_strong n Hn e2 s s0 ρ v v2 matched0) => H2.
           destruct (getObj s0 v1) eqn:G => //. destruct o.
           set s' := [v1 ↦ (c, [v0 ↦ v2] (e))] s0.
           move: (compatibility_assignment s0 s' v1 c  e ([v0 ↦ v2] (e)) G) => H1.
           apply (compatibility_transitivity s s0 s') => //.
           apply H1 => //.
  Qed. 

 
  
  Theorem compatibility_theorem: forall (n : nat), (compatibility_prop n).
  Proof.
    intros.
    move: (compatibility_theorem_rec_step) => H.
    apply H.
    induction n.
    - intros.
      apply PeanoNat.Nat.nlt_0_r in H0 => //.
    - intros.
      move/(_ n):H => H.
      move/(_ IHn):H => H.
      move:(Lt.le_lt_or_eq _ _  (Lt.lt_n_Sm_le _ _ H0) ) => [ H1 | H1 ].
      + apply IHn => //.
      + rewrite H1 => //.
  Qed.

  End Compatibility.
