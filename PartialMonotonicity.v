From Celsius Require Export Trees Eval Reachability Tactics Compatibility.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.

Module PartialMonotonicity.
  Import Reachability.Reachability.
  Import Eval.Evaluator.
  Import Compatibility.Compatibility.
  Create HintDb pM.
  
  (* Definitions and notations : *)
  Definition initializedFields (σ: Store) (l: Loc) (f: list Field) : Prop :=
    match (getObj σ l) with
    | Some (C, ω) => ((length f) <= (length ω))
    | _ => False
    end.
  Notation "σ ⊨ l : f" := (initializedFields σ l f) (at level 80, l at level 99, f at level 99).

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
    induction σ; intros ; simpl => //.
    - apply le_0_n.
    - destruct σ => //.
      simpl.
      destruct a. apply le_0_n.
  Qed.
  
  Lemma partialMonotonicity_domains : forall (σ σ': Store), σ ⪯ σ' -> (dom σ) <= (dom σ').
  Proof.
    intros.    
    unfold partialMonotonicity in H.
    move : (initializedFields_dom σ') => Hσ'.
    destruct (σ) eqn:Σ.
    - apply le_0_n.
    - destruct o.
      case : (initializedFields_exists s c e) => f Hf.
      apply (Lt.lt_le_S _ _ (Hσ' _ _ (H _ _ Hf)) )=> //.
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
      rewrite H1 H5.
      apply H2.
  Qed.
  Hint Resolve partialMonotonicity_assignment: pM.

  

  Definition partialMonotonicity_prop (k : nat) :=  forall (e: Expr) (σ σ': Store) (ρ: Env) (v v': Value),
      ⟦e⟧(σ, ρ, v)(k) = (Success v' σ') -> σ ⪯ σ'.

  Definition partialMonotonicity_prop_list (k : nat) :=  forall (l: list Expr) (σ1 σ2: Store) (ρ: Env) (v : Value) (v_list: list Value),
      ⟦_ l _⟧(σ1, ρ, v)(k) = (Success_list v_list σ2) -> σ1 ⪯ σ2.

  Definition partialMonotonicity_prop_list2 (k : nat) :=  forall (l: list Expr) (σ1 σ2 σ3: Store) (ρ: Env) (v : Value) (v_list1 v_list2 : list Value),
      fold_left (eval_list_aux σ1 ρ v k) l (Success_list v_list1 σ2) = (Success_list v_list2 σ3) -> σ2 ⪯ σ3.


  Lemma partialMonotonicity_rec_step_list2 : forall (n : nat),
      (* Strong induction *)
      (forall (k: nat), (k < n) -> partialMonotonicity_prop k) ->
      (forall (k: nat), (k < n) -> partialMonotonicity_prop_list2 k).
  Proof.
    unfold partialMonotonicity_prop. 
    unfold partialMonotonicity_prop_list2.
    intros n H k H_bound.
    induction l as [| e l].
    + (* case [] *)
      intros. simpl in H0. injection H0 => H2 H3. rewrite H2; apply partialMonotonicity_reflexivity.
    + (* case e::l *)
      intros. simpl in H0. destruct k => //.
      ++ (* k = 0, timeout *)
        simpl in H0. assert (forall l', (fold_left (fun (_ : Result) (_ : Expr) => Timeout) l' Timeout = Timeout)) as H_timeout. { induction l' => //. } rewrite H_timeout in H0 => //.
      ++ (* k > 0 *)
        simpl in H0.
        destruct (⟦ e ⟧ (σ2, ρ, v )( k)) eqn: E.
        +++ rewrite foldLeft_constant in H0 => //.  
        +++ rewrite foldLeft_constant in H0 => //.  
        +++ rewrite -/eval_list in H0.
            simpl in IHl.
            apply (IHl σ1 s σ3 ρ v (v0::v_list1) v_list2) in H0.
            apply H in E.
            apply (partialMonotonicity_transitivity σ2 s σ3) => //.
            apply PeanoNat.Nat.lt_succ_l => //.
        +++ move : (eval_not_success_list k e σ2 s ρ v l0)=> E_not => //.
  Qed.

  Lemma partialMonotonicity_rec_step_list : forall (n : nat),
      (* Strong induction *)
      (forall (k: nat), (k < n) -> partialMonotonicity_prop k) ->
      (forall (k: nat), (k < n) -> partialMonotonicity_prop_list k).
  Proof.
    unfold partialMonotonicity_prop_list.
    intros.
    destruct k => //.
    simpl in H1.
    apply PeanoNat.Nat.lt_succ_l in H0.
    move : (partialMonotonicity_rec_step_list2 n H k H0 l σ1 σ1 σ2 ρ v [] v_list) => H2.
    apply H2 => //.
  Qed.


  Definition partialMonotonicity_prop_init (k : nat) :=  forall (I: Var) (v: list Var) (C: ClN) (σ σ_res: Store),
      (init I v C σ k) = Some σ_res -> σ ⪯ σ_res.

  
  
  
  Lemma partialMonotonicity_rec_step_init : forall (n : nat),
      (* Strong induction *)
      (forall (k: nat), (k < n) -> partialMonotonicity_prop k) ->
      (forall (k: nat), (k < n) -> partialMonotonicity_prop_init k).
  Proof.
    intros n H_strong k H_bound.
    unfold partialMonotonicity_prop_init => I args_val C σ σ_res H.
    destruct k ; simpl in H => //.
    destruct k ; simpl in H ; destruct (ct C) => //. 
    - destruct c. destruct fields ; simpl in H.
      + invert_constructor_equalities. eauto with pM.
      + rewrite foldLeft_constant in H => //.
    - destruct c.
      generalize dependent σ.
      generalize dependent σ_res.
      induction fields.
      + repeat light || auto with pM.
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
              apply (partialMonotonicity_transitivity σ s σ_res) => //.
              apply (partialMonotonicity_transitivity s [I ↦ (c, e0 ++ [v])] (s) σ_res) => //.
              apply (partialMonotonicity_assignment _ _ I c e0 (e0 ++ [v]) O).
              rewrite app_length. simpl. rewrite PeanoNat.Nat.add_1_r. apply PeanoNat.Nat.le_succ_diag_r.
              reflexivity.
          +++ rewrite foldLeft_constant in H => //.
        ++ rewrite foldLeft_constant in H => //. (* Success_list *)
  Qed.
  
  Lemma partialMonotonicity_freshness : forall (σ: Store) (c: ClN) (ρ: Env),
      σ ⪯ σ ++ [(c, ρ)].
  Proof.
    unfold partialMonotonicity.
    unfold initializedFields.
    induction σ ; destruct l => //.
    apply IHσ => //.
  Qed.    
  
  Lemma partialMonotonicity_theorem_rec_step : forall (n : nat),
      (* Strong induction *)
      (forall (k : nat), (k < n ) -> partialMonotonicity_prop k) ->
      (partialMonotonicity_prop n).

    (* To get one step of the evaluator, we destruct n *)
    destruct n.
    (* n = 0 - Timeout *)
    unfold partialMonotonicity_prop => //.
    (* n > 0 - case analysis over e *)
    unfold partialMonotonicity_prop.
    intros H_strong; intros.
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    destruct e;
      (* Trivial cases are handled automatically *)
      repeat light || invert_constructor_equalities || destruct_match || eauto with pM.
    - (* case e = e0.m(ē) *)
      move : (partialMonotonicity_rec_step_list (S n) H_strong n Hn l s s0 ρ v l0 matched3)=> H1.
      eauto using partialMonotonicity_transitivity.
    - (* case e = new C(l) *)
      move : (partialMonotonicity_rec_step_init (S n) H_strong n Hn (length s) l0 c _ σ' matched0) => H3.
      move : (partialMonotonicity_rec_step_list (S n) H_strong n Hn l σ s ρ v l0 matched) => H4.
      eauto using partialMonotonicity_transitivity, partialMonotonicity_freshness.
    - (* case e1.v0 = e2 ; e3 *)
      apply (partialMonotonicity_transitivity σ s σ'); eauto.
      + apply (partialMonotonicity_transitivity s (assign v1 v0 v2 s0) σ'); eauto.
        ++ unfold assign.
           move: (H_strong n Hn e2 s s0 ρ v v2 matched0) => H2.
           destruct (getObj s0 v1) eqn:G => //. destruct o.
           set s' := [v1 ↦ (c, [v0 ↦ v2] (e))] s0.
           move: (partialMonotonicity_assignment s0 s' v1 c  e ([v0 ↦ v2] (e)) G) => H1.
           apply (partialMonotonicity_transitivity s s0 s') => //.
           apply H1 => //.
           apply PeanoNat.Nat.eq_le_incl.
           rewrite update_one3 => //.
  Qed.


  
  Theorem partialMonotonicity_theorem: forall (n : nat), (partialMonotonicity_prop n).
  Proof.
    intros.
    move: (partialMonotonicity_theorem_rec_step) => H.
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
