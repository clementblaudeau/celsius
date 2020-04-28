From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
From Celsius Require Export Reachability.
Require Import ssreflect ssrbool.


Require Import List.
Import ListNotations.
Open Scope nat_scope.


Module Reachability.
  Import Eval.Evaluator.
  Import Reachability.Reachability.
  Import PartialMonotonicity.PartialMonotonicity.
  
  Definition stackability (σ σ' : Store) :=
    forall l, l < (dom σ') -> ((σ' ⊨ l : warm) \/ (l < (dom σ))).
  Notation "σ ≪ σ'" := (stackability σ σ') (at level 80).
  
  Lemma stackability_reflexivity: forall σ, σ ≪ σ.
  Proof.
    unfold stackability. right => //.
  Qed.

  Lemma stackability_transitivity: forall σ1 σ2 σ3,
      σ1 ≪ σ2 -> σ2 ≪ σ3 -> σ2 ⪯ σ3 -> σ1 ≪ σ3.
  Proof.
    unfold stackability.
    intros.
    case /(_ l H2):H0 => H0.
    - left => //.
    - case /(_ l H0):H => H.
      + left. apply: (partialMonotonicity_warm_monotone σ2 σ3 l H1 H) => //.
      + right => //.
  Qed.      

  Lemma stackability_assignment : forall (σ σ': Store) (l l': Loc) (C: ClN) (f: Value) (ω ω': Env),
      (getObj σ l) = Some (C, ω) ->
      ω' = [f ↦ l']ω ->
      σ' = [l ↦ (C, ω')]σ ->
      σ ≪ σ'.
  Proof.
    unfold stackability, dom.
    intros.
    right.
    move: (update_one3 _ l (C,ω') σ).
    rewrite -H1 => H3.
    rewrite -H3 => //.
  Qed.


Definition stackability_prop (k : nat) :=  forall (e: Expr) (σ σ': Store) (ρ: Env) (v v': Value),
      ⟦e⟧(σ, ρ, v)(k) = (Success v' σ') -> σ ≪ σ'.

Definition stackability_prop_list (k : nat) :=  forall (l: list Expr) (σ1 σ2: Store) (ρ: Env) (v : Value) (v_list: list Value),
      ⟦_ l _⟧(σ1, ρ, v)(k) = (Success_list v_list σ2) -> σ1 ≪ σ2 /\ σ1 ⪯ σ2.

Definition stackability_prop_list2 (k : nat) :=  forall (l: list Expr) (σ1 σ2 σ3: Store) (ρ: Env) (v : Value) (v_list1 v_list2 : list Value),
      fold_left (eval_list_aux σ1 ρ v k) l (Success_list v_list1 σ2) = (Success_list v_list2 σ3) -> σ2 ≪ σ3 /\ σ2 ⪯ σ3.


Lemma stackability_rec_step_list2 : forall (n : nat),
    (* Strong induction *)
    (forall (k: nat), (k < n) -> stackability_prop k) ->
    (forall (k: nat), (k < n) -> stackability_prop_list2 k).
  Proof.
  unfold stackability_prop. 
  unfold stackability_prop_list2.
  intros n H k H_bound.
  induction l as [| e l].
  + (* case [] *)
    intros. simpl in H0. injection H0 => H2 H3. rewrite H2.
    apply (conj (stackability_reflexivity _) (partialMonotonicity_reflexivity _)).
  + (* case e::l *)
    intros. simpl in H0. destruct k => //.
    ++ (* k = 0, timeout *)
      simpl in H0. assert (forall l', (fold_left (fun (_ : Result) (_ : Expr) => Timeout) l' Timeout = Timeout)) as H_timeout. { induction l' => //. } rewrite H_timeout in H0 => //.
    ++ (* k > 0 *)
       simpl in H0.
       destruct (⟦ e ⟧ (σ2, ρ, v )( k)) eqn: E.
    +++ assert (H_abs: forall l', fold_left
         (fun (acc : Result) (e : Expr) =>
          match acc with
          | Success_list vs σ1 =>
              match (⟦ e ⟧ (σ1, ρ, v )( k)) with
              | Timeout => Timeout
              | Error => Error
              | Success v σ2 => Success_list (v :: vs) σ2
              | Success_list l s => Success_list l s
              end
          | _ => acc
          end) l' Timeout = Timeout).  { induction  l' => //. }
        rewrite H_abs in H0 => //.
    +++ assert (H_abs: forall l', fold_left
         (fun (acc : Result) (e : Expr) =>
          match acc with
          | Success_list vs σ1 =>
              match (⟦ e ⟧ (σ1, ρ, v )( k)) with
              | Timeout => Timeout
              | Error => Error
              | Success v σ2 => Success_list (v :: vs) σ2
              | Success_list l s => Success_list l s
              end
          | _ => acc
          end) l' Error = Error).  { induction  l' => //. }
        rewrite H_abs in H0 => //.
    +++ simpl in IHl.
        apply (IHl σ1 s σ3 ρ v (v0::v_list1) v_list2) in H0.
        move: (partialMonotonicity_theorem k e σ2 s ρ v v0 E) => H1.
        apply (H _ (PeanoNat.Nat.lt_succ_l _ _ H_bound))in E.
        move: H0 => [H01 H02].
        move: (stackability_transitivity σ2 s σ3 E H01 H02 ) => H2.
        split => //.
        apply (partialMonotonicity_transitivity _ s _ H1 H02).
    +++ move : (eval_not_success_list k e σ2 s ρ v l0)=> E_not => //.
Qed.

Lemma stackability_rec_step_list : forall (n : nat),
    (* Strong induction *)
    (forall (k: nat), (k < n) -> stackability_prop k) ->
    (forall (k: nat), (k < n) -> stackability_prop_list k).
Proof.
  unfold stackability_prop_list.
  intros.
  destruct k => //.
  simpl in H1.
  apply PeanoNat.Nat.lt_succ_l in H0.
  move : (stackability_rec_step_list2 n H k H0 l σ1 σ1 σ2 ρ v [] v_list) => H2.
  apply H2 => //.
Qed.


Definition stackability_prop_init (k : nat) :=  forall (I: Var) (v: list Var) (C: ClN) (σ σ_res: Store),
      (init I v C σ k) = Some σ_res -> σ ≪ σ_res /\ σ ⪯ σ_res.


Lemma stackability_rec_step_init : forall (n : nat),
    (* Strong induction *)
    (forall (k: nat), (k < n) -> stackability_prop k) ->
    (forall (k: nat), (k < n) -> stackability_prop_init k).
Proof.
  intros n H_strong k H_bound.
  unfold stackability_prop_init => I v C σ σ_res H.
  destruct k => //.
  simpl in H.
  destruct (ct C) => //.
  destruct c.
  injection H => H1.
  destruct H.
  generalize dependent σ.
  generalize dependent σ_res.
  induction fields.
  - intros. simpl in H1. rewrite H1. apply (conj (stackability_reflexivity _) (partialMonotonicity_reflexivity _)).
  - intros. simpl in H1. destruct a as [ f t e] eqn:A.
    destruct ((⟦ e ⟧ (σ, [], I )( k))) eqn:E.
    + apply IHfields => //. (* Timeout *)
    + apply IHfields => //. (* Error *)
    +  (* Success *)
      unfold assign in IHfields, H1.
      move /(_ _ _ H1):IHfields => [H1s H1p] ; clear H1.
      move : (H_strong k (PeanoNat.Nat.lt_succ_l k n H_bound) e σ s [] I v0 E) => H2.
      move: (partialMonotonicity_theorem k e σ s [] I v0 E) => H3.
      destruct (getObj s I) eqn:G.
      destruct  o.
      move: (stackability_assignment s ([I ↦ (c, [f ↦ v0] (e0))] (s)) I v0 c f e0 ([f ↦ v0] (e0)) G (eq_refl _) (eq_refl _)) => H4.
      move: (partialMonotonicity_assignment s ([I ↦ (c, [f ↦ v0] (e0))] (s)) I v0 c f e0 ([f ↦ v0] (e0)) G (eq_refl _) (eq_refl _)) => H5.
      move: (partialMonotonicity_transitivity σ s ([I ↦ (c, [f ↦ v0] (e0))] (s)) H3 H5) => H6.
      move: (partialMonotonicity_transitivity s ([I ↦ (c, [f ↦ v0] (e0))] (s)) σ_res H5 H1p) => H7.
      split.
      apply (stackability_transitivity σ [I ↦ (c, [f ↦ v0] (e0))] (s) σ_res) => //.
      apply (stackability_transitivity σ s [I ↦ (c, [f ↦ v0] (e0))] (s) ) => //.
      apply (partialMonotonicity_transitivity σ s σ_res) => //.
      apply (conj (stackability_transitivity σ s σ_res H2 H1s H1p) (partialMonotonicity_transitivity _ s _ H3 H1p)) => //.
    + apply IHfields => //. (* Success_list *)
Qed.


Lemma stackability_freshness : forall (σ: Store) (c: ClN) (ρ: Env),
  σ ≪ σ++[(c,ρ)].
Proof.
  unfold stackability, dom.
  intros.
  rewrite app_length in H; simpl in H.
    simpl; intros
    right.
    move: (update_one3 _ (length σ + 1) (c,ρ) σ).
    destruct σ.
    simpl.
    rewrite -H => H3.
    apply : (stackability_assignment2 σ [length σ + 1 ↦ (c, ρ)] (σ) (length σ +1) c ρ (eq_refl _)). 
Qed.
  
Lemma stackability_theorem_rec_step : forall (n : nat),
  (* Strong induction *)
  (forall (k : nat), (k < n ) -> stackability_prop k) ->
  (stackability_prop n).

  (* To get one step of the evaluator, we destruct n *)
  destruct n.

  (* n = 0 - Timeout *)
  unfold stackability_prop => //.

  (* n > 0 - case analysis over e *)
  unfold stackability_prop.
  intros H_strong; intros.
  destruct e.
  
  - (* case e = x *)
    unfold eval in H.
    destruct (getVal ρ v0) => //.
    injection H => H1 H2.
    rewrite H1.
    apply stackability_reflexivity => //.
  - (* case e = this *)
    unfold eval in H.
    injection H => H1 H2.
    rewrite H1.
    apply stackability_reflexivity => //.
  - (* case e = e0.field *)
    simpl in H.
    destruct  (⟦ e ⟧ (σ, ρ, v )( n)) eqn:E => //.
    destruct (getObj s v1) => //.
    destruct o.
    destruct (getVal e0 v0) => //.
    injection H => H1 H2.
    rewrite<- H1.
    apply (H_strong n (PeanoNat.Nat.lt_succ_diag_r n) e σ s ρ v v1) => //.
  - (* case e = e0.m(ē) *)
    simpl in H.
    destruct  (⟦ e ⟧ (σ, ρ, v )( n)) eqn:E => //.
    destruct (getObj s v0) => //.
    destruct o.
    destruct (ct c) => //.
    destruct c0.
    destruct (methods m) => //.
    destruct m0.
    destruct (⟦_ l _⟧ (s, ρ, v )( n)) eqn: L => //.
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    move : (stackability_rec_step_list (S n) H_strong n Hn l s s0 ρ v l0 L)=> H1.
    move : (H_strong n Hn e σ s ρ v v0 E) => H2.
    move : (H_strong n Hn body s0 σ' ([removeTypes args0 ⟼ l0] ([])) v v' H) => H3.
    apply : (stackability_transitivity σ s0 σ' (stackability_transitivity σ s s0 H2 (proj1 H1) (proj2 H1)) H3).
    apply : (partialMonotonicity_theorem n body s0 σ' [removeTypes args0 ⟼ l0] ([]) v v' H). 
  - (* case e = new C(l) *)
    simpl in H.
    destruct (⟦_ l _⟧ (σ, ρ, v )( n)) eqn:L => //.
    destruct (init (length s + 1) l0 c [length s + 1 ↦ (c, [])] (s) n) eqn:I => //.
    injection H => H1 H2.
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    move : (stackability_rec_step_init (S n) H_strong n Hn (length s +1) l0 c ([length s + 1 ↦ (c, [])] (s)) s0 I) => [H3 H4].
    move : (stackability_rec_step_list (S n) H_strong n Hn l σ s ρ v l0 L) => [H5 H6].
    rewrite -H1.
    apply:  (stackability_transitivity σ s s0 H5).
    apply (stackability_transitivity s ( [length s + 1 ↦ (c, [])] (s)) s0) => //.
    unfold stackability => l1 H7.
    simpl; simpl in H7.
    apply (stackability_freshness).
  - (* case e1.v0 = e2 ; e3 *)
    simpl in H.
    destruct (⟦ e1 ⟧ (σ, ρ, v )( n)) eqn:E1 => //.
    destruct (⟦ e2 ⟧ (s, ρ, v )( n)) eqn:E2 => //.
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    apply (partialMonotonicity_transitivity σ s σ') => //.
    + apply (H_strong n Hn e1 σ s ρ v v1 E1).
    + apply (partialMonotonicity_transitivity s (assign v1 v0 v2 s0) σ').
      ++ unfold assign.
         move: (H_strong n Hn e2 s s0 ρ v v2 E2) => H2.
         destruct (getObj s0 v1) eqn:G => //. destruct o.
         set s' := [v1 ↦ (c, [v0 ↦ v2] (e))] s0.
         move: (partialMonotonicity_assignment s0 s' v1 v2 c v0 e ([v0 ↦ v2] (e)) G) => H1.
         apply (partialMonotonicity_transitivity s s0 s') => //.
         apply H1 => //.
      ++ 
    unfold assign.
    unfold assign  in H.
    destruct (getObj s0 v1) eqn:G => //.
    destruct o.
    move: H.
    set s' := [v1 ↦ (c, [v0 ↦ v2] (e))] s0 => H.
    move: (H_strong n Hn e3 s' σ' ρ v v' H) => //.
    move: (H_strong n Hn e3 s0 σ' ρ v v' H) => //.
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
 

    


    

  
    
    
      
    

