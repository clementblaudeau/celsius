From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export Reachability.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.

Module PartialMonotonicity.
  Import Reachability.Reachability.
  Import Eval.Evaluator.
  
  (* Definitions and notations : *)
  Definition initializedFields (σ: Store) (l: Loc) (f: list Field) : Prop :=
    match (getObj σ l) with
    | Some (C, ω) => ((length ω) <= (length f))
    | _ => False
    end.
  Notation "σ ⊨ l : f" := (initializedFields σ l f) (at level 80, l at level 99, f at level 99).

  Definition partialMonotonicity (σ σ': Store) :=
    forall l f, (σ ⊨ l : f) -> (σ' ⊨ l : f).
  Notation "σ ⪯ σ'" := (partialMonotonicity σ σ') (at level 80).


  (* Results : *)
  Lemma partialMonotonicity_reflexivity : forall (σ : Store), σ ⪯ σ.
  Proof. unfold partialMonotonicity => //. Qed.

  Lemma initializedFields_dom : forall (σ: Store) (l: nat) (f: list Field), (σ ⊨ l : f) -> (l < (dom σ)).
  Proof.
    induction σ.
    - intros.
      rewrite /initializedFields /getObj in H.
      destruct l => //.
    - destruct a.
      intros.
      unfold initializedFields in H.
      destruct l => //.
      apply (PeanoNat.Nat.lt_0_succ).
      simpl.
      apply (Lt.lt_n_S).
      simpl in H.
      unfold initializedFields in IHσ.
      apply IHσ in H => //.
  Qed.

  Lemma initializedFields_exists : forall (σ: Store) (c: ClN) (e: Env), exists (f: list Field), ((c,e)::σ) ⊨ (dom σ) : f.
  Proof.
    unfold initializedFields.
    induction σ.
    - intros => //.
      exists (repeat (field 0 (0,hot) this) (length e)).
      rewrite repeat_length => //.
    - intros => //.
      destruct a.
      apply IHσ.
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


  Lemma partialMonotonicity_transitivity : forall (σ1 σ2 σ3 : Store), (σ1 ⪯ σ2) -> (σ2 ⪯ σ3) -> (σ1 ⪯ σ3).
  Proof.
    unfold partialMonotonicity; auto.
  Qed.    

  Lemma getObj_update1 : forall (σ: Store) (o: Obj) (x: nat),
      x < dom σ -> (getObj [x ↦ o]σ x) = Some o.
  Proof.
    rewrite /dom /getObj => σ o x.
    apply : (update_one1 Obj x o σ) => //.
  Qed.  
  
  Lemma getObj_update2 : forall (σ: Store) (o: Obj) (x x': nat),
      x < dom σ ->
      x <> x' ->
      (getObj [x ↦ o]σ x') = (getObj σ x').
  Proof.
    rewrite /dom /getObj => σ o x x'.
    move : (update_one2 Obj x x' o σ) => //.
  Qed.

  Lemma getObj_dom : forall (σ: Store) (o: Obj) (l: nat),
      (getObj σ l) = Some o ->
      l < (dom σ).
  Proof.
    intros σ o.
    induction σ ; destruct l => //.    
    + move: (PeanoNat.Nat.lt_0_succ (dom σ)) => //.
    + simpl => H. apply (Lt.lt_n_S _ _ (IHσ _ H)) . 
  Qed.


  Lemma partialMonotonicity_assignment : forall (σ σ': Store) (l l': Loc) (C: ClN) (f: Value) (ω ω': Env),
      (getObj σ l) = Some (C, ω) ->
      ω' = [f ↦ l']ω ->
      σ' = [l ↦ (C, ω')]σ ->
      σ ⪯ σ'.
  Proof.
    unfold partialMonotonicity.
    intros.
    unfold initializedFields.
    move: (PeanoNat.Nat.eq_dec l l0) => [H4 | H4].
    - rewrite H1 H4 getObj_update1 => //.
      apply (initializedFields_dom _ _ f0 H2).
      unfold initializedFields in H2.
      rewrite -H4 H in H2 => //.
      move: (update_one3 Loc f l' ω) => H5.
      rewrite H0 H5 => //. 
    - move: (getObj_update2 σ (C, ω') l l0 ((getObj_dom σ (C,ω) l) H) H4)=>H5.
      rewrite H1 H5.
      apply H2.
  Qed.

  

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
    unfold partialMonotonicity_prop_init => I v C σ σ_res H.
    destruct k => //.
    simpl in H.
    destruct (ct C) => //.
    destruct c.
    injection H => H1.
    destruct H.
    generalize dependent σ.
    generalize dependent σ_res.
    induction fields.
    - intros. simpl in H1. rewrite H1. apply partialMonotonicity_reflexivity.
    - intros. simpl in H1. destruct a as [ f t e] eqn:A.
      destruct ((⟦ e ⟧ (σ, [], I )( k))) eqn:E.
      + apply IHfields => //. (* Timeout *)
      + apply IHfields => //. (* Error *)
      +  (* Success *)
        apply IHfields in H1.
        move : (H_strong k (PeanoNat.Nat.lt_succ_l k n H_bound) e σ s [] I v0 E) => H2.
        unfold assign in H1.
        destruct (getObj s I) eqn:G.
        destruct  o.
        move: (partialMonotonicity_assignment s ([I ↦ (c, [f ↦ v0] (e0))] (s)) I v0 c f e0 ([f ↦ v0] (e0)) G) => H3.
        apply (partialMonotonicity_transitivity σ s σ_res) => //.
        apply (partialMonotonicity_transitivity s [I ↦ (c, [f ↦ v0] (e0))] (s) σ_res) => //.
        apply H3 => //.
        apply (partialMonotonicity_transitivity σ s σ_res) => //.
        
      + apply IHfields => //. (* Success_list *)
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
    destruct e.
    
    - (* case e = x *)
      unfold eval in H.
      destruct (getVal ρ v0) => //.
      injection H => H1 H2.
      rewrite H1.
      apply partialMonotonicity_reflexivity => //.
    - (* case e = this *)
      unfold eval in H.
      injection H => H1 H2.
      rewrite H1.
      apply partialMonotonicity_reflexivity => //.
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
      move : (partialMonotonicity_rec_step_list (S n) H_strong n Hn l s s0 ρ v l0 L)=> H1.
      move : (H_strong n Hn e σ s ρ v v0 E) => H2.
      move : (H_strong n Hn body s0 σ' ([removeTypes args0 ⟼ l0] ([])) v v' H) => H3.
      move : (partialMonotonicity_transitivity σ s0 σ' (partialMonotonicity_transitivity σ s s0 H2 H1) H3) => //.
    - (* case e = new C(l) *)
      simpl in H.
      destruct (⟦_ l _⟧ (σ, ρ, v )( n)) eqn:L => //.
      destruct (init (length s) l0 c (s ++ [(c, [])]) n) eqn:I => //.
      injection H => H1 H2.
      move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
      move : (partialMonotonicity_rec_step_init (S n) H_strong n Hn (length s) l0 c _ s0 I) => H3.
      move : (partialMonotonicity_rec_step_list (S n) H_strong n Hn l σ s ρ v l0 L) => H4.
      rewrite -H1.
      apply (partialMonotonicity_transitivity σ s s0) => //.
      apply (partialMonotonicity_transitivity s (s++[(c,[])]) s0) => //.
      apply (partialMonotonicity_freshness).
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
  

  Lemma partialMonotonicity_warm_monotone: forall σ σ' l, σ ⪯ σ' -> (σ ⊨ l : warm) -> (σ' ⊨ l : warm).
  Proof.
    unfold reachable_warm. intros σ σ' l H [C [ω [args [fields[ methods [H2 [H3 H4]] ]]]]].
    unfold partialMonotonicity, initializedFields in H.
    move /(_ l fields):H => H.
    rewrite H2 in H.
  Admitted. (* Issue here *)
  
  



End PartialMonotonicity.
