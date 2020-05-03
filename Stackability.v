From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
From Celsius Require Export Reachability.
From Celsius Require Export Compatibility.
Require Import ssreflect ssrbool.


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
    move: (update_one3 _ l (C,ω') σ).
    rewrite -H1 => H3.
    rewrite -H3 => //.
  Qed.


  Definition stackability_prop (k : nat) :=  forall (e: Expr) (σ σ': Store) (ρ: Env) (v v': Value),
      ⟦e⟧(σ, ρ, v)(k) = (Success v' σ') -> σ ≪ σ'.

  Definition stackability_prop_list (k : nat) :=  forall (l: list Expr) (σ1 σ2: Store) (ρ: Env) (v : Value) (v_list: list Value),
      ⟦_ l _⟧(σ1, ρ, v)(k) = (Success_list v_list σ2) -> σ1 ≪ σ2 /\ σ1 ⪯ σ2 /\ σ1 ⊆ σ2.

  Definition stackability_prop_list2 (k : nat) :=  forall (l: list Expr) (σ1 σ2 σ3: Store) (ρ: Env) (v : Value) (v_list1 v_list2 : list Value),
      fold_left (eval_list_aux σ1 ρ v k) l (Success_list v_list1 σ2) = (Success_list v_list2 σ3) -> σ2 ≪ σ3 /\ σ2 ⪯ σ3 /\ σ2 ⊆ σ3.


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
      eauto using stackability_reflexivity with pM cmpt.
    + (* case e::l *)
      intros. simpl in H0. destruct k => //.
      ++ (* k = 0, timeout *)
        simpl in H0. rewrite foldLeft_constant in H0 => //.
      ++ (* k > 0 *)
            move: (PeanoNat.Nat.lt_succ_l _ _ H_bound) => Hn.
            assert ((forall k0 : nat, k0 < n -> compatibility_prop k0)) as H_comp. {
              intros. apply compatibility_theorem.
            }
(*            move: (compatibility_rec_step_list2 n H_comp (S k) H_bound l σ1 σ1 _ _ _ _ _ H0). *)
            
        simpl in H0.
        destruct (⟦ e ⟧ (σ2, ρ, v )( k)) eqn: E.
        +++ rewrite foldLeft_constant in H0 => //. 
        +++ rewrite foldLeft_constant in H0 => //. 
        +++ simpl in IHl.
            apply (IHl σ1 s σ3 ρ v (v0::v_list1) v_list2) in H0.
            move: H0 => [H01 [H02 H03]].
            move: (partialMonotonicity_theorem k e σ2 s ρ v v0 E) => H1.
            move: (compatibility_theorem k e _ _ _ _ _  E) => H_c2s.
            apply (H _ (PeanoNat.Nat.lt_succ_l _ _ H_bound))in E.
            move: (stackability_transitivity σ2 s σ3 E H01 H02 H03) => Hσ23.
            move: (compatibility_transitivity σ2 s σ3 H_c2s H03) => H_cσ23.
            split => //. split => //.
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


  Definition stackability_prop_init (k : nat) :=  forall (args_val: list Var) (C: ClN) (σ σ_res: Store),
      (init (length σ) args_val C (σ++[(C,[])]) k) = Some σ_res -> σ ≪ σ_res /\ σ ⪯ σ_res /\ σ ⊆ σ_res.

  Lemma stackability_init_warm : forall (F: list Field) (n: nat) (args_val: list Var) (I: Loc) (s1 s2: Store) (C: ClN) (ρ: Env),
      I < dom s1 ->
      (getObj s1 I) = Some (C, ρ) -> 
      (forall (k: nat), (k < n) -> stackability_prop k) ->
      fold_left (init_field args_val I n) F (Some s1) = Some s2 ->
      s1 ⊆ s2 /\ s1 ≪ s2 /\ s1 ⪯ s2 /\ 
      (exists ρ', (getObj s2 I) = Some (C, ρ') /\ ((length F + length ρ) <= length ρ')).
  Proof.
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
      destruct n => //.
      ++ simpl in H1.
         rewrite foldLeft_constant in H1 => //.
      ++ destruct a as [ t e ] eqn:fieldEq.
         simpl in H1.
         destruct ( ⟦ e ⟧ (s1, args_val, I)( n)) eqn:E => //.
         +++ rewrite foldLeft_constant in H1 => //.
         +++ rewrite foldLeft_constant in H1 => //.
         +++ rewrite {2}/assign_new in H1.
             destruct (getObj s I) eqn:G.
             destruct o.
             simpl.
             assert (I < dom s) as H_doms2. {
               apply (getObj_dom _ (c, e0) _ G).
             }
             assert (I < dom [I ↦ (c, e0 ++ [v])] (s)) as H_doms. {         
               unfold dom.
               rewrite update_one3.
               apply H_doms2.
             }
             move: (getObj_update1 s (c,e0++[v]) I H_doms2) => H_sobj. 
             move: (IHF (e0++[v]) ([I ↦ (c, e0 ++ [v])] (s)) s2 c H1 H_doms H_sobj).
             rewrite app_length. simpl.
             rewrite PeanoNat.Nat.add_1_r.
             rewrite -plus_n_Sm.
             move => [H1_cmp1 [H_stk1 [H_pm1 [ ρ' [H_obj H_flen]]]]].
             assert ( length e0 <= length (e0 ++ [v])) as H_len_e0.
             rewrite app_length. simpl. rewrite PeanoNat.Nat.add_1_r.
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
             exists ρ' ; split => //.
             ++++ unfold compatible in H_cmp3.
                  move /(_ I C ρ H0):H_cmp3 => [ω' H_cmp3].
                  rewrite G in H_cmp3. invert_constructor_equalities.
                  rewrite H_obj H3 => //.
             ++++ 
             apply (PeanoNat.Nat.le_trans _ (S (length F + length e0)) _).
             apply le_n_S.
             apply Plus.plus_le_compat_l. 
             apply H_len_ρ. auto.
             ++++ rewrite foldLeft_constant in H1 => //.
         +++  rewrite foldLeft_constant in H1 => //.
  Qed.


  Lemma stackability_rec_step_init : forall (n : nat),
      (* Strong induction *)
      (forall (k: nat), (k < n) -> stackability_prop k) ->
      (forall (k: nat), (k < n) -> stackability_prop_init k).
  Proof.
    intros n H_strong k H_bound.
    unfold stackability_prop_init => args_val C σ σ_res H.
    destruct k => //.
    simpl in H.
    destruct (ct C) eqn:H_class  => //.
    destruct c.
    assert (length σ < dom (σ ++ [(C, [])])) as H_len. {  
      rewrite /dom app_length; simpl. rewrite PeanoNat.Nat.add_1_r. apply PeanoNat.Nat.lt_succ_diag_r.
    }
    move : (getObj_last σ C []) => H_obj.
    assert ((forall k0 : nat, k0 < k -> stackability_prop k0)) as H_strong2. {
      intros. apply H_strong.
      apply (PeanoNat.Nat.lt_trans _ k _) => //.
      apply PeanoNat.Nat.lt_succ_l => //.
    }
    move: (stackability_init_warm fields k args_val (length σ) (σ++[(C,[])]) σ_res C [] H_len H_obj H_strong2 H) => [H_cmp1 [H_stk1 [H_pm1 [ρ' [H_obj2 H_flen]]]]]. 
    simpl in H_flen. rewrite PeanoNat.Nat.add_0_r in H_flen.
    split.
    + move :H_stk1. unfold stackability, dom => H_stk1 l H_l.
      move /(_ l H_l):H_stk1 => H_stk1.
      case: H_stk1; auto.
      rewrite app_length. simpl. rewrite PeanoNat.Nat.add_1_r => H_l'.
      move:(Lt.le_lt_or_eq _ _  (Lt.lt_n_Sm_le _ _ H_l') ) => [ H_l'' | H_l'' ].
      right => //.
      left. rewrite H_l''. unfold reachable_warm.
      exists C, ρ', args, fields, methods. repeat split => //.
    + split. apply (partialMonotonicity_transitivity _ (σ++[(C,[])]) _) => //.
      apply partialMonotonicity_freshness.
      apply (compatibility_transitivity _ (σ++[(C,[])]) _) => //.
      apply compatibility_freshness.
  Qed.  


  Lemma stackability_freshness : forall (σ: Store) (c: ClN) (ρ: Env),
      [(c, ρ)] ⊨ 0 : warm -> 
                     σ ≪ σ++[(c,ρ)].
  Proof.
    unfold stackability, dom.
    intros.
    rewrite app_length in H0; simpl in H.
    rewrite PeanoNat.Nat.add_1_r in H0.
    move: (Lt.le_lt_or_eq l (length σ) (Lt.lt_n_Sm_le _ _ H0)) => [H1 | H1].
    right => //.
    left.
    move: H0 H1. induction σ; simpl; intros => //.
    - rewrite H1 => //.
    - unfold reachable_warm.
      unfold reachable_warm in H.
      destruct H as [C [ω [args [fields [methods [H [H_ct H_len]]]]]]].
      simpl in H.
      injection H => H3 H4.    
      exists c, ρ, args, fields, methods.
      rewrite H1 H4 H3. 
      destruct σ => //.
      simpl.
      rewrite getObj_last.
      repeat (split; auto).
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
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    destruct e.    
    - (* case e = x *)
      repeat light || invert_constructor_equalities || destruct_match || eauto using stackability_reflexivity with pM.
    - (* case e = this *)
      repeat light || invert_constructor_equalities || destruct_match || eauto using stackability_reflexivity with pM. 
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
      repeat light || invert_constructor_equalities || destruct_match || eauto using stackability_reflexivity with pM. 
      move : (partialMonotonicity_theorem n body s0 σ' _  v v' H) => H_pm1.
      move : (partialMonotonicity_theorem n e _ _ _  _ _ matched) => H_pm2.
      move : (compatibility_theorem n body s0 σ' _  v v' H) => H_cmp1.
      move : (compatibility_theorem n e _ _ _  _ _ matched) => H_cmp2.      
      move : (H_strong n Hn e σ s ρ v v0 matched) => H_stk1.
      move : (H_strong n Hn body s0 σ' _ v v' H) => H_stk2.
      move : (stackability_rec_step_list (S n) H_strong n Hn l s s0 ρ v l0 matched3)=> [H_stk3 [H_pm3 H_cmp3]].
      eauto using partialMonotonicity_transitivity, stackability_transitivity, compatibility_transitivity.
    - (* case e = new C(l) *)
      repeat light || invert_constructor_equalities || destruct_match || eauto using stackability_reflexivity with pM.
      move : (stackability_rec_step_list (S n) H_strong n Hn l _ _ ρ v l0 matched)=> [H_stk1 [H_pm1 H_cmp1]].
      move : (stackability_rec_step_init (S n) H_strong n Hn _ _ _ _ matched0) => [H_stk2 [H_pm2 H_cmp2]].
      eauto using partialMonotonicity_transitivity, stackability_transitivity, compatibility_transitivity.
    - (* case e1.v0 = e2 ; e3 *) (* can be cleaned ! *)
      repeat light || invert_constructor_equalities || destruct_match || eauto using stackability_reflexivity with pM.
      move : (partialMonotonicity_theorem n e1 _ _ _  _ _ matched) => H_pm1.
      move : (partialMonotonicity_theorem n e2 _ _ _  _ _ matched0) => H_pm2.
      move : (partialMonotonicity_theorem n e3 _ _ _  _ _ H) => H_pm3.
      move : (compatibility_theorem n e1 _ _ _  _ _ matched) => H_cmp1.
      move : (compatibility_theorem n e2 _ _ _  _ _ matched0) => H_cmp2.
      move : (compatibility_theorem n e3 _ _ _  _ _ H) => H_cmp3.            
      move : (H_strong n Hn _ _ _ _ _ _ matched) => H_stk1.
      move : (H_strong n Hn _ _ _ _ _ _ matched0) => H_stk2.
      move : (H_strong n Hn _ _ _ _ _ _ H) => H_stk3.
      destruct (getObj s0 v1) eqn: G => //.
      + destruct o.
        set s' := [v1 ↦ (c, [v0 ↦ v2] (e))] s0.
           move: (PeanoNat.Nat.eq_le_incl _ _ (eq_sym (update_one3 _ v0 v2 e))) => H_len.
        move: (stackability_assignment s0 s' v1 c e [v0 ↦ v2] (e) G H_len eq_refl) => H_stk4.
        move: (partialMonotonicity_assignment s0 s' v1 c e [v0 ↦ v2] (e) G H_len eq_refl) => H_pm4.
        move: (compatibility_assignment s0 s' v1 c e [v0 ↦ v2] (e) G eq_refl) => H_cmp4.
        assert ( s' = assign v1 v0 v2 s0) as H_assign. {
          unfold assign => //.
          rewrite G => //.
        }
        rewrite -H_assign in H_pm3 H_cmp3 H_stk3.
        eauto using partialMonotonicity_transitivity, stackability_transitivity, compatibility_transitivity.
      + rewrite /assign G in H H_pm3 H_cmp3 H_stk3.
        eauto using partialMonotonicity_transitivity, stackability_transitivity, compatibility_transitivity.
Qed.        
  
  Theorem stackability_theorem: forall (n : nat), (stackability_prop n).
  Proof.
    intros.
    move: (stackability_theorem_rec_step) => H.
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
  
End Stackability.
