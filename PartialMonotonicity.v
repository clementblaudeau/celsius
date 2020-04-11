From Celsius Require Export Trees.
From Celsius Require Export Eval.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.


Definition dom {X: Type} (x: list X) : nat :=
  (length x).

Definition initializedFields (σ: Store) (l: Loc) (f: list Field) : Prop :=
  match (getObj σ l) with
    | Some (C, ω) => ((length ω) <= (length f))
    | _ => False
  end.

Notation "σ ⊨ l : f" := (initializedFields σ l f) (at level 80, l at level 0).

Definition partialMonotonicity (σ σ': Store) :=
  forall l f, l < (dom σ) -> (σ ⊨ l : f) -> (σ' ⊨ l : f).

Notation "σ ⪯ σ'" := (partialMonotonicity σ σ') (at level 80).

Lemma partialMonotonicity_reflexivity : forall (σ : Store), σ ⪯ σ.
  Proof. unfold partialMonotonicity => //.
  Qed.

Lemma initializedFields_dom : forall (σ: Store) (l: nat) (f: list Field), (σ ⊨ l : f) -> (l < (dom σ)).
  Proof.
  move => σ.
  induction σ.
  intros.
  unfold initializedFields in H.
  unfold getObj in H.
  destruct l.
  simpl in H => //.
  simpl in H => //.
  destruct a.
  intros.
  unfold initializedFields in H.
  destruct l.
  simpl.
  apply (PeanoNat.Nat.lt_0_succ).
  simpl.
  Search _ (S _ < S _).
  apply (Lt.lt_n_S).
  simpl in H.
  unfold initializedFields in IHσ.
  apply IHσ in H => //.
Qed.

Lemma initializedFields_exists : forall (σ: Store) (c: ClN) (e: Env), exists (f: list Field), ((c,e)::σ) ⊨ (dom σ) : f.
  Proof.
    unfold initializedFields.
    induction σ.
    - intros.
      simpl.
      exists (repeat (field 0 (0,hot) this) (length e)).
      Search _ (repeat _).
      rewrite repeat_length.
      apply le_n.
    - intros.
      simpl => //.
      destruct a.
      apply IHσ.
Qed.      
 (* 
Lemma domBounds : forall (σ: Store) (l: nat), (l < (dom σ) -> exists C ω , (getObj σ l) = (Some (C, ω))) /\ (l >= (dom σ) -> (getObj σ l) = None).
  Proof.
    induction σ.
    * intros.
      unfold getObj.
      simpl.
      destruct l.
      simpl.
      split => h.
      move: (PeanoNat.Nat.nlt_0_r 0) => h1 => //.
      reflexivity.
      split => h.
      move: (PeanoNat.Nat.nlt_0_r (S l)) => h1 => //.
      simpl => //.
    * intros.
      simpl.
      split.
      - move => h.
        destruct l.
        simpl.
        destruct a.
        exists c, e => //.
        Search _ (S _ < S _).
        move : (Lt.lt_S_n l (dom σ)) => h1.
        apply h1 in h.
        apply IHσ in h.
        simpl => //.
      - move => h.
        destruct l.
        move : (PeanoNat.Nat.nle_succ_0 (dom σ)) => h1 => //.
        simpl.
        Search _ (S _ <= S _).
        unfold ge in h.
        move : (Le.le_S_n (dom σ) l) => h1.
        apply h1 in h.
        unfold ge in IHσ.
        apply IHσ in h => //.
Qed. *)        
    
Lemma partialMonotonicity_domains : forall (σ σ': Store), σ ⪯ σ' -> (dom σ) <= (dom σ').
  Proof.
    intros.    
    unfold partialMonotonicity in H.
    move : (initializedFields_dom σ') => Hσ'.
    destruct (σ) eqn:Σ.
    - apply le_0_n.
    - destruct o.
      move : (initializedFields_exists s c e) => He.
      case He => f Hf.
      move : (H (dom s) f ) => H1.
    simpl in H1.
    move : (PeanoNat.Nat.lt_succ_diag_r (dom s)) => H2.
    apply H1 in H2.
    Check initializedFields_dom.
    move : (initializedFields_dom σ' (dom s) f) => H3.
    apply H3 in H2.
    simpl.    
    Search _ (S _ <= _).
    apply Lt.lt_le_S => //.
    simpl => //.
Qed.

Lemma partialMonotonicity_transitivity : forall (σ1 σ2 σ3 : Store), ((σ1 ⪯ σ2) /\ (σ2 ⪯ σ3)) -> (σ1 ⪯ σ3).
  Proof.
    move => σ1 σ2 σ3 h1.
    destruct h1 as [h1  h2].
    move : (partialMonotonicity_domains σ1 σ2) => h3.
    move : (h3 h1) => h4.
    unfold partialMonotonicity.
    intros.
    unfold partialMonotonicity in h2, h1.
    apply h2.
    apply (PeanoNat.Nat.lt_le_trans l (dom σ1) ) => //.
    apply h1 => //.
Qed.    

Lemma getObj_update1 : forall (σ: Store) (o: Obj) (x: nat),
      x < dom σ -> (getObj [x ↦ o]σ x) = Some o.
  Proof.
  intros.
  move : (update_one1 Obj x o σ) => H1.
  unfold dom in H.
  unfold getObj.
  apply H1 => //.
Qed.  
  
Lemma getObj_update2 : forall (σ: Store) (o: Obj) (x x': nat),
      x < dom σ ->
      x <> x' ->
      (getObj [x ↦ o]σ x') = (getObj σ x').
  Proof.
  intros.
  move : (update_one2 Obj x x' o σ) => H1.
  unfold dom in H.
  unfold getObj.
  apply H1 => //.
Qed.

Lemma getObj_dom : forall (σ: Store) (o: Obj) (l: nat),
      (getObj σ l) = Some o ->
      l < (dom σ).
  Proof.
    intros.
    generalize dependent  l.
    induction σ.    
    - destruct l => H.
    simpl in H.
    discriminate H.
    simpl in H.
    discriminate H.
    - destruct l.
      simpl => H.
      apply PeanoNat.Nat.lt_0_succ.
      simpl => H.
      Search _ (_ < _ -> S _ < S _).
      apply Lt.lt_n_S.
      apply IHσ => //.
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
    - rewrite H1.
    rewrite H4.
    rewrite getObj_update1 => //.
    unfold initializedFields in H3.
    rewrite <- H4 in H3.
    rewrite H in H3 => //.
    move: (update_one3 Loc f l' ω) => H5.
    rewrite -H0 in H5.
    rewrite H5 => //.
    - move: (getObj_update2 σ (C, ω') l l0)=>H5.
      move: (initializedFields_dom σ l0 f0)=>H6.
      move: (H6 H3)=>H7.
      move: ((getObj_dom σ (C,ω) l) H) => H8.
      apply H5 in H8.
      rewrite H1 H8.
      unfold initializedFields in H3 => //.
      done.
Qed.


Theorem partialMonotonicity_theorem : forall (e: Expr) (ct: ClassTable) (σ σ': Store) (ρ: Env) (v v': Value) (k: nat),
      ⟦e⟧(ct, σ, ρ, v)(k) = (Success v' σ') -> σ ⪯ σ'.
  intros.
  generalize dependent k.
  generalize dependent v'.
  generalize dependent σ'.
  induction e.
  - (* case e = x *)
    move => σ' v' k H.
    destruct k. discriminate.
    unfold eval in H.
    destruct (getVal ρ v0) => //.
    injection H => H1 H2.
    rewrite H1.
    apply partialMonotonicity_reflexivity => //.
  - (* case e = this *)
    move => σ' v' k H.
    destruct k. discriminate.
    unfold eval in H.
    injection H => H1 H2.
    rewrite H1.
    apply partialMonotonicity_reflexivity => //.
  - (* case e = e0.field *)
    move => σ' v' k H.
    destruct k. discriminate.
    simpl in H.
    destruct  (⟦ e ⟧ (ct, σ, ρ, v )( k)) eqn:E.
    discriminate.
    discriminate.
    destruct (getObj s v1).
    destruct o.
    destruct (getVal e0 v0).
    injection H => H1 H2.
    rewrite<- H1.
    apply (IHe s v1 k) => //.
    discriminate.
    discriminate.
    discriminate.
  - (* case e = e0.m(ē) *)
    Abort.

    
    
