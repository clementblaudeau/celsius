From Celsius Require Export Trees.
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
  Proof. unfold partialMonotonicity. intros. assumption.
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

Lemma getObj_last : forall (σ : Store) (c:ClN) (e:Env), getObj (σ ++ [(c,e)]) (dom σ) = Some (c,e).
  Proof.
    intros.    induction σ.
    simpl => //.
    simpl => //.
Qed.
    
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


