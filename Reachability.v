From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
Require Import ssreflect ssrbool. (*

Require Import List.
Import ListNotations.
Open Scope nat_scope. *)

(* Reserved Notation "σ ⊨ l1 ⇝ l2" (at level 80). *)
Inductive reachability : ClassTable -> Store -> Loc -> Loc ->Prop :=
|rch_heap  : forall ct l σ,  l < (dom σ) -> (reachability ct σ l l)
|rch_trans : forall ct l0 l1 l2 C ω σ, (reachability ct σ l0 l1) -> (getObj σ l1 = Some (C, ω)) -> (exists f, (getVal ω f = Some l2)) -> (l2 < dom σ) -> (reachability ct σ l0 l2).

Search _ (_ (_,_)).
Check fst.
Notation "σct ⊨ l1 ⇝ l2" := (reachability (snd σct) (fst σct) l1 l2) (at level 80, l1 at level 99).

Check rch_heap.
Check rch_trans.

Lemma reachability_trans: (forall ct σ l1 l2 l3, ((σ, ct) ⊨ l1 ⇝ l2) -> ((σ, ct) ⊨ l2 ⇝ l3) -> ((σ, ct) ⊨ l1 ⇝ l3)).
Proof.
  intros ct σ l1 l2 l3 H1 H2.
  induction H2 => //. 
  apply (rch_trans ct0 l1 l2 l3 C ω σ0 (IHreachability H1) H H0 H3). 
Qed.

Notation "σct ⊨ l : 'cold'" := (l < dom (fst σct)) (at level 80, l at level 99).
Notation "σct ⊨ l : 'warm'" := (exists C ω args fields methods , (getObj (fst σct) l) = Some (C, ω) /\ (((snd σct) C) = Some (class args fields methods)) /\ (length fields <= length ω)) (at level 80, l at level 99).
Notation "σct ⊨ l : 'hot'"  := (forall l', (σct ⊨ l ⇝ l') -> (σct ⊨ l' : warm)) (at level 80, l at level 99).


Lemma reachability_hot: forall (ct: ClassTable) (σ: Store) (l l': Loc), (σ, ct) ⊨ l: hot -> (σ, ct) ⊨ l ⇝ l' -> (σ, ct) ⊨ l': hot.
Proof.
  intros ct σ l l' H1 H2 l'' H3.
  apply (H1 l'' ((reachability_trans _ _ _ _ _) H2 H3)).
Qed. 
                                             
              
