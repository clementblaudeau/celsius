Require Import ssreflect ssrbool.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.PeanoNat.


Theorem strong_induction:
  forall P : nat -> Prop,
    (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
    forall n : nat, P n.
Proof.
  intros.
  apply H.
  induction n ; intros.
  + apply PeanoNat.Nat.nlt_0_r in H0 => //.
  + move : (H n) => H1.
    destruct k.
    ++  destruct n.
        +++ apply H1.
            intros. apply PeanoNat.Nat.nlt_0_r in H2 => //.
        +++ apply IHn.
            apply PeanoNat.Nat.lt_0_succ.
    ++ apply Lt.lt_S_n in H0.
       apply H.
       intros l H2.
       apply IHn.
       apply Lt.lt_n_Sm_le in H2.
       apply (PeanoNat.Nat.le_lt_trans l k n) => //.
Qed.


(* Technical lemma that appears in proofs from time to time *)
Lemma strong_induction_rewrite:
  forall (P:nat -> Prop) n, (forall k : nat, S k <= S n -> P k) <-> (forall k : nat, k < S n -> P k).
  intros.
  split; intros; pose proof (Nat.lt_succ_r k n); eauto.
Qed.
