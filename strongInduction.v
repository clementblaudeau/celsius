(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines a strong induction predicate *)
Require Import ssreflect ssrbool Coq.Arith.Lt Coq.Arith.PeanoNat Psatz.

(** Strong induction predicate is a strenghten version of the built-in induction *)
Theorem strong_induction:
  forall P : nat -> Prop,
    (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
    forall n : nat, P n.
Proof.
  intros.
  apply H.
  induction n ; intros; try lia.
  + move : (H n) => H1.
    destruct k.
    ++ destruct n; [apply H1 | apply IHn] ; lia.
    ++ apply H; intros; apply IHn. lia.
Qed.

(** Technical lemma that appears in proofs from time to time *)
Lemma strong_induction_rewrite:
  forall (P:nat -> Prop) n, (forall k : nat, S k <= S n -> P k) <-> (forall k : nat, k < S n -> P k).
  intros.
  split; intros; pose proof (Nat.lt_succ_r k n); eauto.
Qed.
