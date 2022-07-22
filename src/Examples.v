(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(* This files shows the examples of the paper. To check it, replace the definition of the parameters
in Language.v with those, and rerun the proofs up to the soundness theorem. I plan to make it
cleaner with a centralized import. *)


(* ------------------------------------------------------------------------ *)
(** ** Example 1 *)
(*

class A () {
 var b = new B(this)
}

class B (x : (A,cold)) {
 var a = x
}

class Entry () {
 def main() {
   new A()
 }
}

*)

(** ** Definitions *)
(* To put in Language.v *)

Definition A := cln(1).
Definition B := cln(2).
Definition Entry := cln(0).
Definition EntryClass :=
  class nil nil (fun m => if (let 'mtd n := m in PeanoNat.Nat.eqb n 0)
                       then Some (method hot nil (A,hot) (e_new A nil))
                       else None).

Definition Ξ : list Class :=
  [(* Main Class *)
    EntryClass;

    (* Class A *)
    class nil [field (B,warm) (e_new B [e_this])] (fun _ => None);

    (* Class B *)
    class [(A,cold)] [field (A,cold) (e_var 0)] (fun _ => None)
  ].

Lemma EntryClass_ct : ct Entry = EntryClass.
Proof. unfold ct, Entry. simpl. reflexivity. Qed.

(** ** Typing *)
(* To put in Soundness.v *)

Lemma typable_classes : T_Classes.
Proof with (unfold A, B, Entry; simpl; eauto with typ).
  unfold T_Classes.
  intros [c].
  assert (c = 1 \/ c = 2 \/ (c = 0 \/ c > 2)) as [|[|]] by lia; subst; simpl.
  - (* Class A *)
    split.
    + eapply t_fields_cool_cons; eauto using T_Fields.
      eapply t_new...
    + intros. inverts H.
  - (* Class B *)
    split.
    + eapply t_fields_cool_cons ; eauto using T_Fields.
      eapply t_var...
    + intros. inverts H.
  - (* Class Entry *)
    assert (P_hots []) by (unfold P_hots; eauto using Forall).
    steps; try lia...
    + eapply t_new_hot...
    + eapply t_new_hot...
    + eapply t_new_hot...
Qed.
