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


(* ------------------------------------------------------------------------ *)
(** ** Example 2 *)
(*

class ConstStream () {
 var tail = this
}

class Entry () {
 def main() {
   new ConstStream()
 }
}

*)

(** ** Definitions *)
(* To put in Language.v *)


Definition ConstStream := cln(1).
Definition Entry := cln(0).
Definition EntryClass :=
  class nil nil (fun m => if (let 'mtd n := m in PeanoNat.Nat.eqb n 0)
                       then Some (method hot nil (ConstStream,hot) (e_new ConstStream nil))
                       else None).

Definition Ξ : list Class :=
  [(* Main Class *)
    EntryClass;

    (* Class ConstStream *)
    class nil [field (ConstStream, cold) (e_this)] (fun _ => None)
  ].

Lemma EntryClass_ct : ct Entry = EntryClass.
Proof. unfold ct, Entry. simpl. reflexivity. Qed.

(** ** Typing *)
(* To put in Soundness.v *)

Lemma typable_classes : T_Classes.
Proof with (unfold ConstStream, Entry; simpl; eauto with typ).
  unfold T_Classes.
  intros [c].
  assert (c = 1 \/ (c = 0 \/ c > 1)) as [|] by lia; subst; simpl.
  - (* Class ConstStream *)
    split.
    + eapply t_fields_cool_cons; eauto using T_Fields.
      simpl...
    + intros. inverts H.
  - (* Class Entry *)
    assert (P_hots []) by (unfold P_hots; eauto using Forall).
    steps; try lia...
    all: try eapply t_new_hot...
Qed.


(* ------------------------------------------------------------------------ *)
(** ** Example 3 *)
(*

class Server (a : Address) {
 var address : (Address: hot) = a
 var _ = this.broadcast()

 @ cool{address} def broadcast() : (Address: hot) = { this.address }
}

class Address () { }

class Entry () {
 def main() {
   new Server(new Address())
 }
}

*)

(** ** Definitions *)
(* To put in Language.v *)


Definition Server := cln(1).
Definition Address := cln(2).
Definition Entry := cln(0).

Definition EntryClass :=
  class nil nil (fun m => if (let 'mtd n := m in PeanoNat.Nat.eqb n 0)
                       then Some (method hot nil (Server,hot) (e_new Server [e_new Address []]))
                       else None).

Definition Ξ : list Class :=
  [(* Main Class *)
    EntryClass;

    (* Class Server *)
    class [(Address, hot)] [field (Address, hot) (e_var 0); field (Address, hot) (e_mtd (e_this) (mtd 0) nil)]
      (fun m => if (let 'mtd n := m in PeanoNat.Nat.eqb n 0)
                       then Some (method (cool 1) nil (Address,hot) (e_fld e_this 0))
                       else None);

    (* Class Adress *)
    class nil nil (fun _ => None)
  ].

Lemma EntryClass_ct : ct Entry = EntryClass.
Proof. unfold ct, Entry. simpl. reflexivity. Qed.
Definition main: Mtd := mtd(0).

(** ** Typing *)
(* To put in Soundness.v *)


Lemma typable_classes : T_Classes.
Proof with (unfold Address, Server, Entry; simpl; eauto with typ lia).
  unfold T_Classes. intros C.
  assert (C = Address \/ C = Server \/ ct C = ct Entry). {
    destruct C as [c].
    assert (c = 1 \/ c = 2 \/ (c = 0 \/ c > 2)) as [|[|[|]]] by lia;
      subst; unfold Address, Server, Entry; simpl; auto.
    right. right. repeat (destruct c; try lia; auto).
  }
  destruct H as [|[|]]; rewrite H; subst...
  - (* Class Address *)
    split.
    + eapply t_fields_nil.
    + intros. inverts H.
  - (* Class Server *)
    split.
    + eapply t_fields_cool_cons; eauto using T_Fields; simpl...
      eapply t_fields_cool_cons; eauto using T_Fields; simpl.
      eapply t_call with (C := cln 1) (μ0 := cool 1); steps...
    + intros.
      destruct m. steps...
  - (* Class Entry *)
    assert (P_hots []) by (unfold P_hots; eauto using Forall).
    unfold Entry in *.
    split; [eauto using T_Fields | steps].
    unfold Server, Address.
    eapply t_new_hot with (argsTs:=[(cln 2, hot)]); steps...
    eapply t_exprs_cons...
    eapply t_new_hot...
Qed.
