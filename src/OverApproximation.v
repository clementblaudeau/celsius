(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** Store typing *)

From Celsius Require Export MetaTheory Reachability LibTactics.
Require Import Coq.ssr.ssreflect Coq.ssr.ssrbool Coq.Lists.List Coq.micromega.Psatz Ensembles.

Lemma ot_hot_dom: forall Σ C ω Args Flds Mtds,
    ct C = class Args Flds Mtds ->
    Σ ⊨ (C, ω) : (C, hot) ->
    dom Flds <= dom ω.
Proof with (meta; eauto with lia).
  intros.
  inverts H0.
  destruct (dom Flds) eqn: H__Flds...
  lets [ ]: fieldType_exists n H; steps...
  specialize (H5 n x μ) as [ ]; steps...
Qed.
Local Hint Resolve ot_hot_dom: typ.

Lemma ot_warm_dom: forall Σ C ω Args Flds Mtds,
    ct C = class Args Flds Mtds ->
    Σ ⊨ (C, ω) : (C, hot) ->
    dom Flds <= dom ω.
Proof with (meta; eauto with lia).
  intros.
  inverts H0.
  destruct (dom Flds) eqn: H__Flds...
  lets [ ]: fieldType_exists n H; steps...
  specialize (H5 n x μ) as [ ]; steps...
Qed.
Local Hint Resolve ot_warm_dom: typ.


Lemma object_over_approximation:
  forall Σ σ (l:Loc) μ,
    wf σ ->
    (Σ ⊨ σ) ->
    (Σ ⊨ l : μ) ->
    (σ ⊨ l : μ).
Proof with (meta; eauto with typ rch updates lia).
  intros ...
  lets [?C [?ω [?μ ?]]]: H0 H1; steps...
  destruct (ct C) as [Args Flds Mtds] eqn:H__ct ...
  destruct μ0 as [ | | Ω | ], μ as [ | | Ω0 |];
    try solve [invert H5];
    try apply_anywhere s_mode_cool;
    try solve [eapply getObj_dom; eauto].
  - (* hot *)
    intros l' H__rch.
    eapply hot_transitivity in H__rch...
    + lets [?C [?ω [?μ [? [ ]]]]]: H0 H8.
      destruct (ct C1) as [?Args ?Flds ?Mtds] eqn:?H__ct ...
      exists C0, ω0, Args0, Flds0, Mtds0; steps...
    + exists C, (C, hot)...
  - (* hot ⊑ warm *)
    exists C ω Args Flds Mtds; steps...
  - (* hot ⊑ cool Ω *)
    exists C ω Args Flds Mtds; steps...
    admit.
  - (* warm *)
    exists C ω Args Flds Mtds; steps...
    eapply wf_proj2 ...








        steps.


      unfold fieldType; steps... reflexivity.
      repeat eexists; steps...

    eapply H0 in H6.
    admit.
  - (* warm *)
    + repeat eexists; steps ...
      apply s_mode_cool in H4.
      inverts H6 ...
    + eapply getObj_dom...

  - (* cool *)
    destruct μ; try solve [invert H4] ...
    + repeat eexists; steps ...
      apply s_mode_cool in H4.
      inverts H6 ...
    + eapply getObj_dom...
  - (* cold *)
    destruct μ; try solve [invert H4] ...
    eapply getObj_dom...
Qed.




    inverts H4. admit.

  - (* cold *)


  lets : H H0.
  inverts H1 ; steps.
  inverts H2 .
  assert (S l <= dom Σ) by admit.
  specialize (H l); steps.
  rewrite H0 in H; invert_constructor_equalities; steps.
  destruct μ.
  + assert (μ0 = hot) by (inverts H4; steps); subst.
    invert H5; steps.
    intros l' H__l'.
    destruct (getObj σ l') as [[D ω'] |] eqn:getObj.
    exists D, ω'. do 3 eexists.
    split => //.
    split => //.

  + admit.
  + admit.
  + inverts H4.

  inversion H1; steps.
  inversion H2; steps.
  specialize (H l); steps.
  assert (S l <= dom Σ) by admit. steps.
  inversion H7; steps.
  + (* hot *)
    admit.
  + (* warm *)
    exists C0, ω.
  inversion H5; steps.


  + (* hot *)
    admit.
  + (* warm *)
    specialize (H l); steps.
    assert (S l <= dom Σ) by admit. steps.
    inversion H7; steps.
    exists C0, ω.
    inversion H5; steps.
