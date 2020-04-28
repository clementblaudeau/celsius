From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
From Celsius Require Export Reachability.
Require Import ssreflect ssrbool.



Module Reachability.
  Import Eval.Evaluator.
  Import Reachability.Reachability.
  Import PartialMonotonicity.PartialMonotonicity.
  
  Definition stackability (σ σ' : Store) :=
    forall l, l < (dom σ') -> ((σ' ⊨ l : warm) \/ (l < (dom σ))).
  Notation "σ ≪ σ'" := (stackability σ σ') (at level 80).
  
  Lemma stackability_reflexivity: forall σ, σ ≪ σ.
  Proof.
    unfold stackability. right => //.
  Qed.

  Lemma stackability_transitivity: forall σ1 σ2 σ3,
      σ1 ≪ σ2 -> σ2 ≪ σ3 -> σ2 ⪯ σ3 -> σ1 ≪ σ3.
  Proof.
    unfold stackability.
    intros.
    case /(_ l H2):H0 => H0.
    - left => //.
    - case /(_ l H0):H => H.
      + left. apply: (partialMonotonicity_warm_monotone σ2 σ3 l H1 H) => //.
      + right => //.
  Qed.      

  Lemma stackability_assignment : forall (σ σ': Store) (l l': Loc) (C: ClN) (f: Value) (ω ω': Env),
      (getObj σ l) = Some (C, ω) ->
      ω' = [f ↦ l']ω ->
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



    


    

  
    
    
      
    

