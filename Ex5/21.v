Require Import Classical.

Lemma ABC_iff_iff :
    forall A B C : Prop, ((A <-> B) <-> C) <-> (A <-> (B <-> C)).
Proof.
  intros.
  tauto.
Qed.

Goal
  forall P Q R : Prop,
  (IF P then Q else R) ->
  exists b : bool,
  (if b then Q else R).
Proof.
  intros.
  destruct H.
  exists true.
  tauto.
  exists false.
  tauto.
Qed.

Require Import IndefiniteDescription.

Goal
  forall P Q R : nat -> Prop,
  (forall n, IF P n then Q n else R n) ->
  exists f : nat -> bool,
  (forall n, if f n then Q n else R n).
Proof.
  intros.
  apply (functional_choice (fun (x:nat) (b:bool) => if b then Q x else R x)).
  intro.
  destruct (H x).
  exists true.
  tauto.
  exists false.
  tauto.
  Qed.
