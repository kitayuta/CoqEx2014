Require Import Lists.List.

Fixpoint sum (xs: list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

Theorem Pigeon_Hole_Principle :
  forall (xs : list nat), length xs < sum xs -> (exists x, 1<x /\ In x xs).
Proof.
  intros.
  induction xs.
  simpl in H.
  exfalso.
  apply (Lt.lt_n_0 0 H).
  induction a.
  simpl in H.
  assert (exists x : nat, 1 < x /\ In x xs).
  apply IHxs.
  apply (Lt.lt_trans (length xs) (S (length xs)) (sum xs) (Lt.lt_n_Sn (length xs)) H).
  destruct H0.
  exists x.
  destruct H0.
  split.
  assumption.
  simpl.
  right.
  assumption.
  induction a.
  simpl in H.
  apply Lt.lt_S_n in H.
  apply IHxs in H.
  destruct H.
  destruct H.
  exists x.
  split.
  assumption.
  simpl.
  right.
  assumption.
  exists (S (S a)).
  split.
  apply Lt.lt_n_S.
  apply Lt.lt_0_Sn.
  simpl.
  left.
  reflexivity.
Qed.
