Require Import Arith.

Definition Nat : Type :=
  forall A : Type, (A -> A) -> (A -> A).

Definition NatPlus(n m : Nat) : Nat :=
  fun _ f x => n _ f (m _ f x).

Definition nat2Nat : nat -> Nat := nat_iter.

Definition Nat2nat(n : Nat) : nat := n _ S O.

Lemma NatPlus_plus :
  forall n m, Nat2nat (NatPlus (nat2Nat n) (nat2Nat m)) = n + m.
Proof.
  intros.
  unfold nat2Nat, NatPlus, Nat2nat.
  induction n.
  simpl.
  induction m.
  simpl.
  reflexivity.
  simpl.
  f_equal.
  assumption.
  simpl.
  f_equal.
  assumption.
Qed.
