Require Import Arith.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  exact plus_permute_2_in_4.
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  intros.
  rewrite mult_plus_distr_r.
  rewrite! mult_plus_distr_l.
  replace (m * n) with (n * m) by apply mult_comm.
  replace (n * m + m * m) with (m * m + n * m) by apply plus_comm.
  rewrite plus_permute_2_in_4.
  replace (n * m + n * m) with  (n * m * 1 + n * m).
  rewrite mult_n_Sm.
  replace ((n * m) * 2) with (2 * (n * m)) by apply mult_comm.
  rewrite mult_assoc.
  reflexivity.
  rewrite mult_1_r.
  reflexivity.
Qed.