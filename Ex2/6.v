Require Import Arith.

Goal forall x y, x < y -> x + 10 < y + 10.
Proof.
  intro.
  intro.
  apply plus_lt_compat_r.
Qed.