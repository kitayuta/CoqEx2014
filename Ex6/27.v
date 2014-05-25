Require Import ZArith.
Require Import Omega.

Lemma hoge : forall z : Z, (z ^ 4 - 4 * z ^ 2 + 4 > 0)%Z.
Proof.
  intro.
  replace (z^4-4*z^2+4)%Z with ((z*z-2)*(z*z-2))%Z by ring.
  rewrite <- Z.square_spec.
  assert (forall p, (Z.pos p * Z.pos p - 2)%Z <> 0%Z).
  intros.
  destruct p.
  remember (Z.pos p~1) as m3.
  assert (m3 >= 3)%Z.
  rewrite Heqm3.
  unfold Z.ge.
  simpl.
  unfold Pos.compare, Pos.compare_cont.
  destruct p.
  congruence.
  congruence.
  congruence.
  assert (m3*m3 >= 3*m3)%Z.
  apply Zmult_ge_compat_r.
  assumption.
  omega.
  omega.
  remember (Z.pos p~0) as m2.
  assert (m2 >= 2)%Z.
  rewrite Heqm2.
  unfold Z.ge.
  simpl.
  unfold Pos.compare, Pos.compare_cont.
  destruct p.
  congruence.
  congruence.
  congruence.
  assert (m2*m2 >= 2*m2)%Z.
  apply Zmult_ge_compat_r.
  assumption.
  omega.
  omega.
  omega.
  assert (z*z-2 <> 0)%Z.
  destruct z.
  omega.
  apply H.
  replace (Z.neg p * Z.neg p)%Z with (Z.pos p * Z.pos p)%Z.
  apply H.
  simpl.
  reflexivity.
  remember (z*z-2)%Z as y.
  destruct y.
  congruence.
  simpl.
  unfold Z.gt.
  reflexivity.
  simpl.
  unfold Z.gt.
  reflexivity.
Qed.