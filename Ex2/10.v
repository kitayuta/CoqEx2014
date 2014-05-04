Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).

Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.

Lemma inv_r : forall x, x * / x = 1.
Proof.
  intros.
  replace (x * / x) with ((1 * x) * / x).
  replace (1 * x) with (((/ / x) * (/ x)) * x).
  replace (/ / x * / x * x) with (/ / x * (/ x * x)).
  rewrite inv_l.
  rewrite <- mult_assoc.
  rewrite one_unit_l.
  apply inv_l.
  apply mult_assoc.
  rewrite inv_l.
  reflexivity.
  rewrite one_unit_l.
  reflexivity.
Qed.

Lemma one_unit_r : forall x, x * 1 = x.
Proof.
  intros.
  replace 1 with (/x * x) by apply inv_l.
  rewrite mult_assoc.
  rewrite inv_r.  
  apply one_unit_l.  
Qed.