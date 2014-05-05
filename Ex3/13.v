Inductive pos : Set :=
| SO : pos
| S : pos -> pos.

Fixpoint plus(n m:pos) : pos :=
  match n with
    | SO => S m
    | S p => S (p + m)
  end
    where "n + m" := (plus n m).

Infix "+" := plus.

Theorem plus_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  f_equal.
  assumption.
Qed.
