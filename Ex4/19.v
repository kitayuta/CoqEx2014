Parameter A : Set.
Definition Eq : A -> A -> Prop :=
  fun x y => forall P : A -> Prop, P x <-> P y.
Lemma Eq_eq : forall x y, Eq x y <-> x = y.
Proof.
  unfold iff, Eq.
  split.
  intro.
  apply H.
  reflexivity.
  intros.
  rewrite H.
  apply iff_refl.
Qed.