Theorem NotNot_LEM : forall P : Prop, ~ ~(P \/ ~P).
Proof.
  intros.
  intro.
  apply H.
  right.
  intro.
  apply H.
  left.
  assumption.
Qed.
