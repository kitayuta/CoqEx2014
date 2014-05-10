Definition True' : Prop := forall P : Prop, P -> P.
Goal True <-> True'.
Proof.
  unfold iff, True'.
  split.
  intros.
  assumption.
  intro.
  apply I.
Qed.
Goal True'.
Proof.
  unfold True'.
  intros.
  assumption.
Qed.

Definition False' : Prop := forall P : Prop, P.
Goal False' <-> False.
Proof.
  unfold iff.
  split.
  intro.
  apply H.
  apply False_ind.
Qed.
Goal forall P : Prop, False' -> P.
Proof.
  intros.
  apply H.
Qed.

Definition and' : Prop -> Prop -> Prop :=
  fun A B => forall P : Prop, (A -> B -> P) -> P.
Goal forall P Q : Prop, P /\ Q <-> and' P Q.
Proof.
  intros.
  unfold iff, and'.
  split.
  intro.
  destruct H.
  intros.
  exact (H1 H H0).
  intro.
  split.
  apply H.
  intros.
  assumption.
  apply H.
  intros.
  assumption.
Qed.

Definition or' : Prop -> Prop -> Prop :=
  fun A B => forall P : Prop, (A -> P) -> (B -> P) -> P.
Goal forall P Q : Prop, P \/ Q <-> or' P Q.
Proof.
  intros.
  unfold iff, or'.
  split.
  intros.
  destruct H.
  exact (H0 H).
  exact (H1 H).
  intro.
  apply H.
  apply or_introl.
  apply or_intror.
Qed.