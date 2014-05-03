Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros.
  intro.
  destruct H.
  apply H.
  destruct H0.
  assumption.
  apply H.
  destruct H0.
  assumption.
Qed.
 
Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros.
  intro.
  destruct H.
  destruct H0.
  apply (H H0).
  apply (H1 H0).
Qed.
 
Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  split.
  intro.
  apply H.
  left.
  assumption.
  intro.
  apply H.
  right.
  assumption.
Qed.
