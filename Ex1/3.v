Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  intros.
  destruct H.
  contradiction.
  assumption.
Qed.
