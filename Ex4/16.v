Definition tautology : forall P : Prop, P -> P
  := fun (P : Prop) (H : P) => H .

Definition Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P
  :=  fun (P Q : Prop) (H0 : ~ Q /\ (P -> Q)) (H1 : P) =>
        match H0 with conj L R => L (R H1) end.

Definition Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q
  := fun (P Q : Prop) (H0 : P \/ Q) (H1 : ~P) =>
       match H0 with
           | or_introl Hl => False_ind Q (H1 Hl)
           | or_intror Hr => Hr end.

Definition tautology_on_Set : forall A : Set, A -> A
  := fun (A : Set) (H : A) => H.

Definition Modus_tollens_on_Set : forall A B : Set, (B -> Empty_set) * (A -> B) -> (A -> Empty_set)
  := fun (A B : Set) (S0 : (B -> Empty_set) * (A -> B)) (S1 : A) =>
       let (L, R) := S0 in L (R S1).

Definition Disjunctive_syllogism_on_Set : forall A B : Set, (A + B) -> (A -> Empty_set) -> B
  := fun (A B : Set) (S0 : (A + B)) (S1 : A -> Empty_set) =>
       match S0 with
           | inl l => Empty_set_rec (fun _ : Empty_set => B) (S1 l)
           | inr r => r
       end.
