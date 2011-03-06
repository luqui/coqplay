Require Import Arith.

Section iteration.

Variable A : Type.
Variable f : A -> A.
Variable measure : A -> nat.
Hypothesis measure_decreases : forall x, measure (f x) = 0 \/ measure (f x) < measure x.

Fixpoint iterate_helper (n : nat) (x : A) : A :=
  match n with
  | O => x
  | S n' => match measure x with
            | O => x
            | _ => iterate_helper n' (f x)
            end
  end.

Definition iterate (x : A) : A := iterate_helper (measure x) x.

Lemma measuring_lemma : forall n x, measure x <= S n -> measure (f x) <= n.
 intros.
 destruct (measure_decreases x).
 rewrite H0.
 apply le_O_n.
 apply lt_n_Sm_le.
 apply (lt_le_trans _ _ _ H0 H).
Qed.

Lemma iterate_terminates_lemma : forall n x, measure x <= n -> measure (iterate_helper n x) = 0.
 induction n ; intros ; simpl.
 symmetry.
 apply (le_n_O_eq (measure x)) ; assumption.
 set (m := measure x).
 assert (measure x = m) ; trivial.
 destruct m.
 assumption.
 pose (measuring_lemma n x H).
 pose (IHn (f x) l).
 assumption.
Qed.

Theorem iterate_terminates : forall x, measure (iterate x) = 0.
 intro.
 apply iterate_terminates_lemma.
 constructor.
Qed.

End iteration.