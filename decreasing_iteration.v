Require Import Arith.
Set Implicit Arguments.

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

Ltac smart_destruct H := 
  let m := fresh "m" in
  set (m := H) ; assert (H = m) ; trivial ; destruct m.

Hint Resolve le_n_O_eq sym_eq measuring_lemma.

Lemma iterate_terminates_lemma : forall n x, measure x <= n -> measure (iterate_helper n x) = 0.
 induction n ; simpl ; [ auto | intros ; smart_destruct (measure x) ; auto ].
Qed.

Theorem iterate_terminates : forall x, measure (iterate x) = 0.
 intro ; apply iterate_terminates_lemma ; auto.
Qed.

End iteration.

Check iterate_terminates.