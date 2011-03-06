Require Import Arith.
Require Import List.
Set Implicit Arguments.


Ltac smart_destruct H := 
  let m := fresh "m" in
  set (m := H) ; assert (H = m) ; trivial ; destruct m.


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

Hint Resolve le_n_O_eq sym_eq measuring_lemma.

Lemma iterate_terminates_lemma : forall n x, measure x <= n -> measure (iterate_helper n x) = 0.
 induction n ; simpl ; [ auto | intros ; smart_destruct (measure x) ; auto ].
Qed.

Theorem iterate_terminates : forall x, measure (iterate x) = 0.
 intro ; apply iterate_terminates_lemma ; auto.
Qed.

End iteration.



Section context_map.

Variable A : Type.
Definition ContextMap := option A -> A -> option A -> A.
Variable f : ContextMap.

Fixpoint context_map_helper (lcx : option A) (xs : list A) : list A :=
  match xs with
  | nil     => nil
  | e :: es => match es with
               | nil => f lcx e None :: nil
               | e' :: es' => f lcx e (Some e') :: context_map_helper (Some e) es
               end
  end.

Definition context_map (xs : list A) := context_map_helper None xs.

End context_map.


Section count.

Variable A : Type.
Variable p : A -> bool.

Fixpoint count (lst : list A) : nat :=
  match lst with
  | nil => O
  | x :: xs => if p x then S (count xs) else count xs
  end.

Hint Resolve le_n_S le_S.

Lemma count_length : forall xs, count xs <= length xs.
 induction xs ; auto ; simpl ; destruct (p a) ; auto.
Qed.

End count.


Section soldiers.

Inductive Direction := E | W.
Definition State := list Direction.

Definition stepper : ContextMap Direction := fun l x r =>
  match x with
  | W => match l with
         | Some E => E
         | _ => W
         end
  | E => match r with
         | Some W => W
         | _ => E
         end
  end.

Definition step : State -> State 
  := context_map stepper.

Definition eqW := fun x => match x with E => false | W => true end.

Fixpoint measure (s : State) : nat :=
  match s with
  | nil => 0
  | E :: xs => count eqW xs + measure xs
  | W :: xs => measure xs
  end.

(* Need to show step decreases measure:
     Inductively, if a W changes to an E, then that can increase the measure.  We have to show that
     if a W changes to an E, that means the W was preceded by an E (which will change to a W), and
     thus the measure decreases by more than it increases.

   It would be helpful to have some lemmas about context_map to help us show this.
*)