Require Import Setoid.

Section natf.

Variable A : Type.

CoInductive stream :=
| cons : A -> stream -> stream.

CoFixpoint natfToStream (f : nat -> A) : stream :=
  cons (f 0) (natfToStream (fun n => f (S n))).

Definition frobStream (s : stream) :=
  match s with
  | cons x xs => cons x xs
  end.

Lemma frobStream_id : forall s, s = frobStream s.
 destruct s ; reflexivity.
Qed.
 
Fixpoint streamToNatf (s : stream) (n : nat) : A :=
  match s with
  | cons x xs =>
    match n with
    | O => x
    | S n' => streamToNatf xs n'
    end
  end.

Theorem inv1 : forall n f, streamToNatf (natfToStream f) n = f n.
 induction n.
 simpl.
 trivial.
 simpl.
 intro f.
 rewrite (IHn (fun n0 : nat => f (S n0))).
 trivial.
Qed.

CoInductive streamEq : stream -> stream -> Prop :=
| consEq : forall x s t, streamEq s t -> streamEq (cons x s) (cons x t).

Theorem inv2 : forall s, streamEq (natfToStream (fun n => streamToNatf s n)) s.
 cofix.
 intros.
 destruct s.
 rewrite (frobStream_id (natfToStream (fun n => streamToNatf (cons a s) n))).
 simpl.
 apply consEq.
 apply inv2.
Qed.

End natf.