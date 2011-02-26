(* Painstaking proof that the standard equivalence relation
   defining rationals is in fact an equivalence relation *)

Require Import Equivalence.
Require Import Omega.
Require Import Arith.

Record Rat := mkRat { numer : nat ; denom : nat ; nonzero : denom <> 0 }.

Definition Rat_equiv r r' := numer r * denom r' = numer r' * denom r.

Instance Rat_equiv_Reflexive : Reflexive Rat_equiv.
 red ; destruct x ; unfold Rat_equiv ; simpl ; trivial.
Qed.

Instance Rat_equiv_Symmetric : Symmetric Rat_equiv.
 red ; intros.
 apply eq_Symmetric.
 assumption.
Qed.

Lemma le_antisym : forall x y, x <= y -> y <= x -> x = y.
 intros.
 destruct (le_lt_eq_dec _ _ H).
 apply le_not_gt in H0.
 contradiction.
 assumption.
Qed.

Lemma times_monotone : forall x y y', y < y' -> S x * y < S x * y'.
 induction x ; intros.
 simpl ; repeat rewrite <- plus_n_O ; assumption.
 rewrite mult_succ_l.
 pattern (S (S x) * y') ; rewrite mult_succ_l.
 pose (IHx _ _ H).
 apply (plus_lt_compat _ _ _ _ l H).
Qed.

Lemma nat_discrete : forall x y : nat, x = y \/ x <> y.
 induction x ; destruct y ; auto.
 destruct (IHx y) ; auto.
Qed.

Lemma mult_cancel_l_lemma : forall x y z, S z * x = S z * y -> x = y.
 intros.
 destruct (nat_discrete x y).
 assumption.
 destruct (nat_total_order _ _ H0) ;
 pose (l := times_monotone z _ _ H1) ;
 rewrite H in l ; 
 destruct (lt_irrefl _ l).
Qed.
 
Lemma mult_cancel_l : forall x y z, z <> 0 -> z * x = z * y -> x = y.
 intros.
 destruct z.
 simpl in H0 ; contradiction.
 apply (mult_cancel_l_lemma _ _ _ H0).
Qed.

Instance Rat_equiv_Transitive : Transitive Rat_equiv.
 red.
 intros x y z.
 unfold Rat_equiv.
 destruct x as [a b b_nonzero].
 destruct y as [c d d_nonzero].
 destruct z as [e f f_nonzero].
 simpl.
 intros.
 apply (f_equal (fun x => x * b)) in H0.
 rewrite <- mult_assoc in H0.
 rewrite (mult_comm f b) in H0.
 rewrite mult_assoc in H0.
 rewrite <- H in H0.
 rewrite (mult_comm a d) in H0.
 rewrite (mult_comm e d) in H0.
 rewrite <- (mult_assoc d a f) in H0.
 rewrite <- (mult_assoc d e b) in H0.
 apply (mult_cancel_l (a*f) (e*b) _ d_nonzero) in H0.
 assumption.
Qed.


Instance Rat_equiv_Equivalence : Equivalence Rat_equiv
 := { Equivalence_Reflexive := Rat_equiv_Reflexive
    ; Equivalence_Symmetric := Rat_equiv_Symmetric
    ; Equivalence_Transitive := Rat_equiv_Transitive
    }.

Notation "A %= B" := (Rat_equiv A B)  (at level 70).

Lemma nonzero_S : forall n, n <> 0 -> exists m, n = S m.
 destruct n ; intros.
 destruct H ; trivial.
 exists n ; trivial.
Qed.

Program Definition rat_plus (x y : Rat) :=
  match x with
  | mkRat a b b_nonzero =>
    match y with
    | mkRat c d d_nonzero =>
      mkRat (a*d + b*c) (b*d) _
    end
  end.
Next Obligation.
 destruct (nonzero_S _ b_nonzero).
 destruct (nonzero_S _ d_nonzero).
 rewrite H.
 rewrite H0.
 discriminate.
Qed.

Theorem rat_plus_comm : forall x y, rat_plus x y %= rat_plus y x.
 intros.
 destruct x as [a b b_nonzero].
 destruct y as [c d d_nonzero].
 unfold Rat_equiv.
 simpl.
 ring.
Qed.

Theorem rat_plus_assoc : forall x y z, rat_plus (rat_plus x y) z %= rat_plus x (rat_plus y z).
 intros.
 destruct x as [a b b_nonzero].
 destruct y as [c d d_nonzero].
 destruct z as [e f f_nonzero].
 unfold Rat_equiv.
 simpl.
 ring.
Qed.

