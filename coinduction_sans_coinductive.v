(* 
  I've always felt that coinductive, broken as it is in
  coq, was unnecessary and that it ought to be able to
  be modeled (in all forms, not just the easy ones) using
  basic structures.

  This is a short development which explores this, modeling
  coinductive as the sum of all coalgebras over a functor.
  At the end I implement the usual stream coinductive
  using this technique.  It remains to be seen whether this 
  small development (section nu) is complete -- whether we 
  can do everything we could using coq's coinductive using
  this.  And I don't think we can prove that from within 
  coq, because its idea of coinductive is not first-class.
*)

Set Implicit Arguments.
Require Import List.

Section nu.

Variable F : Type -> Type.
Hypothesis F_fmap : forall a b, (a -> b) -> F a -> F b.

Definition Coalg A := A -> F A.

Record Nu := mkNu {
  carrier : Type;
  coalg : Coalg carrier;
  point : carrier
}.

Definition unfold : forall B, (B -> F B) -> B -> Nu := mkNu.

Definition NuCoalg : Coalg Nu := fun nu => 
    match nu with
    | mkNu carrier' coalg' point' => 
       F_fmap (mkNu coalg') (coalg' point')
    end.

End nu.

(* Modeling stream A as Nu (prod A) *)

Section stream.

Variable A : Type.

Definition prod_fmap X Y (f : X->Y) (p:A*X) : A*Y
  := let (a,x) := p in (a,f x).

Definition stream := Nu (prod A).

Definition project := NuCoalg prod_fmap.

(* Extract a finite prefix of a stream *)
Fixpoint approx (s : stream) (n:nat) : list A :=
  match n with
  | O => nil
  | S n' => let (x,s') := project s in
             x :: approx s' n'
  end.


(* Coq Coinductive stream *)
CoInductive stream' :=
| cons : A -> stream' -> stream'.

(* and it's bullshit unfolding lemma *)
Definition frob_stream' s := 
  match s with cons x xs => cons x xs end.

Lemma frob_stream'_defn : forall s, s = frob_stream' s.
 destruct s ; reflexivity.
Qed.

(* Equivalence of coq coinductive streams to 
   final coalgebra streams *)

Definition stream'_to_stream : stream' -> stream :=
  unfold _ (fun s =>
    match s with
    | cons x s' => (x, s')
    end).

CoFixpoint stream_to_stream' (s : stream) :=
  let (x,s') := project s in
  cons x (stream_to_stream' s').

(* Bisimulation type for proving equivalence of
   Coq coinductive streams *)
CoInductive stream'_eq : stream' -> stream' -> Prop :=
| cons_eq : forall s t x, stream'_eq s t -> stream'_eq (cons x s) (cons x t).

Theorem inverses1 : forall s, stream'_eq s (stream_to_stream' (stream'_to_stream s)).
 cofix.
 destruct s.
 rewrite frob_stream'_defn ; simpl.
 fold (unfold (prod A)).
 fold stream'_to_stream.
 apply cons_eq.
 auto.
Qed.

(* Todo: prove the other inverse using a final
   coalgebra bisimulation type (hope that is expressible)
*)

End stream.

Definition nats := unfold _ (fun n =>  (n, S n)) 0.

Eval simpl in approx nats 10.