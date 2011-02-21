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

  To prove equivalence of stream below to coq's coinductive
  stream, it appears we need some sort of fixpoint lemma,
  so that we can see the recursion within unfold (which
  is a non-recursive definition here, so it may be
  nontrivial).  It's likely that this lemma is needed
  to do other interesting stuff with this development as
  well.
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

End stream.

Definition nats := unfold _ (fun n =>  (n, S n)) 0.

Eval simpl in approx nats 10.