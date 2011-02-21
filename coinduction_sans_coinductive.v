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
       F_fmap carrier' _ (mkNu carrier' coalg') (coalg' point')
    end.

End nu.

Definition prod_fmap X A B (f : A->B) (p:X*A) : X*B
  := let (x,y) := p in (x,f y).

Definition natsNu := unfold (prod nat) nat 
   (fun n =>  (n, S n)) 0.

Definition nats := NuCoalg _ (prod_fmap nat) natsNu.

Fixpoint approx A (nu : Nu (prod A)) (n:nat) : list A :=
  match n with
  | O => nil
  | S n' => let (x,nu') := NuCoalg _ (prod_fmap A) nu in
             x :: approx A nu' n'
  end.

Eval simpl in approx _ natsNu 10.