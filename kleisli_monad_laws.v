Set Implicit Arguments.

Section MonadLaws.

Hypothesis extensionality : forall A B (f g : A -> B), (forall x, f x = g x) -> f = g.

Variable M : Type -> Type.
Variable unit : forall a, a -> M a.
Variable bind : forall a b, (a -> M b) -> (M a -> M b).

Definition flipbind a b (x:M a) (f:a->M b) := bind f x.

Infix ">>=" := flipbind (at level 50, left associativity).

Definition law1 := forall a (x:M a), x >>= (unit (a:=_)) = x.
Definition law2 := forall a b (x:a) (f : a -> M b), unit x >>= f = f x.
Definition law3 := forall a b c (x:M a) (f : a -> M b) (g : b -> M c), 
                     (x >>= f) >>= g = x >>= (fun y => f y >>= g).


Definition kleisli a b c (f : a -> M b) (g : b -> M c) : a -> M c := fun x => f x >>= g.

Infix ">=>" := kleisli (at level 50, left associativity).

Definition law1' := forall a b (f : a -> M b), f >=> (unit (a:=_)) = f.
Definition law2' := forall a b (f : a -> M b), (unit (a:=_)) >=> f = f.
Definition law3' := forall a b c d (f : a -> M b) (g : b -> M c) (h : c -> M d), (f >=> g) >=> h = f >=> (g >=> h).


Theorem law1_kleisli : law1 <-> law1'.
 unfold law1 ; unfold law1'.
 split ; intros.
 unfold kleisli.
 apply extensionality.
 intros.
 apply H.

 pose (H (M a) _ (fun x => x)).
 unfold kleisli in e.
 apply (f_equal (fun f => f x) e).
Qed.

Theorem law2_kleisli : law2 <-> law2'.
 unfold law2 ; unfold law2'.
 split ; intros.
 unfold kleisli.
 apply extensionality.
 intros.
 apply H.

 pose (H _  _ f).
 unfold kleisli in e.
 apply (f_equal (fun f => f x) e).
Qed.

Theorem law3_kleisli : law3 <-> law3'.
 unfold law3 ; unfold law3'.
 split ; intros.
 unfold kleisli.
 apply extensionality.
 intros.
 apply H.

 unfold kleisli in H.
 pose (H _ _ _ _ (fun x => x) f g).
 simpl in e.
 apply (f_equal (fun f => f x) e).
Qed.

End MonadLaws.