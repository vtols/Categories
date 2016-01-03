Load Functor.

Definition hom_pairing {C D : Category} a b :=
  prod (Hom C (fst a) (fst b)) (Hom D (snd a) (snd b)).

Definition id_pairing {C D : Category} (a : Ob C * Ob D) :=
  (@Id _ (fst a), @Id _ (snd a)).

Definition comp_pairing
           {C D : Category}
           (a b c: Ob C * Ob D) 
           (f : hom_pairing a b)
           (g : hom_pairing b c) :=
  (Comp _ (fst f) (fst g), Comp _ (snd f) (snd g)).
  
Variable C D : Category.
Variable a : Ob C.
Variable b : Ob D.
Check @Id _ a.
Check hom_pairing (a, b) (a, b).
Check Build_Category ((Ob C) * (Ob D)) (hom_pairing).
Check hom_pairing.
Check id_pairing.
Check snd.


Definition Product (C D : Category) : Category.
  apply (Build_Category
           ((Ob C) * (Ob D))
           (hom_pairing)
           (fun a => id_pairing a)
           (fun a b c f g => comp_pairing a b c f g)
        ).
  
  unfold comp_pairing, id_pairing, hom_pairing.
  intros.
  simpl.
  rewrite (idl C), (idl D).
  simpl.
  symmetry.
  apply surjective_pairing.

  unfold comp_pairing, id_pairing, hom_pairing.
  intros.
  simpl.
  rewrite (idr C), (idr D).
  symmetry.
  apply surjective_pairing.

  unfold comp_pairing, id_pairing, hom_pairing.
  intros.
  simpl.
  rewrite <- (assoc C (fst f) (fst g) (fst h)),
             (assoc D (snd f) (snd g) (snd h)).
  trivial.
Defined.

Definition PiFst : Functor (Product C D) C.
  apply (Build_Functor _ _ _
                       (fun a b (f: Hom (Product C D) a b) => fst f)).
  simpl.
  trivial.

  simpl.
  trivial.
Defined.

Definition PiSnd : Functor (Product C D) D.
  apply (Build_Functor _ _ _
                       (fun a b (f: Hom (Product C D) a b) => snd f)).
  simpl.
  trivial.

  simpl.
  trivial.
Defined.