Load Category.

Definition Mono
           {C : Category}
           {a b : Ob C}
           (f : Hom _ a b)
  :=
  forall (c : Ob C),
    forall (g h : Hom _ b c),
      Comp _ f g = Comp _ f h -> g = h.

Definition Epi
           {C : Category}
           {b c: Ob C}
           (f : Hom _ b c)
  :=
  forall (a : Ob C),
    forall (g h : Hom _ a b),
      Comp _ g f = Comp _ h f -> g = h.

Definition Bi
           {C : Category}
           {a b : Ob C}
           (f : Hom _ a b) := Mono f /\ Epi f.

Definition InvOf
           {C : Category}
           {a b : Ob C}
           (f : Hom _ a b)
           (g : Hom _ b a)
  := Comp _ f g = Id _.

Definition Iso
           {C : Category}
           {a b : Ob C}
           (f : Hom _ a b)
  := exists g, InvOf f g /\ InvOf g f.

Theorem MonoEpi : forall {C : Category}
                         {a b : Ob C} 
                         (f : Hom _ a b),
                    Iso f -> Mono f /\ Epi f.
  intros.
  unfold Iso, InvOf in H.
  split.

  unfold Mono.
  intros.
  elim H.
  intros.
  destruct H1.
  rewrite <- (idl _ _ _ g), <- (idl _ _ _ h).
  rewrite <- H2.
  rewrite <- (assoc _ x f g), <- (assoc _ x f h).
  rewrite H0.
  trivial.

  unfold Epi.
  intros.
  elim H.
  intros.
  destruct H1.
  rewrite <- (idr _ _ _ g), <- (idr _ _ _ h).
  rewrite <- H1.
  rewrite (assoc _ g f x), (assoc _ h f x).
  rewrite H0.
  trivial.
Qed.

Definition RetractOf {C : Category} a b :=
  exists (f: Hom _ a b)
         (g: Hom _ b a),
    Comp C f g = @Id _ a.

Definition Initial {C : Category} (a : Ob C) :=
  forall (b : Ob C),
  exists (f : Hom _ a b),
  forall (g : Hom _ a b),
    f = g.

Definition Terminal {C : Category} (a : Ob C) :=
  forall (b : Ob C),
  exists (f : Hom _ b a),
  forall (g : Hom _ b a),
    f = g.

Definition Isomorph {C : Category} (a b : Ob C) :=
  exists (f : Hom _ a b), Iso f.

Theorem UniqueInitial :
  forall {C : Category},
  forall (a b : Ob C), Initial a -> Initial b -> Isomorph a b.
  intros C a b Ha Hb.
  unfold Initial in Ha, Hb.
  assert (Hab := Ha b).
  assert (Haa := Ha a).
  assert (Hba := Hb a).
  assert (Hbb := Hb b).
  elim Hab.
  intros u _.
  elim Hba.
  intros v _.
  elim Haa.
  intros ia H.
  elim Hbb.
  intros ib G.

  unfold Isomorph, Iso, InvOf.
  exists u, v.
  
  split.

  rewrite <- (H (Comp _ u v)), <- (H (Id _)).
  trivial.

  rewrite <- (G (Comp _ v u)), <- (G (Id _)).
  trivial.
Defined.