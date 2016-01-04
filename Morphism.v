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

Record Iso
           {C : Category}
           {a b : Ob C}
           (f : Hom _ a b) :=
  {
    inv_f:     Hom _ b a;
    inv_left:  Comp _ inv_f f = Id _;
    inv_right: Comp _ f inv_f = Id _
  }.

Theorem MonoEpi : forall {C : Category}
                         {a b : Ob C} 
                         (f : Hom _ a b),
                    Iso f -> Mono f /\ Epi f.
  intros.
  split.

  unfold Mono.
  intros.
  rewrite <- (idl _ _ _ g).
  rewrite <- (idl _ _ _ h).
  rewrite <- (inv_left f X).
  rewrite <- (assoc _ (inv_f f X) f g).
  rewrite <- (assoc _ (inv_f f X) f h).
  rewrite H.
  trivial.

  unfold Epi.
  intros.
  rewrite <- (idr _ _ _ g).
  rewrite <- (idr _ _ _ h).
  rewrite <- (inv_right f X).
  rewrite (assoc _ g f (inv_f f X)).
  rewrite (assoc _ h f (inv_f f X)).
  rewrite H.
  trivial.  
Qed.

Definition RetractOf {C : Category} a b :=
  exists (f: Hom _ a b)
         (g: Hom _ b a),
    Comp C f g = @Id _ a.

Record Terminal {C : Category} (a : Ob C) :=
  {
    morph_from:      forall b,
                       Hom _ b a;
    uniq_morph_from: forall {b} (g : Hom _ b a),
                       morph_from    b = g
  }.

Record Initial {C : Category} (a : Ob C) :=
  {
    morph_to:        forall b,
                       Hom _ a b;
    uniq_morph_to:   forall {b} (g : Hom _ a b),
                       morph_to    b = g
  }.

Record Isomorph {C : Category} (a b : Ob C) :=
  {
    iso_f:>     Hom _ a b;
    is_iso:>    Iso iso_f
  }.

Variable C : Category.
Variable a b : Ob C.
Variable iz : Isomorph a b.
Check inv_f.
(*Check inv_f iz iz.*)

Theorem UniqueInitial : forall {C : Category},
                        forall (a b : Ob C),
                          Initial a ->
                          Initial b ->
                          Isomorph a b.
  intros C a b Ia Ib.
  destruct Ia as [mab Hab], Ib as [mba Hba].
  assert (u := mab b).
  assert (v := mba a).
  refine (Build_Isomorph _ _ _ u _).
  refine (Build_Iso _ _ _ u v _ _).
      rewrite <- (Hba _ (Comp _ v u)).
      rewrite (Hba _ (Id _)).
      trivial.

      rewrite <- (Hab _ (Comp _ u v)).
      rewrite (Hab _ (Id _)).
      trivial.
Qed.