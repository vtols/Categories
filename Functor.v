Load Category.

Record Functor (C D : Category) :=
    {
      (* Functor F maps objects and
         morphisms in first category
         to objects and morphisms in
         other category *)

      (* Here this map is 
         separated in two *)
      
      (* First maps object of C to
         object of D *)
      FOb:   Ob C -> Ob D;

      (* Second maps morphism
           f  in Hom(  a ,   b )
         to morphism
         F(f) in Hom(F(a), F(b)) *)
      FHom:  forall {a b : Ob C},
               Hom _ a b -> Hom _ (FOb a) (FOb b);

      (* Functor maps identity
         morphism in this way
         F(Id_a) = Id_F(a) *)
      FId:   forall {a : Ob C},
               FHom (@Id _ a) = @Id _ (FOb a);
      FComp: forall {a b c : Ob C}
               (f: Hom _ a b)
               (g: Hom _ b c),
               FHom (Comp _ f g) = Comp _ (FHom f) (FHom g)
    }.

(*
  Check FComp.

  Variable C D : Category.
  Variable F : Functor C D.
  Variable a : Ob C.
  Check @Id.
  Check @Id C a.
  Check FHom C D F (@Id C a).
*)