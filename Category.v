Record Category :=
    {
      (* Basic elements of every category
         are obects and arrows (morphisms)
         between them. *)

      (* So we begin with Ob as set of objects *)
      Ob:     Type;
    
      (* Then Hom as family of sets of arrows
         parametrized by two objects –
         the begin and the end of an arrow

         For example for objects a and b
         Hom(a,b) is the set of arrows
         that starts at a and ends at b *)
      Hom:    Ob -> Ob -> Type;
      
      (* Also there are some propositions about
         category *)

      (* For every object a there is
         identity morphism id in Hom(a,a) *)
      Id:     forall {a},
                Hom a a;

      (* We can compose arrow. 
         Suppose we have objects a, b, c.
         And two arrows f in Hom(a,b) and
         g in Hom(b,c).
         So, end of f is the start of g.
         Such arrows are composable.
         By composing them we get some
         new arrow h, h in Hom(a,c)
         *)
      Comp:   forall {a b c},
                Hom a b -> Hom b c -> Hom a c;
      
      (* Composing any arrow f in Hom(a,b)
         with Id  arrow we always get f arrow.
         
         Though, in Hom(a,a) can be
         other arrows than Id. *)
      idl:    forall a b
                     (f: Hom a b),
                Comp Id f = f;

      idr:    forall a b
                     (f: Hom a b),
                Comp f Id = f;

      (* Associativity rule for composition *)
      assoc:  forall {a b c d}
                     (f: Hom a b)
                     (g: Hom b c)
                     (h: Hom c d),
                Comp f (Comp g h) = Comp (Comp f g) h
    }.

(*
  Definition OpHom (C : Category) x y := Hom C y x.
  Variable C : Category.
  Variable x y : Ob C.
  Check OpHom C x y.
  Check Build_Category (Ob C) (OpHom C). *)