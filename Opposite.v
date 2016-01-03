Load Category.


Definition Op (C: Category) : Category.
  apply (Build_Category
           (Ob C)
           (fun x y => Hom C y x)
           (fun a => @Id C a)
           (fun a b c f g => @Comp C c b a g f)
        ).

  intros.
  apply idr.

  intros.
  apply idl.

  intros.
  symmetry.
  apply assoc.
Qed.