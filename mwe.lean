set_option pp.implicit true

open smt_tactic
meta def blast : tactic unit := using_smt $ intros

def {u} auto_cast {α β : Type u} {h : α = β} (a : α) := cast h a
notation `⟦` p `⟧` := @auto_cast _ _ (by blast) p

structure Category :=
  (Obj : Type)
  (Hom : Obj → Obj → Type)
  (identity : Π (X : Obj), Hom X X)
  (compose  : Π {X Y Z : Obj} (f : Hom X Y) (g : Hom Y Z), Hom X Z)
  
def ProductCategory (C D : Category) : Category :=
  { Obj      := C^.Obj × D^.Obj
  , Hom      := λ (X Y : C^.Obj × D^.Obj), C^.Hom X^.fst Y^.fst × D^.Hom X^.snd Y^.snd
  , identity := λ X, (C^.identity X^.fst, D^.identity X^.snd)
  , compose  := λ _ _ _ f g, (C^.compose f^.fst g^.fst, D^.compose f^.snd g^.snd) }

structure Functor (C D : Category) :=
  (onObj : C^.Obj → D^.Obj)
  (onMor : Π {X Y : C^.Obj}, C^.Hom X Y → D^.Hom (onObj X) (onObj Y))
 
structure PreMonoidalCategory :=
  (carrier : Category)
  (tensor  : Functor (ProductCategory carrier carrier) carrier)

notation X `⊗` Y := PreMonoidalCategory.tensor^.onObj (X, Y)
  
structure MonoidalCategory extends PreMonoidalCategory :=
  (associator : Π (X Y Z : carrier^.Obj),
     carrier^.Hom (tensor^.onObj (tensor^.onObj (X, Y), Z))
                  (tensor^.onObj (X, tensor^.onObj (Y, Z))))

  (pentagon : Π (X Y Z W : carrier^.Obj),
     tensor^.onMor (associator X Y Z, carrier^.identity W) =
     tensor^.onMor (associator X Y Z, carrier^.identity W))
