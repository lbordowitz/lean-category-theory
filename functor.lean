-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category

open tqft.categories

namespace tqft.categories.functor

universe variables u1 v1 u2 v2


structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C^.Obj),
    onMorphisms (C^.identity X) = D^.identity (onObjects X))
  (functoriality : ∀ { X Y Z : C^.Obj } (f : C^.Hom X Y) (g : C^.Hom Y Z),
    onMorphisms (C^.compose f g) = D^.compose (onMorphisms f) (onMorphisms g))

structure ObjectifiedFunctor {C D : Category} (obj: C^.Obj → D^.Obj) := (mk := Functor.mk obj)

structure ObjectishFunctor {C D : Category} (obj: C^.Obj → D^.Obj) := 
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (obj X) (obj Y))
  (identities : ∀ (X : C^.Obj),
    onMorphisms (C^.identity X) = D^.identity (obj X))
  (functoriality : ∀ { X Y Z : C^.Obj } (f : C^.Hom X Y) (g : C^.Hom Y Z),
    onMorphisms (C^.compose f g) = D^.compose (onMorphisms f) (onMorphisms g))

definition ob_to_fun {C D : Category} { obj: C^.Obj → D^.Obj } (OF : ObjectishFunctor obj) : Functor C D := Functor.mk
  obj
  (λ X Y, OF^.onMorphisms)
  (λ X, OF^.identities X)
  (λ X Y Z f g, OF^.functoriality f g)

-- print coercions
--attribute ob_to_fun [coercion]

attribute [simp] Functor.identities
attribute [simp] Functor.functoriality

attribute [simp] ObjectishFunctor.identities
attribute [simp] ObjectishFunctor.functoriality

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
instance Functor_to_onObjects { C D : Category }: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C^.Obj -> D^.Obj,
  coe := Functor.onObjects }

-- TODO get Functor_to_onMorphisms working

/-
-- Unfortunately we haven't been able to set up similar notation for morphisms.
-- Instead we define notation so that `F <$> f` denotes the functor `F` applied to the morphism `f`.
-- One can still write out `onMorphisms F f` when needed, or even the very verbose `@Functor.onMorphisms C D F X Y f`.
--namespace notations
  -- Lean complains about the use of local variables in
  -- notation. There must be a way around that.
  infix `<$>` :50 := λ {C : Category} {D : Category}
                       (F : Functor C D) {X Y : C^.Obj} (f : C^.Hom X Y),
                       Functor.onMorphisms F f
end notations

open notations
-/

-- This defines a coercion allowing us to write `F f` for `onMorphisms F f`
-- but sadly it doesn't work if to_onObjects is already in scope.
--instance Functor_to_onMorphisms { C D : Category } : has_coe_to_fun (Functor C D) :=
--{ F   := λ f, Π ⦃X Y : C^.Obj⦄, C^.Hom X Y → D^.Hom (f X) (f Y), -- contrary to usual use, `f` here denotes the Functor.
--  coe := Functor.onMorphisms }

@[reducible] definition IdentityFunctor ( C: Category ) : Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f,
  identities    := take x, rfl,
  functoriality := take X Y Z, take f g, rfl
}

@[reducible] definition FunctorComposition { C D E : Category } ( F : Functor C D ) ( G : Functor D E ) : Functor C E :=
{
  onObjects     := λ X, G (F X),
  onMorphisms   := λ _ _ f, G^.onMorphisms (F^.onMorphisms f),
  identities    := take X, /-calc
                G^.onMorphisms (F^.onMorphisms (C^.identity X)) = G^.onMorphisms (D^.identity (F X)) : by rw [F^.identities X]
                                                            ... = E^.identity (G (F X)) : by rw [G^.identities (F X)],-/ 
                           by rw [F^.identities X, G^.identities (F X)],
  functoriality := take X Y Z, take f g, /-calc
    G^.onMorphisms (F^.onMorphisms (C^.compose f g)) = G^.onMorphisms (D^.compose (F^.onMorphisms f) (F^.onMorphisms g)) : by rw [F^.functoriality f g]
                                                 ... = E^.compose (G^.onMorphisms (F^.onMorphisms f)) (G^.onMorphisms (F^.onMorphisms g)) : -/
                                        by rw [F^.functoriality f g, G^.functoriality (F^.onMorphisms f) (F^.onMorphisms g)]
}

-- We'll want to be able to prove that two functors are equal if they are equal on objects and on morphisms.
-- Implementation warning:
-- When using `apply Functors_pointwise_equal`, you might expect that Lean will create two goals,
--   one for `objectWitness`, and one for `morphismWitness`.
--   However, because `morphismWitness` depends on `objectWitness`, it will actually only create the goal
--   for `morphismWitness`, leaving the `objectWitness` goal somehow "implicit" and likely unprovable.
--   See https://groups.google.com/d/msg/lean-user/bhStu87PjiI/vqsyr9ZABAAJ for details.
-- If you run into this problem, use `fapply Functors_pointwise_equal` instead.


def transportHom
 {C D : Category} {F G : Functor C D}
 (objectWitness : ∀ X : C^.Obj, F^.onObjects X = G^.onObjects X )
 {X Y : C^.Obj}
 (h : D^.Hom (F^.onObjects X) (F^.onObjects Y)) : D^.Hom (G^.onObjects X) (G^.onObjects Y) :=
eq.rec_on (objectWitness X) (eq.rec_on (objectWitness Y) h)

infix `►`:60 := transportHom

@[pointwise] lemma Functors_pointwise_equal
  { C D : Category }
  { obj : C^.Obj → D^.Obj}
  { F G : ObjectishFunctor obj }
  ( morphismWitness : ∀ X Y : C^.Obj, ∀ f : C^.Hom X Y, F^.onMorphisms f = G^.onMorphisms f) : F = G :=
begin
  induction F with F_onMorphisms,
  induction G with G_onMorphisms,
  assert h_morphisms : @F_onMorphisms = @G_onMorphisms, 
  apply funext, intro X, apply funext, intro Y, apply funext, intro f,
  exact morphismWitness X Y f,
  subst h_morphisms
end

def fun_to_obj {C D : Category} (F : Functor C D) : ObjectishFunctor F^.onObjects := ObjectishFunctor.mk
  (λ X Y, F^.onMorphisms)
  (λ X, F^.identities X)
  (λ X Y Z f g, F^.functoriality f g)

-- TODO This is using ObjectishFunctor, but not Functor proper. need to coerce/convert.

lemma FunctorComposition_left_identity { C D : Category } ( F : Functor C D ) :
  FunctorComposition (IdentityFunctor C) F = F := Functors_pointwise_equal (take X Y : C^.Obj, take f : C^.Hom X Y, 
    calc
      (fun_to_obj (FunctorComposition (IdentityFunctor C) F ))^.onMorphisms f = (fun_to_obj F)^.onMorphisms f : rfl)

lemma FunctorComposition_right_identity { C D : Category } ( F : Functor C D ) :
  FunctorComposition F (IdentityFunctor D) = F := Functors_pointwise_equal (take X Y : C^.Obj, take f : C^.Hom X Y, 
    calc
      (FunctorComposition F (IdentityFunctor C) )^.onMorphisms f = F^.onMorphisms f : rfl

lemma FunctorComposition_associative { B C D E : Category } ( F : Functor B C ) ( G : Functor C D ) ( H : Functor D E ) :
  FunctorComposition (FunctorComposition F G) H = FunctorComposition F (FunctorComposition G H) := _

end tqft.categories.functor
