-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

set_option pp.universes true

open smt_tactic

def pointwise_attribute : user_attribute := {
  name := `pointwise,
  descr := "A lemma that proves things are equal using the fact they are pointwise equal."
}

run_command attribute.register `pointwise_attribute

open tactic

/- Try to apply one of the given lemas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic unit
| []      := failed
| (c::cs) := (mk_const c >>= fapply) <|> any_apply cs

meta def smt   : tactic unit := using_smt $ intros >> add_lemmas_from_facts >> try ematch >> try simp

meta def pointwise (and_then : tactic unit) : tactic unit :=
do cs ← attribute.get_instances `pointwise,
   try (do any_apply cs, and_then)

meta def blast : tactic unit := smt >> pointwise (repeat_at_most 2 blast) -- pointwise equality of functors creates two goals

notation `♮` := by abstract { blast }

@[pointwise] lemma {u v} pair_equality {α : Type u} {β : Type v} { X: α × β }: (X^.fst, X^.snd) = X := begin induction X, blast end
@[pointwise] lemma {u v} pair_equality_1 {α : Type u} {β : Type v} { X: α × β } { A : α } ( p : A = X^.fst ) : (A, X^.snd) = X := begin induction X, blast end
@[pointwise] lemma {u v} pair_equality_2 {α : Type u} {β : Type v} { X: α × β } { B : β } ( p : B = X^.snd ) : (X^.fst, B) = X := begin induction X, blast end
-- But let's not use this last one, as it introduces two goals.
-- @[pointwise] lemma {u v} pair_equality_3 {α : Type u} {β : Type v} { X: α × β } { A : α } ( p : A = X^.fst ) { B : β } ( p : B = X^.snd ) : (A, B) = X := begin induction X, blast end
attribute [pointwise] subtype.eq

def {u} auto_cast {α β : Type u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Type u} (a : α) : @auto_cast α α ♮ a = a := ♮
notation `⟦` p `⟧` := @auto_cast _ _ ♮ p