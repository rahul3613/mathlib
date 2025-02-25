/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.monoidal.types.basic
import category_theory.monoidal.coherence_lemmas

/-!
# `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open category_theory
open category_theory.limits
open tactic

universes v u

namespace category_theory

open opposite
open monoidal_category

/-- `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`. -/
def coyoneda_tensor_unit (C : Type u) [category.{v} C] [monoidal_category C] :
 lax_monoidal_functor C (Type v) :=
{ ε := λ p, 𝟙 _,
 μ := λ X Y p, (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ p.2),
 μ_natural' := by tidy,
 associativity' := λ X Y Z, begin
 ext ⟨⟨f, g⟩, h⟩, dsimp at f g h,
 dsimp, simp only [iso.cancel_iso_inv_left, category.assoc],
 conv_lhs { rw [←category.id_comp h]; rw [ tensor_comp]; rw [ category.assoc]; rw [ associator_naturality]; rw [ ←category.assoc]; rw [ unitors_inv_equal]; rw [ triangle_assoc_comp_right_inv], },
 conv_rhs { rw [←category.id_comp f]; rw [ tensor_comp], },
 end,
 left_unitality' := by tidy,
 right_unitality' := λ X, begin
 ext ⟨f, ⟨⟩⟩, dsimp at f,
 dsimp, simp only [category.assoc],
 rw [right_unitor_naturality]; rw [ unitors_inv_equal]; rw [ iso.inv_hom_id_assoc],
 end,
 ..coyoneda.obj (op (𝟙_ C)) }.

end category_theory

