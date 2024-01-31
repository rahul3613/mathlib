/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.basic
import algebra.module.linear_map
import algebra.invertible
import algebra.algebra.basic

/-!
# Linear categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An `R`-linear category is a category in which `X ⟶ Y` is an `R`-module in such a way that
composition of morphisms is `R`-linear in both variables.

Note that sometimes in the literature a "linear category" is further required to be abelian.

## Implementation

Corresponding to the fact that we need to have an `add_comm_group X` structure in place
to talk about a `module R X` structure,
we need `preadditive C` as a prerequisite typeclass for `linear R C`.
This makes for longer signatures than would be ideal.

## Future work

It would be nice to have a usable framework of enriched categories in which this just became
a category enriched in `Module R`.

-/

universes w v u

open category_theory.limits
open linear_map

namespace category_theory

/-- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
    `R`-linear in both variables. -/
class linear (R : Type w) [semiring R] (C : Type u) [category.{v} C] [preadditive C] :=
(hom_module : Π X Y : C, module R (X ⟶ Y) . tactic.apply_instance)
(smul_comp' : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z),
  (r • f) ≫ g = r • (f ≫ g) . obviously)
(comp_smul' : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z),
  f ≫ (r • g) = r • (f ≫ g) . obviously)

attribute [instance] linear.hom_module
restate_axiom linear.smul_comp'
restate_axiom linear.comp_smul'
attribute [simp,reassoc] linear.smul_comp
attribute [reassoc, simp] linear.comp_smul -- (the linter doesn't like `simp` on the `_assoc` lemma)

end category_theory

open category_theory

namespace category_theory.linear

variables {C : Type u} [category.{v} C] [preadditive C]

instance preadditive_nat_linear : linear ℕ C :=
{ smul_comp' := λ X Y Z r f g, (preadditive.right_comp X g).map_nsmul f r,
  comp_smul' := λ X Y Z f r g, (preadditive.left_comp Z f).map_nsmul g r, }

instance preadditive_int_linear : linear ℤ C :=
{ smul_comp' := λ X Y Z r f g, (preadditive.right_comp X g).map_zsmul f r,
  comp_smul' := λ X Y Z f r g, (preadditive.left_comp Z f).map_zsmul g r, }

section End

variables {R : Type w}

instance [semiring R] [linear R C] (X : C) : module R (End X) :=
by { dsimp [End], apply_instance, }

instance [comm_semiring R] [linear R C] (X : C) : algebra R (End X) :=
algebra.of_module (λ r f g, comp_smul _ _ _ _ _ _) (λ r f g, smul_comp _ _ _ _ _ _)

end End

section
variables {R : Type w} [semiring R] [linear R C]

section induced_category
universes u'
variables {C} {D : Type u'} (F : D → C)

instance induced_category : linear.{w v} R (induced_category C F) :=
{ hom_module := λ X Y, @linear.hom_module R _ C _ _ _ (F X) (F Y),
  smul_comp' := λ P Q R f f' g, smul_comp' _ _ _ _ _ _,
  comp_smul' := λ P Q R f g g', comp_smul' _ _ _ _ _ _, }

end induced_category

instance full_subcategory (Z : C → Prop) : linear.{w v} R (full_subcategory Z) :=
{ hom_module := λ X Y, @linear.hom_module R _ C _ _ _ X.obj Y.obj,
  smul_comp' := λ P Q R f f' g, smul_comp' _ _ _ _ _ _,
  comp_smul' := λ P Q R f g g', comp_smul' _ _ _ _ _ _, }

variables (R)

/-- Composition by a fixed left argument as an `R`-linear map. -/
@[simps]
def left_comp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →ₗ[R] (X ⟶ Z) :=
{ to_fun := λ g, f ≫ g,
  map_add' := by simp,
  map_smul' := by simp, }

/-- Composition by a fixed right argument as an `R`-linear map. -/
@[simps]
def right_comp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) →ₗ[R] (X ⟶ Z) :=
{ to_fun := λ f, f ≫ g,
  map_add' := by simp,
  map_smul' := by simp, }

instance {X Y : C} (f : X ⟶ Y) [epi f] (r : R) [invertible r] : epi (r • f) :=
⟨λ R g g' H, begin
  rw [smul_comp, smul_comp, ←comp_smul, ←comp_smul, cancel_epi] at H,
  simpa [smul_smul] using congr_arg (λ f, ⅟r • f) H,
end⟩

instance {X Y : C} (f : X ⟶ Y) [mono f] (r : R) [invertible r] : mono (r • f) :=
⟨λ R g g' H, begin
  rw [comp_smul, comp_smul, ←smul_comp, ←smul_comp, cancel_mono] at H,
  simpa [smul_smul] using congr_arg (λ f, ⅟r • f) H,
end⟩

/-- Given isomorphic objects `X ≅ Y, W ≅ Z` in a `k`-linear category, we have a `k`-linear
isomorphism between `Hom(X, W)` and `Hom(Y, Z).` -/
def hom_congr (k : Type*) {C : Type*} [category C] [semiring k]
  [preadditive C] [linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) :
  (X ⟶ W) ≃ₗ[k] (Y ⟶ Z) :=
{ inv_fun := (left_comp k W f₁.hom).comp (right_comp k Y f₂.symm.hom),
  left_inv := λ x, by simp only [iso.symm_hom, linear_map.to_fun_eq_coe, linear_map.coe_comp,
    function.comp_app, left_comp_apply, right_comp_apply, category.assoc, iso.hom_inv_id,
    category.comp_id, iso.hom_inv_id_assoc],
  right_inv := λ x, by simp only [iso.symm_hom, linear_map.coe_comp, function.comp_app,
    right_comp_apply, left_comp_apply, linear_map.to_fun_eq_coe, iso.inv_hom_id_assoc,
    category.assoc, iso.inv_hom_id, category.comp_id],
  ..(right_comp k Y f₂.hom).comp (left_comp k W f₁.symm.hom) }

lemma hom_congr_apply (k : Type*) {C : Type*} [category C] [semiring k]
  [preadditive C] [linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : X ⟶ W) :
  hom_congr k f₁ f₂ f = (f₁.inv ≫ f) ≫ f₂.hom := rfl

lemma hom_congr_symm_apply (k : Type*) {C : Type*} [category C] [semiring k]
  [preadditive C] [linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : Y ⟶ Z) :
  (hom_congr k f₁ f₂).symm f = f₁.hom ≫ f ≫ f₂.inv := rfl

end

section
variables {S : Type w} [comm_semiring S] [linear S C]

/-- Composition as a bilinear map. -/
@[simps]
def comp (X Y Z : C) : (X ⟶ Y) →ₗ[S] ((Y ⟶ Z) →ₗ[S] (X ⟶ Z)) :=
{ to_fun := λ f, left_comp S Z f,
  map_add' := by { intros, ext, simp, },
  map_smul' := by { intros, ext, simp, }, }

end

end category_theory.linear
