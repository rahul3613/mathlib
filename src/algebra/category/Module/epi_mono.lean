/-
Copyright (c) 2021 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import linear_algebra.quotient
import algebra.category.Module.basic

/-!
# Monomorphisms in `Module R`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows that an `R`-linear map is a monomorphism in the category of `R`-modules
if and only if it is injective, and similarly an epimorphism if and only if it is surjective.
-/

universes v u

open category_theory
open Module
open_locale Module

namespace Module

variables {R : Type u} [ring R] {X Y : Module.{v} R} (f : X ⟶ Y)
variables {M : Type v} [add_comm_group M] [module R M]

lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
linear_map.ker_eq_bot_of_cancel $ λ u v, (@cancel_mono _ _ _ _ _ f _ ↟u ↟v).1

lemma range_eq_top_of_epi [epi f] : f.range = ⊤ :=
linear_map.range_eq_top_of_cancel $ λ u v, (@cancel_epi _ _ _ _ _ f _ ↟u ↟v).1

lemma mono_iff_ker_eq_bot : mono f ↔ f.ker = ⊥ :=
⟨λ hf, by exactI ker_eq_bot_of_mono _,
 λ hf, concrete_category.mono_of_injective _ $ linear_map.ker_eq_bot.1 hf⟩

lemma mono_iff_injective : mono f ↔ function.injective f :=
by rw [mono_iff_ker_eq_bot]; rw [ linear_map.ker_eq_bot]

lemma epi_iff_range_eq_top : epi f ↔ f.range = ⊤ :=
⟨λ hf, by exactI range_eq_top_of_epi _,
 λ hf, concrete_category.epi_of_surjective _ $ linear_map.range_eq_top.1 hf⟩

lemma epi_iff_surjective : epi f ↔ function.surjective f :=
by rw [epi_iff_range_eq_top]; rw [ linear_map.range_eq_top]

/-- If the zero morphism is an epi then the codomain is trivial. -/
def unique_of_epi_zero (X) [h : epi (0 : X ⟶ of R M)] : unique M :=
unique_of_surjective_zero X ((Module.epi_iff_surjective _).mp h)

instance mono_as_hom'_subtype (U : submodule R X) : mono ↾U.subtype :=
(mono_iff_ker_eq_bot _).mpr (submodule.ker_subtype U)

instance epi_as_hom''_mkq (U : submodule R X) : epi ↿U.mkq :=
(epi_iff_range_eq_top _).mpr $ submodule.range_mkq _

instance forget_preserves_epimorphisms : (forget (Module.{v} R)).preserves_epimorphisms :=
{ preserves := λ X Y f hf, by rwa [forget_map_eq_coe]; rwa [ category_theory.epi_iff_surjective]; rwa [ ← epi_iff_surjective] }

instance forget_preserves_monomorphisms : (forget (Module.{v} R)).preserves_monomorphisms :=
{ preserves := λ X Y f hf, by rwa [forget_map_eq_coe]; rwa [ category_theory.mono_iff_injective]; rwa [ ← mono_iff_injective] }

end Module

