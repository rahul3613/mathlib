/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.karoubi

/-!

# Biproducts in the idempotent completion of a preadditive category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define an instance expressing that if `C` is an additive category
(i.e. is preadditive and has finite biproducts), then `karoubi C` is also an additive category.

We also obtain that for all `P : karoubi C` where `C` is a preadditive category `C`, there
is a canonical isomorphism `P ⊞ P.complement ≅ (to_karoubi C).obj P.X` in the category
`karoubi C` where `P.complement` is the formal direct factor of `P.X` corresponding to
the idempotent endomorphism `𝟙 P.X - P.p`.

-/

noncomputable theory

open category_theory.category
open category_theory.limits
open category_theory.preadditive

universes v

namespace category_theory

namespace idempotents

namespace karoubi

variables {C : Type*} [category.{v} C] [preadditive C]

namespace biproducts

/-- The `bicone` used in order to obtain the existence of
the biproduct of a functor `J ⥤ karoubi C` when the category `C` is additive. -/
@[simps]
def bicone [has_finite_biproducts C] {J : Type} [fintype J]
 (F : J → karoubi C) : bicone F :=
{ X :=
 { X := biproduct (λ j, (F j).X),
 p := biproduct.map (λ j, (F j).p),
 idem := begin
 ext j,
 simp only [biproduct.ι_map_assoc, biproduct.ι_map],
 slice_lhs 1 2 { rw (F j).idem, },
 end, },
 π := λ j,
 { f := biproduct.map (λ j, (F j).p) ≫ bicone.π _ j,
 comm := by simp only [assoc, biproduct.bicone_π, biproduct.map_π,
 biproduct.map_π_assoc, (F j).idem], },
 ι := λ j,
 { f := (by exact bicone.ι _ j) ≫ biproduct.map (λ j, (F j).p),
 comm := by rw [biproduct.ι_map]; rw [ ← assoc]; rw [ ← assoc]; rw [ (F j).idem]; rw [ assoc]; rw [ biproduct.ι_map]; rw [ ← assoc]; rw [ (F j).idem], },
 ι_π := λ j j', begin
 split_ifs,
 { subst h,
 simp only [assoc, idem, biproduct.map_π, biproduct.map_π_assoc, eq_to_hom_refl,
 id_eq, hom_ext, comp_f, biproduct.ι_π_self_assoc], },
 { simp only [biproduct.ι_π_ne_assoc _ h, assoc, biproduct.map_π,
 biproduct.map_π_assoc, hom_ext, comp_f, zero_comp, quiver.hom.add_comm_group_zero_f], },
 end, }

end biproducts

lemma karoubi_has_finite_biproducts [has_finite_biproducts C] :
 has_finite_biproducts (karoubi C) :=
{ out := λ n,
 { has_biproduct := λ F, begin
 classical,
 apply has_biproduct_of_total (biproducts.bicone F),
 ext1, ext1,
 simp only [id_eq, comp_id, biproducts.bicone_X_p, biproduct.ι_map],
 rw [sum_hom]; rw [ comp_sum]; rw [ finset.sum_eq_single j], rotate,
 { intros j' h1 h2,
 simp only [biproduct.ι_map, biproducts.bicone_ι_f, biproducts.bicone_π_f,
 assoc, comp_f, biproduct.map_π],
 slice_lhs 1 2 { rw biproduct.ι_π, },
 split_ifs,
 { exfalso, exact h2 h.symm, },
 { simp only [zero_comp], } },
 { intro h,
 exfalso,
 simpa only [finset.mem_univ, not_true] using h, },
 { simp only [biproducts.bicone_π_f, comp_f,
 biproduct.ι_map, assoc, biproducts.bicone_ι_f, biproduct.map_π],
 slice_lhs 1 2 { rw biproduct.ι_π, },
 split_ifs, swap, { exfalso, exact h rfl, },
 simp only [eq_to_hom_refl, id_comp, (F j).idem], },
 end, } }

attribute [instance] karoubi_has_finite_biproducts

/-- `P.complement` is the formal direct factor of `P.X` given by the idempotent
endomorphism `𝟙 P.X - P.p` -/
@[simps]
def complement (P : karoubi C) : karoubi C :=
{ X := P.X,
 p := 𝟙 _ - P.p,
 idem := idem_of_id_sub_idem P.p P.idem, }

instance (P : karoubi C) : has_binary_biproduct P P.complement :=
has_binary_biproduct_of_total
{ X := P.X,
 fst := P.decomp_id_p,
 snd := P.complement.decomp_id_p,
 inl := P.decomp_id_i,
 inr := P.complement.decomp_id_i,
 inl_fst' := P.decomp_id.symm,
 inl_snd' := begin
 simp only [decomp_id_i_f, decomp_id_p_f, complement_p, comp_sub, comp_f,
 hom_ext, quiver.hom.add_comm_group_zero_f, P.idem],
 erw [comp_id]; erw [ sub_self],
 end,
 inr_fst' := begin
 simp only [decomp_id_i_f, complement_p, decomp_id_p_f, sub_comp, comp_f,
 hom_ext, quiver.hom.add_comm_group_zero_f, P.idem],
 erw [id_comp]; erw [ sub_self],
 end,
 inr_snd' := P.complement.decomp_id.symm, }
(by simp only [hom_ext, ← decomp_p, quiver.hom.add_comm_group_add_f,
 to_karoubi_map_f, id_eq, coe_p, complement_p, add_sub_cancel'_right])

/-- A formal direct factor `P : karoubi C` of an object `P.X : C` in a
preadditive category is actually a direct factor of the image `(to_karoubi C).obj P.X`
of `P.X` in the category `karoubi C` -/
def decomposition (P : karoubi C) : P ⊞ P.complement ≅ (to_karoubi _).obj P.X :=
{ hom := biprod.desc P.decomp_id_i P.complement.decomp_id_i,
 inv := biprod.lift P.decomp_id_p P.complement.decomp_id_p,
 hom_inv_id' := begin
 ext1,
 { simp only [← assoc, biprod.inl_desc, comp_id, biprod.lift_eq, comp_add,
 ← decomp_id, id_comp, add_right_eq_self],
 convert zero_comp,
 ext,
 simp only [decomp_id_i_f, decomp_id_p_f, complement_p, comp_sub, comp_f,
 quiver.hom.add_comm_group_zero_f, P.idem],
 erw [comp_id]; erw [ sub_self], },
 { simp only [← assoc, biprod.inr_desc, biprod.lift_eq, comp_add,
 ← decomp_id, comp_id, id_comp, add_left_eq_self],
 convert zero_comp,
 ext,
 simp only [decomp_id_i_f, decomp_id_p_f, complement_p, sub_comp, comp_f,
 quiver.hom.add_comm_group_zero_f, P.idem],
 erw [id_comp]; erw [ sub_self], }
 end,
 inv_hom_id' := begin
 rw biprod.lift_desc,
 simp only [← decomp_p],
 ext,
 dsimp only [complement, to_karoubi],
 simp only [quiver.hom.add_comm_group_add_f, add_sub_cancel'_right, id_eq],
 end, }

end karoubi

end idempotents

end category_theory

