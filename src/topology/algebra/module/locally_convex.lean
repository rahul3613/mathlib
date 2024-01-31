/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.convex.topology
/-!
# Locally convex topological modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A `locally_convex_space` is a topological semimodule over an ordered semiring in which any point
admits a neighborhood basis made of convex sets, or equivalently, in which convex neighborhoods of
a point form a neighborhood basis at that point.

In a module, this is equivalent to `0` satisfying such properties.

## Main results

- `locally_convex_space_iff_zero` : in a module, local convexity at zero gives
 local convexity everywhere
- `seminorm.locally_convex_space` : a topology generated by a family of seminorms is locally convex
- `normed_space.locally_convex_space` : a normed space is locally convex

## TODO

- define a structure `locally_convex_filter_basis`, extending `module_filter_basis`, for filter
 bases generating a locally convex topology

-/

open topological_space filter set

open_locale topology pointwise

section semimodule

/-- A `locally_convex_space` is a topological semimodule over an ordered semiring in which convex
neighborhoods of a point form a neighborhood basis at that point. -/
class locally_convex_space (𝕜 E : Type*) [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
 [topological_space E] : Prop :=
(convex_basis : ∀ x : E, (𝓝 x).has_basis (λ (s : set E), s ∈ 𝓝 x ∧ convex 𝕜 s) id)

variables (𝕜 E : Type*) [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] [topological_space E]

lemma locally_convex_space_iff :
 locally_convex_space 𝕜 E ↔
 ∀ x : E, (𝓝 x).has_basis (λ (s : set E), s ∈ 𝓝 x ∧ convex 𝕜 s) id :=
⟨@locally_convex_space.convex_basis _ _ _ _ _ _, locally_convex_space.mk⟩

lemma locally_convex_space.of_bases {ι : Type*} (b : E → ι → set E) (p : E → ι → Prop)
 (hbasis : ∀ x : E, (𝓝 x).has_basis (p x) (b x)) (hconvex : ∀ x i, p x i → convex 𝕜 (b x i)) :
 locally_convex_space 𝕜 E :=
⟨λ x, (hbasis x).to_has_basis
 (λ i hi, ⟨b x i, ⟨⟨(hbasis x).mem_of_mem hi, hconvex x i hi⟩, le_refl (b x i)⟩⟩)
 (λ s hs, ⟨(hbasis x).index s hs.1,
 ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩)⟩

lemma locally_convex_space.convex_basis_zero [locally_convex_space 𝕜 E] :
 (𝓝 0 : filter E).has_basis (λ s, s ∈ (𝓝 0 : filter E) ∧ convex 𝕜 s) id :=
locally_convex_space.convex_basis 0

lemma locally_convex_space_iff_exists_convex_subset :
 locally_convex_space 𝕜 E ↔ ∀ x : E, ∀ U ∈ 𝓝 x, ∃ S ∈ 𝓝 x, convex 𝕜 S ∧ S ⊆ U :=
(locally_convex_space_iff 𝕜 E).trans (forall_congr $ λ x, has_basis_self)

end semimodule

section module

variables (𝕜 E : Type*) [ordered_semiring 𝕜] [add_comm_group E] [module 𝕜 E] [topological_space E]
 [topological_add_group E]

lemma locally_convex_space.of_basis_zero {ι : Type*} (b : ι → set E) (p : ι → Prop)
 (hbasis : (𝓝 0).has_basis p b) (hconvex : ∀ i, p i → convex 𝕜 (b i)) :
 locally_convex_space 𝕜 E :=
begin
 refine locally_convex_space.of_bases 𝕜 E (λ (x : E) (i : ι), ((+) x) '' b i) (λ _, p) (λ x, _)
 (λ x i hi, (hconvex i hi).translate x),
 rw ← map_add_left_nhds_zero,
 exact hbasis.map _
end

lemma locally_convex_space_iff_zero :
 locally_convex_space 𝕜 E ↔
 (𝓝 0 : filter E).has_basis (λ (s : set E), s ∈ (𝓝 0 : filter E) ∧ convex 𝕜 s) id :=
⟨λ h, @locally_convex_space.convex_basis _ _ _ _ _ _ h 0,
 λ h, locally_convex_space.of_basis_zero 𝕜 E _ _ h (λ s, and.right)⟩

lemma locally_convex_space_iff_exists_convex_subset_zero :
 locally_convex_space 𝕜 E ↔
 ∀ U ∈ (𝓝 0 : filter E), ∃ S ∈ (𝓝 0 : filter E), convex 𝕜 S ∧ S ⊆ U :=
(locally_convex_space_iff_zero 𝕜 E).trans has_basis_self

-- see Note [lower instance priority]
@[priority 100] instance locally_convex_space.to_locally_connected_space [module ℝ E]
 [has_continuous_smul ℝ E] [locally_convex_space ℝ E] :
 locally_connected_space E :=
locally_connected_space_of_connected_bases _ _
 (λ x, @locally_convex_space.convex_basis ℝ _ _ _ _ _ _ x)
 (λ x s hs, hs.2.is_preconnected)

end module

section linear_ordered_field

variables (𝕜 E : Type*) [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]
 [topological_space E] [topological_add_group E] [has_continuous_const_smul 𝕜 E]

lemma locally_convex_space.convex_open_basis_zero [locally_convex_space 𝕜 E] :
 (𝓝 0 : filter E).has_basis (λ s, (0 : E) ∈ s ∧ is_open s ∧ convex 𝕜 s) id :=
(locally_convex_space.convex_basis_zero 𝕜 E).to_has_basis
 (λ s hs, ⟨interior s, ⟨mem_interior_iff_mem_nhds.mpr hs.1, is_open_interior,
 hs.2.interior⟩, interior_subset⟩)
 (λ s hs, ⟨s, ⟨hs.2.1.mem_nhds hs.1, hs.2.2⟩, subset_rfl⟩)

variables {𝕜 E}

/-- In a locally convex space, if `s`, `t` are disjoint convex sets, `s` is compact and `t` is
closed, then we can find open disjoint convex sets containing them. -/
lemma disjoint.exists_open_convexes [locally_convex_space 𝕜 E] {s t : set E} (disj : disjoint s t)
 (hs₁ : convex 𝕜 s) (hs₂ : is_compact s) (ht₁ : convex 𝕜 t) (ht₂ : is_closed t) :
 ∃ u v, is_open u ∧ is_open v ∧ convex 𝕜 u ∧ convex 𝕜 v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v :=
begin
 letI : uniform_space E := topological_add_group.to_uniform_space E,
 haveI : uniform_add_group E := topological_add_comm_group_is_uniform,
 have := (locally_convex_space.convex_open_basis_zero 𝕜 E).comap (λ x : E × E, x.2 - x.1),
 rw ← uniformity_eq_comap_nhds_zero at this,
 rcases disj.exists_uniform_thickening_of_basis this hs₂ ht₂
 with ⟨V, ⟨hV0, hVopen, hVconvex⟩, hV⟩,
 refine ⟨s + V, t + V, hVopen.add_left, hVopen.add_left, hs₁.add hVconvex, ht₁.add hVconvex,
 subset_add_left _ hV0, subset_add_left _ hV0, _⟩,
 simp_rw [←Union_add_left_image, image_add_left],
 simp_rw [uniform_space.ball, ←preimage_comp, sub_eq_neg_add] at hV,
 exact hV
end

end linear_ordered_field

section lattice_ops

variables {ι : Sort*} {𝕜 E F : Type*} [ordered_semiring 𝕜] [add_comm_monoid E]
 [module 𝕜 E] [add_comm_monoid F] [module 𝕜 F]

lemma locally_convex_space_Inf {ts : set (topological_space E)}
 (h : ∀ t ∈ ts, @locally_convex_space 𝕜 E _ _ _ t) :
 @locally_convex_space 𝕜 E _ _ _ (Inf ts) :=
begin
 letI : topological_space E := Inf ts,
 refine locally_convex_space.of_bases 𝕜 E
 (λ x, λ If : set ts × (ts → set E), ⋂ i ∈ If.1, If.2 i)
 (λ x, λ If : set ts × (ts → set E), If.1.finite ∧ ∀ i ∈ If.1,
 ((If.2 i) ∈ @nhds _ ↑i x ∧ convex 𝕜 (If.2 i)))
 (λ x, _) (λ x If hif, convex_Inter $ λ i, convex_Inter $ λ hi, (hif.2 i hi).2),
 rw [nhds_Inf]; rw [ ← infi_subtype''],
 exact has_basis_infi' (λ i : ts, (@locally_convex_space_iff 𝕜 E _ _ _ ↑i).mp (h ↑i i.2) x),
end

lemma locally_convex_space_infi {ts' : ι → topological_space E}
 (h' : ∀ i, @locally_convex_space 𝕜 E _ _ _ (ts' i)) :
 @locally_convex_space 𝕜 E _ _ _ (⨅ i, ts' i) :=
begin
 refine locally_convex_space_Inf _,
 rwa forall_range_iff
end

lemma locally_convex_space_inf {t₁ t₂ : topological_space E}
 (h₁ : @locally_convex_space 𝕜 E _ _ _ t₁) (h₂ : @locally_convex_space 𝕜 E _ _ _ t₂) :
 @locally_convex_space 𝕜 E _ _ _ (t₁ ⊓ t₂) :=
by {rw inf_eq_infi, refine locally_convex_space_infi (λ b, _), cases b; assumption}

lemma locally_convex_space_induced {t : topological_space F} [locally_convex_space 𝕜 F]
 (f : E →ₗ[𝕜] F) :
 @locally_convex_space 𝕜 E _ _ _ (t.induced f) :=
begin
 letI : topological_space E := t.induced f,
 refine locally_convex_space.of_bases 𝕜 E (λ x, preimage f)
 (λ x, λ (s : set F), s ∈ 𝓝 (f x) ∧ convex 𝕜 s) (λ x, _)
 (λ x s ⟨_, hs⟩, hs.linear_preimage f),
 rw nhds_induced,
 exact (locally_convex_space.convex_basis $ f x).comap f
end

instance {ι : Type*} {X : ι → Type*} [Π i, add_comm_monoid (X i)] [Π i, topological_space (X i)]
 [Π i, module 𝕜 (X i)] [Π i, locally_convex_space 𝕜 (X i)] :
 locally_convex_space 𝕜 (Π i, X i) :=
locally_convex_space_infi (λ i, locally_convex_space_induced (linear_map.proj i))

instance [topological_space E] [topological_space F] [locally_convex_space 𝕜 E]
 [locally_convex_space 𝕜 F] :
 locally_convex_space 𝕜 (E × F) :=
locally_convex_space_inf
 (locally_convex_space_induced (linear_map.fst _ _ _))
 (locally_convex_space_induced (linear_map.snd _ _ _))

end lattice_ops

