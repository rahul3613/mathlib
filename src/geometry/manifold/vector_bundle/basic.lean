/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import geometry.manifold.vector_bundle.fiberwise_linear
import topology.vector_bundle.constructions

/-! # Smooth vector bundles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines smooth vector bundles over a smooth manifold.

Let `E` be a topological vector bundle, with model fiber `F` and base space `B`. We consider `E` as
carrying a charted space structure given by its trivializations -- these are charts to `B × F`.
Then, by "composition", if `B` is itself a charted space over `H` (e.g. a smooth manifold), then `E`
is also a charted space over `H × F`

Now, we define `smooth_vector_bundle` as the `Prop` of having smooth transition functions.
Recall the structure groupoid `smooth_fiberwise_linear` on `B × F` consisting of smooth, fiberwise
linear local homeomorphisms. We show that our definition of "smooth vector bundle" implies
`has_groupoid` for this groupoid, and show (by a "composition" of `has_groupoid` instances) that
this means that a smooth vector bundle is a smooth manifold.

Since `smooth_vector_bundle` is a mixin, it should be easy to make variants and for many such
variants to coexist -- vector bundles can be smooth vector bundles over several different base
fields, they can also be C^k vector bundles, etc.

## Main definitions and constructions

* `fiber_bundle.charted_space`: A fiber bundle `E` over a base `B` with model fiber `F` is naturally
 a charted space modelled on `B × F`.

* `fiber_bundle.charted_space'`: Let `B` be a charted space modelled on `HB`. Then a fiber bundle
 `E` over a base `B` with model fiber `F` is naturally a charted space modelled on `HB.prod F`.

* `smooth_vector_bundle`: Mixin class stating that a (topological) `vector_bundle` is smooth, in the
 sense of having smooth transition functions.

* `smooth_fiberwise_linear.has_groupoid`: For a smooth vector bundle `E` over `B` with fiber
 modelled on `F`, the change-of-co-ordinates between two trivializations `e`, `e'` for `E`,
 considered as charts to `B × F`, is smooth and fiberwise linear, in the sense of belonging to the
 structure groupoid `smooth_fiberwise_linear`.

* `bundle.total_space.smooth_manifold_with_corners`: A smooth vector bundle is naturally a smooth
 manifold.

* `vector_bundle_core.smooth_vector_bundle`: If a (topological) `vector_bundle_core` is smooth,
 in the sense of having smooth transition functions (cf. `vector_bundle_core.is_smooth`),
 then the vector bundle constructed from it is a smooth vector bundle.

* `vector_prebundle.smooth_vector_bundle`: If a `vector_prebundle` is smooth,
 in the sense of having smooth transition functions (cf. `vector_prebundle.is_smooth`),
 then the vector bundle constructed from it is a smooth vector bundle.

* `bundle.prod.smooth_vector_bundle`: The direct sum of two smooth vector bundles is a smooth vector
 bundle.
-/

assert_not_exists mfderiv

open bundle set local_homeomorph function (id_def) filter
open_locale manifold bundle topology

variables {𝕜 B B' F M : Type*} {E : B → Type*}

/-! ### Charted space structure on a fiber bundle -/

section
variables [topological_space F] [topological_space (total_space F E)] [∀ x, topological_space (E x)]
 {HB : Type*} [topological_space HB]
 [topological_space B] [charted_space HB B] [fiber_bundle F E]

/-- A fiber bundle `E` over a base `B` with model fiber `F` is naturally a charted space modelled on
`B × F`. -/
instance fiber_bundle.charted_space : charted_space (B × F) (total_space F E) :=
{ atlas := (λ e : trivialization F (π F E), e.to_local_homeomorph) '' trivialization_atlas F E,
 chart_at := λ x, (trivialization_at F E x.proj).to_local_homeomorph,
 mem_chart_source := λ x, (trivialization_at F E x.proj).mem_source.mpr
 (mem_base_set_trivialization_at F E x.proj),
 chart_mem_atlas := λ x, mem_image_of_mem _ (trivialization_mem_atlas F E _) }

section
local attribute [reducible] model_prod

/-- Let `B` be a charted space modelled on `HB`. Then a fiber bundle `E` over a base `B` with model
fiber `F` is naturally a charted space modelled on `HB.prod F`. -/
instance fiber_bundle.charted_space' : charted_space (model_prod HB F) (total_space F E) :=
charted_space.comp _ (model_prod B F) _
end

lemma fiber_bundle.charted_space_chart_at (x : total_space F E) :
 chart_at (model_prod HB F) x =
 (trivialization_at F E x.proj).to_local_homeomorph ≫ₕ
 (chart_at HB x.proj).prod (local_homeomorph.refl F) :=
begin
 dsimp only [fiber_bundle.charted_space', charted_space.comp, fiber_bundle.charted_space,
 prod_charted_space, charted_space_self],
 rw [trivialization.coe_coe]; rw [ trivialization.coe_fst' _ (mem_base_set_trivialization_at F E x.proj)]
end

lemma fiber_bundle.charted_space_chart_at_symm_fst (x : total_space F E) (y : model_prod HB F)
 (hy : y ∈ (chart_at (model_prod HB F) x).target) :
 ((chart_at (model_prod HB F) x).symm y).proj = (chart_at HB x.proj).symm y.1 :=
begin
 simp only [fiber_bundle.charted_space_chart_at] with mfld_simps at hy ⊢,
 exact (trivialization_at F E x.proj).proj_symm_apply hy.2,
end

end

section
variables [nontrivially_normed_field 𝕜]
 [normed_add_comm_group F] [normed_space 𝕜 F]
 [topological_space (total_space F E)] [∀ x, topological_space (E x)]

 {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
 {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
 (E' : B → Type*) [Π x, has_zero (E' x)]
 {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
 {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
 [topological_space M] [charted_space HM M] [Is : smooth_manifold_with_corners IM M]
 {n : ℕ∞}

variables [topological_space B] [charted_space HB B] [fiber_bundle F E]

protected lemma fiber_bundle.ext_chart_at (x : total_space F E) :
 ext_chart_at (IB.prod 𝓘(𝕜, F)) x =
 (trivialization_at F E x.proj).to_local_equiv ≫
 (ext_chart_at IB x.proj).prod (local_equiv.refl F) :=
begin
 simp_rw [ext_chart_at, fiber_bundle.charted_space_chart_at, extend],
 simp only [local_equiv.trans_assoc] with mfld_simps,
end

/-! ### Smoothness of maps in/out fiber bundles

Note: For these results we don't need that the bundle is a smooth vector bundle, or even a vector
bundle at all, just that it is a fiber bundle over a charted base space.
-/

namespace bundle
variables {F E IB}

/-- Characterization of C^n functions into a smooth vector bundle. -/
lemma cont_mdiff_within_at_total_space (f : M → total_space F E) {s : set M} {x₀ : M} :
 cont_mdiff_within_at IM (IB.prod (𝓘(𝕜, F))) n f s x₀ ↔
 cont_mdiff_within_at IM IB n (λ x, (f x).proj) s x₀ ∧
 cont_mdiff_within_at IM 𝓘(𝕜, F) n (λ x, (trivialization_at F E (f x₀).proj (f x)).2) s x₀ :=
begin
 simp only [cont_mdiff_within_at_iff_target] {single_pass := tt},
 rw [and_and_and_comm]; rw [ ← continuous_within_at_total_space]; rw [ and.congr_right_iff],
 intros hf,
 simp_rw [model_with_corners_self_prod, fiber_bundle.ext_chart_at, function.comp, local_equiv.trans_apply, local_equiv.prod_coe, local_equiv.refl_coe, ext_chart_at_self_apply, model_with_corners_self_coe, id_def],
 refine (cont_mdiff_within_at_prod_iff _).trans _, -- rw doesn't do this?
 have h1 : (λ x, (f x).proj) ⁻¹' (trivialization_at F E (f x₀).proj).base_set ∈ 𝓝[s] x₀ :=
 ((continuous_proj F E).continuous_within_at.comp hf (maps_to_image f s))
 .preimage_mem_nhds_within
 ((trivialization.open_base_set _).mem_nhds (mem_base_set_trivialization_at F E _)),
 refine and_congr (eventually_eq.cont_mdiff_within_at_iff (eventually_of_mem h1 $ λ x hx, _) _)
 iff.rfl,
 { simp_rw [function.comp, local_homeomorph.coe_coe, trivialization.coe_coe],
 rw [trivialization.coe_fst'],
 exact hx },
 { simp only with mfld_simps },
end

/-- Characterization of C^n functions into a smooth vector bundle. -/
lemma cont_mdiff_at_total_space (f : M → total_space F E) (x₀ : M) :
 cont_mdiff_at IM (IB.prod (𝓘(𝕜, F))) n f x₀ ↔
 cont_mdiff_at IM IB n (λ x, (f x).proj) x₀ ∧
 cont_mdiff_at IM 𝓘(𝕜, F) n (λ x, (trivialization_at F E (f x₀).proj (f x)).2) x₀ :=
by { simp_rw [← cont_mdiff_within_at_univ], exact cont_mdiff_within_at_total_space f }

/-- Characterization of C^n sections of a smooth vector bundle. -/
lemma cont_mdiff_at_section (s : Π x, E x) (x₀ : B) :
 cont_mdiff_at IB (IB.prod (𝓘(𝕜, F))) n (λ x, total_space.mk' F x (s x)) x₀ ↔
 cont_mdiff_at IB 𝓘(𝕜, F) n (λ x, (trivialization_at F E x₀ (total_space.mk' F x (s x))).2) x₀ :=
by { simp_rw [cont_mdiff_at_total_space, and_iff_right_iff_imp], intro x, exact cont_mdiff_at_id }

variables (E)
lemma cont_mdiff_proj : cont_mdiff (IB.prod 𝓘(𝕜, F)) IB n (π F E) :=
begin
 intro x,
 rw [cont_mdiff_at]; rw [ cont_mdiff_within_at_iff'],
 refine ⟨(continuous_proj F E).continuous_within_at, _⟩,
 simp_rw [(∘), fiber_bundle.ext_chart_at],
 apply cont_diff_within_at_fst.congr,
 { rintros ⟨a, b⟩ hab,
 simp only with mfld_simps at hab,
 have : ((chart_at HB x.1).symm (IB.symm a), b) ∈ (trivialization_at F E x.proj).target,
 { simp only [hab] with mfld_simps },
 simp only [trivialization.proj_symm_apply _ this, hab] with mfld_simps },
 { simp only with mfld_simps }
end

lemma smooth_proj : smooth (IB.prod 𝓘(𝕜, F)) IB (π F E) :=
cont_mdiff_proj E

lemma cont_mdiff_on_proj {s : set (total_space F E)} :
 cont_mdiff_on (IB.prod 𝓘(𝕜, F)) IB n (π F E) s :=
(bundle.cont_mdiff_proj E).cont_mdiff_on

lemma smooth_on_proj {s : set (total_space F E)} :
 smooth_on (IB.prod 𝓘(𝕜, F)) IB (π F E) s :=
cont_mdiff_on_proj E

lemma cont_mdiff_at_proj {p : total_space F E} :
 cont_mdiff_at (IB.prod 𝓘(𝕜, F)) IB n
 (π F E) p :=
(bundle.cont_mdiff_proj E).cont_mdiff_at

lemma smooth_at_proj {p : total_space F E} :
 smooth_at (IB.prod 𝓘(𝕜, F)) IB (π F E) p :=
bundle.cont_mdiff_at_proj E

lemma cont_mdiff_within_at_proj
 {s : set (total_space F E)}
 {p : total_space F E} :
 cont_mdiff_within_at (IB.prod 𝓘(𝕜, F)) IB n (π F E) s p :=
(bundle.cont_mdiff_at_proj E).cont_mdiff_within_at

lemma smooth_within_at_proj
 {s : set (total_space F E)}
 {p : total_space F E} :
 smooth_within_at (IB.prod 𝓘(𝕜, F)) IB (π F E) s p :=
bundle.cont_mdiff_within_at_proj E

variables (𝕜 E) [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)] [vector_bundle 𝕜 F E]

lemma smooth_zero_section : smooth IB (IB.prod 𝓘(𝕜, F)) (zero_section F E) :=
begin
 intro x,
 rw [bundle.cont_mdiff_at_total_space],
 refine ⟨cont_mdiff_at_id, cont_mdiff_at_const.congr_of_eventually_eq _⟩,
 { exact 0 },
 refine eventually_of_mem ((trivialization_at F E x).open_base_set.mem_nhds
 (mem_base_set_trivialization_at F E x)) (λ x' hx', _),
 simp_rw [zero_section_proj, (trivialization_at F E x).zero_section 𝕜 hx']
end

end bundle

end

/-! ### Smooth vector bundles -/

variables [nontrivially_normed_field 𝕜]
 {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
 {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
 [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]
 {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
 {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
 [topological_space M] [charted_space HM M] [Is : smooth_manifold_with_corners IM M]
 {n : ℕ∞}
 [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
 [normed_add_comm_group F] [normed_space 𝕜 F]

section with_topology

variables [topological_space (total_space F E)] [∀ x, topological_space (E x)]

variables (F E) [fiber_bundle F E] [vector_bundle 𝕜 F E]

/-- When `B` is a smooth manifold with corners with respect to a model `IB` and `E` is a
topological vector bundle over `B` with fibers isomorphic to `F`, then `smooth_vector_bundle F E IB`
registers that the bundle is smooth, in the sense of having smooth transition functions.
This is a mixin, not carrying any new data`. -/
class smooth_vector_bundle : Prop :=
(smooth_on_coord_change : ∀ (e e' : trivialization F (π F E))
 [mem_trivialization_atlas e] [mem_trivialization_atlas e'],
 smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ b : B, (e.coord_changeL 𝕜 e' b : F →L[𝕜] F))
 (e.base_set ∩ e'.base_set))

export smooth_vector_bundle (smooth_on_coord_change)

variables [smooth_vector_bundle F E IB]

/-- For a smooth vector bundle `E` over `B` with fiber modelled on `F`, the change-of-co-ordinates
between two trivializations `e`, `e'` for `E`, considered as charts to `B × F`, is smooth and
fiberwise linear. -/
instance : has_groupoid (total_space F E) (smooth_fiberwise_linear B F IB) :=
{ compatible := begin
 rintros _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩,
 haveI : mem_trivialization_atlas e := ⟨he⟩,
 haveI : mem_trivialization_atlas e' := ⟨he'⟩,
 resetI,
 rw mem_smooth_fiberwise_linear_iff,
 refine ⟨_, _, e.open_base_set.inter e'.open_base_set, smooth_on_coord_change e e', _, _, _⟩,
 { rw inter_comm,
 apply cont_mdiff_on.congr (smooth_on_coord_change e' e),
 { intros b hb,
 rw e.symm_coord_changeL e' hb },
 { apply_instance },
 { apply_instance }, },
 { simp only [e.symm_trans_source_eq e', fiberwise_linear.local_homeomorph,
 trans_to_local_equiv, symm_to_local_equiv]},
 { rintros ⟨b, v⟩ hb,
 have hb' : b ∈ e.base_set ∩ e'.base_set,
 { simpa only [trans_to_local_equiv, symm_to_local_equiv, e.symm_trans_source_eq e',
 coe_coe_symm, prod_mk_mem_set_prod_eq, mem_univ, and_true] using hb },
 exact e.apply_symm_apply_eq_coord_changeL e' hb' v, }
 end }

/-- A smooth vector bundle `E` is naturally a smooth manifold. -/
instance : smooth_manifold_with_corners (IB.prod 𝓘(𝕜, F)) (total_space F E) :=
begin
 refine { .. structure_groupoid.has_groupoid.comp (smooth_fiberwise_linear B F IB) _ },
 intros e he,
 rw mem_smooth_fiberwise_linear_iff at he,
 obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he,
 rw [is_local_structomorph_on_cont_diff_groupoid_iff],
 refine ⟨cont_mdiff_on.congr _ heφ.eq_on, cont_mdiff_on.congr _ heφ.symm'.eq_on⟩,
 { rw heφ.source_eq,
 apply smooth_on_fst.prod_mk,
 exact (hφ.comp cont_mdiff_on_fst $ prod_subset_preimage_fst _ _).clm_apply cont_mdiff_on_snd },
 { rw heφ.target_eq,
 apply smooth_on_fst.prod_mk,
 exact (h2φ.comp cont_mdiff_on_fst $ prod_subset_preimage_fst _ _).clm_apply cont_mdiff_on_snd },
end

/-! ### Core construction for smooth vector bundles -/

namespace vector_bundle_core
variables {ι : Type*} {F} (Z : vector_bundle_core 𝕜 B F ι)

/-- Mixin for a `vector_bundle_core` stating smoothness (of transition functions). -/
class is_smooth (IB : model_with_corners 𝕜 EB HB) : Prop :=
(smooth_on_coord_change [] :
 ∀ i j, smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (Z.coord_change i j) (Z.base_set i ∩ Z.base_set j))

export is_smooth (renaming smooth_on_coord_change → vector_bundle_core.smooth_on_coord_change)

variables [Z.is_smooth IB]

/-- If a `vector_bundle_core` has the `is_smooth` mixin, then the vector bundle constructed from it
is a smooth vector bundle. -/
instance smooth_vector_bundle : smooth_vector_bundle F Z.fiber IB :=
{ smooth_on_coord_change := begin
 rintros - - ⟨i, rfl⟩ ⟨i', rfl⟩,
 refine (Z.smooth_on_coord_change IB i i').congr (λ b hb, _),
 ext v,
 exact Z.local_triv_coord_change_eq i i' hb v,
 end }

end vector_bundle_core

/-! ### The trivial smooth vector bundle -/

/-- A trivial vector bundle over a smooth manifold is a smooth vector bundle. -/
instance bundle.trivial.smooth_vector_bundle : smooth_vector_bundle F (bundle.trivial B F) IB :=
{ smooth_on_coord_change := begin
 introsI e e' he he',
 unfreezingI { obtain rfl := bundle.trivial.eq_trivialization B F e },
 unfreezingI { obtain rfl := bundle.trivial.eq_trivialization B F e' },
 simp_rw bundle.trivial.trivialization.coord_changeL,
 exact smooth_const.smooth_on
 end }

/-! ### Direct sums of smooth vector bundles -/

section prod
variables (F₁ : Type*) [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
 (E₁ : B → Type*) [topological_space (total_space F₁ E₁)]
 [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜 (E₁ x)]

variables (F₂ : Type*) [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
 (E₂ : B → Type*) [topological_space (total_space F₂ E₂)]
 [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜 (E₂ x)]

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
 [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]
 [vector_bundle 𝕜 F₁ E₁] [vector_bundle 𝕜 F₂ E₂]
 [smooth_vector_bundle F₁ E₁ IB] [smooth_vector_bundle F₂ E₂ IB]

/-- The direct sum of two smooth vector bundles over the same base is a smooth vector bundle. -/
instance bundle.prod.smooth_vector_bundle :
 smooth_vector_bundle (F₁ × F₂) (E₁ ×ᵇ E₂) IB :=
{ smooth_on_coord_change := begin
 rintros _ _ ⟨e₁, e₂, i₁, i₂, rfl⟩ ⟨e₁', e₂', i₁', i₂', rfl⟩,
 resetI,
 rw [smooth_on],
 refine cont_mdiff_on.congr _ (e₁.coord_changeL_prod 𝕜 e₁' e₂ e₂'),
 refine cont_mdiff_on.clm_prod_map _ _,
 { refine (smooth_on_coord_change e₁ e₁').mono _,
 simp only [trivialization.base_set_prod] with mfld_simps,
 mfld_set_tac },
 { refine (smooth_on_coord_change e₂ e₂').mono _,
 simp only [trivialization.base_set_prod] with mfld_simps,
 mfld_set_tac },
 end }

end prod

end with_topology

/-! ### Prebundle construction for smooth vector bundles -/

namespace vector_prebundle

variables [∀ x, topological_space (E x)] {F E}

/-- Mixin for a `vector_prebundle` stating smoothness of coordinate changes. -/
class is_smooth (a : vector_prebundle 𝕜 F E) : Prop :=
(exists_smooth_coord_change : ∀ (e e' ∈ a.pretrivialization_atlas), ∃ f : B → F →L[𝕜] F,
 smooth_on IB 𝓘(𝕜, F →L[𝕜] F) f (e.base_set ∩ e'.base_set) ∧
 ∀ (b : B) (hb : b ∈ e.base_set ∩ e'.base_set) (v : F), f b v = (e' ⟨b ,e.symm b v⟩).2)

variables (a : vector_prebundle 𝕜 F E) [ha : a.is_smooth IB] {e e' : pretrivialization F (π F E)}
include ha

/-- A randomly chosen coordinate change on a `smooth_vector_prebundle`, given by
 the field `exists_coord_change`. Note that `a.smooth_coord_change` need not be the same as
 `a.coord_change`. -/
noncomputable def smooth_coord_change (he : e ∈ a.pretrivialization_atlas)
 (he' : e' ∈ a.pretrivialization_atlas) (b : B) : F →L[𝕜] F :=
classical.some (ha.exists_smooth_coord_change e he e' he') b

variables {IB}
lemma smooth_on_smooth_coord_change (he : e ∈ a.pretrivialization_atlas)
 (he' : e' ∈ a.pretrivialization_atlas) :
 smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (a.smooth_coord_change IB he he') (e.base_set ∩ e'.base_set) :=
(classical.some_spec (ha.exists_smooth_coord_change e he e' he')).1

lemma smooth_coord_change_apply (he : e ∈ a.pretrivialization_atlas)
 (he' : e' ∈ a.pretrivialization_atlas) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
 a.smooth_coord_change IB he he' b v = (e' ⟨b, e.symm b v⟩).2 :=
(classical.some_spec (ha.exists_smooth_coord_change e he e' he')).2 b hb v

lemma mk_smooth_coord_change (he : e ∈ a.pretrivialization_atlas)
 (he' : e' ∈ a.pretrivialization_atlas) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
 (b, (a.smooth_coord_change IB he he' b v)) = e' ⟨b, e.symm b v⟩ :=
begin
 ext,
 { rw [e.mk_symm hb.1 v]; rw [ e'.coe_fst']; rw [ e.proj_symm_apply' hb.1],
 rw [e.proj_symm_apply' hb.1], exact hb.2 },
 { exact a.smooth_coord_change_apply he he' hb v }
end

variables (IB)
/-- Make a `smooth_vector_bundle` from a `smooth_vector_prebundle`. -/
lemma smooth_vector_bundle :
 @smooth_vector_bundle _ _ F E _ _ _ _ _ _ IB _ _ _ _ _ _ _
 a.total_space_topology _ a.to_fiber_bundle a.to_vector_bundle :=
{ smooth_on_coord_change := begin
 rintros _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩,
 refine (a.smooth_on_smooth_coord_change he he').congr _,
 intros b hb,
 ext v,
 rw [a.smooth_coord_change_apply he he' hb v]; rw [ continuous_linear_equiv.coe_coe]; rw [ trivialization.coord_changeL_apply],
 exacts [rfl, hb]
 end }

end vector_prebundle

