/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/

import topology.vector_bundle.basic
import analysis.normed_space.operator_norm

/-!
# The vector bundle of continuous (semi)linear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the (topological) vector bundle of continuous (semi)linear maps between two vector bundles
over the same base.

Given bundles `E₁ E₂ : B → Type*`, normed spaces `F₁` and `F₂`, and a ring-homomorphism `σ` between
their respective scalar fields, we define `bundle.continuous_linear_map σ F₁ E₁ F₂ E₂ x` to be a
type synonym for `λ x, E₁ x →SL[σ] E₂ x`. If the `E₁` and `E₂` are vector bundles with model fibers
`F₁` and `F₂`, then this will be a vector bundle with fiber `F₁ →SL[σ] F₂`.

The topology on the total space is constructed from the trivializations for `E₁` and `E₂` and the
norm-topology on the model fiber `F₁ →SL[𝕜] F₂` using the `vector_prebundle` construction. This is
a bit awkward because it introduces a dependence on the normed space structure of the model fibers,
rather than just their topological vector space structure; it is not clear whether this is
necessary.

Similar constructions should be possible (but are yet to be formalized) for tensor products of
topological vector bundles, exterior algebras, and so on, where again the topology can be defined
using a norm on the fiber model if this helps.

## Main Definitions

* `bundle.continuous_linear_map.vector_bundle`: continuous semilinear maps between
 vector bundles form a vector bundle.

-/

noncomputable theory

open_locale bundle
open bundle set continuous_linear_map

variables {𝕜₁ : Type*} [nontrivially_normed_field 𝕜₁] {𝕜₂ : Type*} [nontrivially_normed_field 𝕜₂]
 (σ : 𝕜₁ →+* 𝕜₂) [iσ : ring_hom_isometric σ]

variables {B : Type*}

variables {F₁ : Type*} [normed_add_comm_group F₁] [normed_space 𝕜₁ F₁]
 (E₁ : B → Type*) [Π x, add_comm_group (E₁ x)] [Π x, module 𝕜₁ (E₁ x)]
 [topological_space (total_space F₁ E₁)]
variables {F₂ : Type*} [normed_add_comm_group F₂] [normed_space 𝕜₂ F₂]
 (E₂ : B → Type*) [Π x, add_comm_group (E₂ x)] [Π x, module 𝕜₂ (E₂ x)]
 [topological_space (total_space F₂ E₂)]

/-- A reducible type synonym for the bundle of continuous (semi)linear maps. For some reason, it
helps with instance search.

Porting note: after the port is done, we may want to remove this definition.
-/
@[reducible]
protected def bundle.continuous_linear_map [∀ x, topological_space (E₁ x)]
 [∀ x, topological_space (E₂ x)] : Π x : B, Type* :=
λ x, E₁ x →SL[σ] E₂ x

-- Porting note: possibly remove after the port
instance bundle.continuous_linear_map.module [∀ x, topological_space (E₁ x)]
 [∀ x, topological_space (E₂ x)] [∀ x, topological_add_group (E₂ x)]
 [∀ x, has_continuous_const_smul 𝕜₂ (E₂ x)] :
 ∀ x, module 𝕜₂ (bundle.continuous_linear_map σ E₁ E₂ x) :=
λ _, infer_instance

variables {E₁ E₂}

variables [topological_space B] (e₁ e₁' : trivialization F₁ (π F₁ E₁))
 (e₂ e₂' : trivialization F₂ (π F₂ E₂))

namespace pretrivialization

/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂'` is the coordinate change
function between the two induced (pre)trivializations
`pretrivialization.continuous_linear_map σ e₁ e₂` and
`pretrivialization.continuous_linear_map σ e₁' e₂'` of `bundle.continuous_linear_map`. -/
def continuous_linear_map_coord_change
 [e₁.is_linear 𝕜₁] [e₁'.is_linear 𝕜₁] [e₂.is_linear 𝕜₂] [e₂'.is_linear 𝕜₂] (b : B) :
 (F₁ →SL[σ] F₂) →L[𝕜₂] F₁ →SL[σ] F₂ :=
((e₁'.coord_changeL 𝕜₁ e₁ b).symm.arrow_congrSL (e₂.coord_changeL 𝕜₂ e₂' b) :
 (F₁ →SL[σ] F₂) ≃L[𝕜₂] F₁ →SL[σ] F₂)

variables {σ e₁ e₁' e₂ e₂'}
variables [Π x, topological_space (E₁ x)] [fiber_bundle F₁ E₁]
variables [Π x, topological_space (E₂ x)] [ita : Π x, topological_add_group (E₂ x)]
 [fiber_bundle F₂ E₂]

include iσ

lemma continuous_on_continuous_linear_map_coord_change
 [vector_bundle 𝕜₁ F₁ E₁] [vector_bundle 𝕜₂ F₂ E₂]
 [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₁']
 [mem_trivialization_atlas e₂] [mem_trivialization_atlas e₂'] :
 continuous_on (continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂')
 ((e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set)) :=
begin
 have h₁ := (compSL F₁ F₂ F₂ σ (ring_hom.id 𝕜₂)).continuous,
 have h₂ := (continuous_linear_map.flip (compSL F₁ F₁ F₂ (ring_hom.id 𝕜₁) σ)).continuous,
 have h₃ := (continuous_on_coord_change 𝕜₁ e₁' e₁),
 have h₄ := (continuous_on_coord_change 𝕜₂ e₂ e₂'),
 refine ((h₁.comp_continuous_on (h₄.mono _)).clm_comp (h₂.comp_continuous_on (h₃.mono _))).congr _,
 { mfld_set_tac },
 { mfld_set_tac },
 { intros b hb, ext L v,
 simp only [continuous_linear_map_coord_change, continuous_linear_equiv.coe_coe,
 continuous_linear_equiv.arrow_congrSL_apply,
 comp_apply, function.comp, compSL_apply, flip_apply, continuous_linear_equiv.symm_symm] },
end

omit iσ

variables (σ e₁ e₁' e₂ e₂')
 [e₁.is_linear 𝕜₁] [e₁'.is_linear 𝕜₁] [e₂.is_linear 𝕜₂] [e₂'.is_linear 𝕜₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`pretrivialization.continuous_linear_map σ e₁ e₂` is the induced pretrivialization for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
topological vector bundle structure. -/
def continuous_linear_map :
 pretrivialization (F₁ →SL[σ] F₂) (π (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂)) :=
{ to_fun := λ p, ⟨p.1, continuous_linear_map.comp (e₂.continuous_linear_map_at 𝕜₂ p.1)
 (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁ →L[𝕜₁] E₁ p.1) : F₁ →SL[σ] E₂ p.1)⟩,
 inv_fun := λ p, ⟨p.1, continuous_linear_map.comp (e₂.symmL 𝕜₂ p.1)
 (p.2.comp (e₁.continuous_linear_map_at 𝕜₁ p.1 : E₁ p.1 →L[𝕜₁] F₁) : E₁ p.1 →SL[σ] F₂)⟩,
 source := (bundle.total_space.proj) ⁻¹' (e₁.base_set ∩ e₂.base_set),
 target := (e₁.base_set ∩ e₂.base_set) ×ˢ set.univ,
 map_source' := λ ⟨x, L⟩ h, ⟨h, set.mem_univ _⟩,
 map_target' := λ ⟨x, f⟩ h, h.1,
 left_inv' := λ ⟨x, L⟩ ⟨h₁, h₂⟩,
 begin
 simp_rw [sigma.mk.inj_iff, eq_self_iff_true, heq_iff_eq, true_and],
 ext v,
 simp only [comp_apply, trivialization.symmL_continuous_linear_map_at, h₁, h₂]
 end,
 right_inv' := λ ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩,
 begin
 simp_rw [prod.mk.inj_iff, eq_self_iff_true, true_and],
 ext v,
 simp only [comp_apply, trivialization.continuous_linear_map_at_symmL, h₁, h₂]
 end,
 open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
 base_set := e₁.base_set ∩ e₂.base_set,
 open_base_set := e₁.open_base_set.inter e₂.open_base_set,
 source_eq := rfl,
 target_eq := rfl,
 proj_to_fun := λ ⟨x, f⟩ h, rfl }

include ita

-- porting note: todo: see if Lean 4 can generate this instance without a hint
instance continuous_linear_map.is_linear
 [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜₂ (E₂ x)] :
 (pretrivialization.continuous_linear_map σ e₁ e₂).is_linear 𝕜₂ :=
{ linear := λ x h,
 { map_add := λ L L',
 show (e₂.continuous_linear_map_at 𝕜₂ x).comp ((L + L').comp (e₁.symmL 𝕜₁ x)) = _,
 begin
 simp_rw [add_comp, comp_add],
 refl
 end,
 map_smul := λ c L,
 show (e₂.continuous_linear_map_at 𝕜₂ x).comp ((c • L).comp (e₁.symmL 𝕜₁ x)) = _,
 begin
 simp_rw [smul_comp, comp_smulₛₗ, ring_hom.id_apply],
 refl
 end, } }

omit ita

lemma continuous_linear_map_apply
 (p : total_space (F₁ →SL[σ] F₂) (λ x, E₁ x →SL[σ] E₂ x)) :
 (continuous_linear_map σ e₁ e₂) p =
 ⟨p.1, continuous_linear_map.comp (e₂.continuous_linear_map_at 𝕜₂ p.1)
 (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁ →L[𝕜₁] E₁ p.1) : F₁ →SL[σ] E₂ p.1)⟩ :=
rfl

lemma continuous_linear_map_symm_apply (p : B × (F₁ →SL[σ] F₂)) :
 (continuous_linear_map σ e₁ e₂).to_local_equiv.symm p =
 ⟨p.1, continuous_linear_map.comp (e₂.symmL 𝕜₂ p.1)
 (p.2.comp (e₁.continuous_linear_map_at 𝕜₁ p.1 : E₁ p.1 →L[𝕜₁] F₁) : E₁ p.1 →SL[σ] F₂)⟩ :=
rfl

include ita

lemma continuous_linear_map_symm_apply' {b : B} (hb : b ∈ e₁.base_set ∩ e₂.base_set)
 (L : F₁ →SL[σ] F₂) :
 (continuous_linear_map σ e₁ e₂).symm b L =
 (e₂.symmL 𝕜₂ b).comp (L.comp $ e₁.continuous_linear_map_at 𝕜₁ b) :=
begin
 rw [symm_apply], refl, exact hb
end

lemma continuous_linear_map_coord_change_apply (b : B)
 (hb : b ∈ (e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set)) (L : F₁ →SL[σ] F₂) :
 continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂' b L =
 (continuous_linear_map σ e₁' e₂' ⟨b, ((continuous_linear_map σ e₁ e₂).symm b L)⟩).2 :=
begin
 ext v,
 simp_rw [continuous_linear_map_coord_change, continuous_linear_equiv.coe_coe, continuous_linear_equiv.arrow_congrSL_apply, continuous_linear_map_apply, continuous_linear_map_symm_apply' σ e₁ e₂ hb.1, comp_apply, continuous_linear_equiv.coe_coe, continuous_linear_equiv.symm_symm, trivialization.continuous_linear_map_at_apply, trivialization.symmL_apply],
 rw [e₂.coord_changeL_apply e₂']; rw [ e₁'.coord_changeL_apply e₁]; rw [ e₁.coe_linear_map_at_of_mem hb.1.1]; rw [ e₂'.coe_linear_map_at_of_mem hb.2.2],
 exacts [⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]
end

end pretrivialization

open pretrivialization
variables (F₁ E₁ F₂ E₂)
variables [Π x : B, topological_space (E₁ x)] [fiber_bundle F₁ E₁] [vector_bundle 𝕜₁ F₁ E₁]
variables [Π x : B, topological_space (E₂ x)] [fiber_bundle F₂ E₂] [vector_bundle 𝕜₂ F₂ E₂]
variables [Π x, topological_add_group (E₂ x)] [Π x, has_continuous_smul 𝕜₂ (E₂ x)]

include iσ

/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`vector_prebundle` (this is an auxiliary construction for the
`vector_bundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def _root_.bundle.continuous_linear_map.vector_prebundle :
 vector_prebundle 𝕜₂ (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂) :=
{ pretrivialization_atlas :=
 {e | ∃ (e₁ : trivialization F₁ (π F₁ E₁)) (e₂ : trivialization F₂ (π F₂ E₂))
 [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₂], by exactI
 e = pretrivialization.continuous_linear_map σ e₁ e₂},
 pretrivialization_linear' := begin
 rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩,
 apply_instance
 end,
 pretrivialization_at := λ x, pretrivialization.continuous_linear_map σ
 (trivialization_at F₁ E₁ x) (trivialization_at F₂ E₂ x),
 mem_base_pretrivialization_at := λ x,
 ⟨mem_base_set_trivialization_at F₁ E₁ x, mem_base_set_trivialization_at F₂ E₂ x⟩,
 pretrivialization_mem_atlas := λ x,
 ⟨trivialization_at F₁ E₁ x, trivialization_at F₂ E₂ x, _, _, rfl⟩,
 exists_coord_change := by { rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩,
 resetI,
 exact ⟨continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂',
 continuous_on_continuous_linear_map_coord_change,
 continuous_linear_map_coord_change_apply σ e₁ e₁' e₂ e₂'⟩ },
 total_space_mk_inducing :=
 begin
 intros b,
 let L₁ : E₁ b ≃L[𝕜₁] F₁ := (trivialization_at F₁ E₁ b).continuous_linear_equiv_at 𝕜₁ b
 (mem_base_set_trivialization_at _ _ _),
 let L₂ : E₂ b ≃L[𝕜₂] F₂ := (trivialization_at F₂ E₂ b).continuous_linear_equiv_at 𝕜₂ b
 (mem_base_set_trivialization_at _ _ _),
 let φ : (E₁ b →SL[σ] E₂ b) ≃L[𝕜₂] (F₁ →SL[σ] F₂) := L₁.arrow_congrSL L₂,
 have : inducing (λ x, (b, φ x)) := inducing_const_prod.mpr φ.to_homeomorph.inducing,
 convert this,
 ext f,
 { refl },
 ext x,
 dsimp [φ, pretrivialization.continuous_linear_map_apply],
 rw [trivialization.linear_map_at_def_of_mem _ (mem_base_set_trivialization_at _ _ _)],
 refl
 end }

/-- Topology on the total space of the continuous `σ`-semilinear_maps between two "normable" vector
bundles over the same base. -/
instance bundle.continuous_linear_map.topological_space_total_space :
 topological_space (total_space (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂)) :=
(bundle.continuous_linear_map.vector_prebundle
 σ F₁ E₁ F₂ E₂).total_space_topology

/-- The continuous `σ`-semilinear_maps between two vector bundles form a fiber bundle. -/
instance _root_.bundle.continuous_linear_map.fiber_bundle :
 fiber_bundle (F₁ →SL[σ] F₂) (λ x, E₁ x →SL[σ] E₂ x) :=
(bundle.continuous_linear_map.vector_prebundle
 σ F₁ E₁ F₂ E₂).to_fiber_bundle

/-- The continuous `σ`-semilinear_maps between two vector bundles form a vector bundle. -/
instance _root_.bundle.continuous_linear_map.vector_bundle :
 vector_bundle 𝕜₂ (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂) :=
(bundle.continuous_linear_map.vector_prebundle
 σ F₁ E₁ F₂ E₂).to_vector_bundle

variables (e₁ e₂) [he₁ : mem_trivialization_atlas e₁] [he₂ : mem_trivialization_atlas e₂]
 {F₁ E₁ F₂ E₂}

include he₁ he₂

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`,
whose base set is `e₁.base_set ∩ e₂.base_set`. -/
def trivialization.continuous_linear_map :
 trivialization (F₁ →SL[σ] F₂) (π (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂)) :=
vector_prebundle.trivialization_of_mem_pretrivialization_atlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

instance _root_.bundle.continuous_linear_map.mem_trivialization_atlas :
 mem_trivialization_atlas (e₁.continuous_linear_map σ e₂ :
 trivialization (F₁ →SL[σ] F₂) (π (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂))) :=
{ out := ⟨_, ⟨e₁, e₂, by apply_instance, by apply_instance, rfl⟩, rfl⟩ }

variables {e₁ e₂}

@[simp] lemma trivialization.base_set_continuous_linear_map :
 (e₁.continuous_linear_map σ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

lemma trivialization.continuous_linear_map_apply
 (p : total_space (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂)) :
 e₁.continuous_linear_map σ e₂ p =
 ⟨p.1, (e₂.continuous_linear_map_at 𝕜₂ p.1 : _ →L[𝕜₂] _).comp
 (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁ →L[𝕜₁] E₁ p.1) : F₁ →SL[σ] E₂ p.1)⟩ :=
rfl

omit he₁ he₂

lemma hom_trivialization_at_apply (x₀ : B)
 (x : total_space (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂)) :
 trivialization_at (F₁ →SL[σ] F₂) (λ x, E₁ x →SL[σ] E₂ x) x₀ x =
 ⟨x.1, in_coordinates F₁ E₁ F₂ E₂ x₀ x.1 x₀ x.1 x.2⟩ :=
rfl

@[simp, mfld_simps]
lemma hom_trivialization_at_source (x₀ : B) :
 (trivialization_at (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂) x₀).source =
 π (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ E₁ E₂) ⁻¹'
 ((trivialization_at F₁ E₁ x₀).base_set ∩ (trivialization_at F₂ E₂ x₀).base_set) :=
rfl

@[simp, mfld_simps]
lemma hom_trivialization_at_target (x₀ : B) :
 (trivialization_at (F₁ →SL[σ] F₂) (λ x, E₁ x →SL[σ] E₂ x) x₀).target =
 ((trivialization_at F₁ E₁ x₀).base_set ∩ (trivialization_at F₂ E₂ x₀).base_set) ×ˢ set.univ :=
rfl

