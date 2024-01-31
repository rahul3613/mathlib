/-
Copyright (c) 2022 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import analysis.convex.cone.dual
import analysis.inner_product_space.adjoint

/-!
# Proper cones

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define a proper cone as a nonempty, closed, convex cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once have the definitions of conic programs and
linear programs, the results from this file can be used to prove duality theorems.

## TODO

The next steps are:
- Add convex_cone_class that extends set_like and replace the below instance
- Define the positive cone as a proper cone.
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.
- Find a better reference (textbook instead of lecture notes).
- Show submodules are (proper) cones.

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

open continuous_linear_map filter set

namespace convex_cone

variables {𝕜 : Type*} [ordered_semiring 𝕜]
variables {E : Type*} [add_comm_monoid E] [topological_space E] [has_continuous_add E]
  [has_smul 𝕜 E] [has_continuous_const_smul 𝕜 E]

/-- The closure of a convex cone inside a topological space as a convex cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : convex_cone 𝕜 E) : convex_cone 𝕜 E :=
{ carrier := closure ↑K,
  smul_mem' :=
    λ c hc _ h₁, map_mem_closure (continuous_id'.const_smul c) h₁ (λ _ h₂, K.smul_mem hc h₂),
  add_mem' := λ _ h₁ _ h₂, map_mem_closure₂ continuous_add h₁ h₂ K.add_mem }

@[simp, norm_cast] lemma coe_closure (K : convex_cone 𝕜 E) : (K.closure : set E) = closure K := rfl

@[simp] protected lemma mem_closure {K : convex_cone 𝕜 E} {a : E} :
  a ∈ K.closure ↔ a ∈ closure (K : set E) := iff.rfl

@[simp] lemma closure_eq {K L : convex_cone 𝕜 E} : K.closure = L ↔ closure (K : set E) = L :=
set_like.ext'_iff

end convex_cone

/-- A proper cone is a convex cone `K` that is nonempty and closed. Proper cones have the nice
property that the dual of the dual of a proper cone is itself. This makes them useful for defining
cone programs and proving duality theorems. -/
structure proper_cone (𝕜 : Type*) (E : Type*)
  [ordered_semiring 𝕜] [add_comm_monoid E] [topological_space E] [has_smul 𝕜 E]
  extends convex_cone 𝕜 E :=
(nonempty'  : (carrier : set E).nonempty)
(is_closed' : is_closed (carrier : set E))

namespace proper_cone

section has_smul

variables {𝕜 : Type*} [ordered_semiring 𝕜]
variables {E : Type*} [add_comm_monoid E] [topological_space E] [has_smul 𝕜 E]

instance : has_coe (proper_cone 𝕜 E) (convex_cone 𝕜 E) := ⟨λ K, K.1⟩

@[simp] lemma to_convex_cone_eq_coe (K : proper_cone 𝕜 E) : K.to_convex_cone = K := rfl

lemma ext' : function.injective (coe : proper_cone 𝕜 E → convex_cone 𝕜 E) :=
λ S T h, by cases S; cases T; congr'

-- TODO: add convex_cone_class that extends set_like and replace the below instance
instance : set_like (proper_cone 𝕜 E) E :=
{ coe := λ K, K.carrier,
  coe_injective' := λ _ _ h, proper_cone.ext' (set_like.coe_injective h) }

@[ext] lemma ext {S T : proper_cone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

@[simp] lemma mem_coe {x : E} {K : proper_cone 𝕜 E} : x ∈ (K : convex_cone 𝕜 E) ↔ x ∈ K := iff.rfl

protected lemma nonempty (K : proper_cone 𝕜 E) : (K : set E).nonempty := K.nonempty'

protected lemma is_closed (K : proper_cone 𝕜 E) : is_closed (K : set E) := K.is_closed'

end has_smul

section module

variables {𝕜 : Type*} [ordered_semiring 𝕜]
variables {E : Type*} [add_comm_monoid E] [topological_space E] [t1_space E] [module 𝕜 E]

instance : has_zero (proper_cone 𝕜 E) :=
⟨ { to_convex_cone := 0,
    nonempty' := ⟨0, rfl⟩,
    is_closed' := is_closed_singleton } ⟩

instance : inhabited (proper_cone 𝕜 E) := ⟨0⟩

@[simp] lemma mem_zero (x : E) : x ∈ (0 : proper_cone 𝕜 E) ↔ x = 0 := iff.rfl
@[simp, norm_cast] lemma coe_zero : ↑(0 : proper_cone 𝕜 E) = (0 : convex_cone 𝕜 E) := rfl

lemma pointed_zero : (0 : proper_cone 𝕜 E).pointed := by simp [convex_cone.pointed_zero]

end module

section inner_product_space

variables {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E]
variables {F : Type*} [normed_add_comm_group F] [inner_product_space ℝ F]
variables {G : Type*} [normed_add_comm_group G] [inner_product_space ℝ G]

protected lemma pointed (K : proper_cone ℝ E) : (K : convex_cone ℝ E).pointed :=
(K : convex_cone ℝ E).pointed_of_nonempty_of_is_closed K.nonempty K.is_closed

/-- The closure of image of a proper cone under a continuous `ℝ`-linear map is a proper cone. We
use continuous maps here so that the comap of f is also a map between proper cones. -/
noncomputable def map (f : E →L[ℝ] F) (K : proper_cone ℝ E) : proper_cone ℝ F :=
{ to_convex_cone := convex_cone.closure (convex_cone.map (f : E →ₗ[ℝ] F) ↑K),
  nonempty' := ⟨ 0, subset_closure $ set_like.mem_coe.2 $ convex_cone.mem_map.2
    ⟨0, K.pointed, map_zero _⟩ ⟩,
  is_closed' := is_closed_closure }

@[simp, norm_cast] lemma coe_map (f : E →L[ℝ] F) (K : proper_cone ℝ E) :
  ↑(K.map f) = (convex_cone.map (f : E →ₗ[ℝ] F) ↑K).closure := rfl

@[simp] lemma mem_map {f : E →L[ℝ] F} {K : proper_cone ℝ E} {y : F} :
  y ∈ K.map f ↔ y ∈ (convex_cone.map (f : E →ₗ[ℝ] F) ↑K).closure := iff.rfl

@[simp] lemma map_id (K : proper_cone ℝ E) : K.map (continuous_linear_map.id ℝ E) = K :=
proper_cone.ext' $ by simpa using is_closed.closure_eq K.is_closed

/-- The inner dual cone of a proper cone is a proper cone. -/
def dual (K : proper_cone ℝ E): (proper_cone ℝ E) :=
{ to_convex_cone := (K : set E).inner_dual_cone,
  nonempty' := ⟨0, pointed_inner_dual_cone _⟩,
  is_closed' := is_closed_inner_dual_cone _ }

@[simp, norm_cast]
lemma coe_dual (K : proper_cone ℝ E) : ↑(dual K) = (K : set E).inner_dual_cone := rfl

@[simp] lemma mem_dual {K : proper_cone ℝ E} {y : E} :
  y ∈ dual K ↔ ∀ ⦃x⦄, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ :=
by {rw [← mem_coe, coe_dual, mem_inner_dual_cone _ _], refl}

/-- The preimage of a proper cone under a continuous `ℝ`-linear map is a proper cone. -/
noncomputable def comap (f : E →L[ℝ] F) (S : proper_cone ℝ F) : proper_cone ℝ E :=
{ to_convex_cone := convex_cone.comap (f : E →ₗ[ℝ] F) S,
  nonempty' := ⟨ 0,
  begin
    simp only [convex_cone.comap, mem_preimage, map_zero, set_like.mem_coe, mem_coe],
    apply proper_cone.pointed,
  end ⟩,
  is_closed' :=
  begin
    simp only [convex_cone.comap, continuous_linear_map.coe_coe],
    apply is_closed.preimage f.2 S.is_closed,
  end }

@[simp] lemma coe_comap (f : E →L[ℝ] F) (S : proper_cone ℝ F) : (S.comap f : set E) = f ⁻¹' S :=
rfl

@[simp] lemma comap_id (S : convex_cone ℝ E) : S.comap linear_map.id = S :=
set_like.coe_injective preimage_id

lemma comap_comap (g : F →L[ℝ] G) (f : E →L[ℝ] F) (S : proper_cone ℝ G) :
  (S.comap g).comap f = S.comap (g.comp f) :=
set_like.coe_injective $ preimage_comp.symm

@[simp] lemma mem_comap {f : E →L[ℝ] F} {S : proper_cone ℝ F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
iff.rfl

end inner_product_space

section complete_space

variables {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E] [complete_space E]
variables {F : Type*} [normed_add_comm_group F] [inner_product_space ℝ F] [complete_space F]

/-- The dual of the dual of a proper cone is itself. -/
@[simp] theorem dual_dual (K : proper_cone ℝ E) : K.dual.dual = K := proper_cone.ext' $
  (K : convex_cone ℝ E).inner_dual_cone_of_inner_dual_cone_eq_self K.nonempty K.is_closed

/-- This is a relative version of
`convex_cone.hyperplane_separation_of_nonempty_of_is_closed_of_nmem`, which we recover by setting
`f` to be the identity map. This is a geometric interpretation of the Farkas' lemma
stated using proper cones. -/
theorem hyperplane_separation (K : proper_cone ℝ E) {f : E →L[ℝ] F} {b : F} :
  b ∈ K.map f ↔ ∀ y : F, (adjoint f y) ∈ K.dual → 0 ≤ ⟪y, b⟫_ℝ := iff.intro
begin
  -- suppose `b ∈ K.map f`
  simp only [proper_cone.mem_map, proper_cone.mem_dual, adjoint_inner_right,
    convex_cone.mem_closure, mem_closure_iff_seq_limit],

  -- there is a sequence `seq : ℕ → F` in the image of `f` that converges to `b`
  rintros ⟨seq, hmem, htends⟩ y hinner,

  suffices h : ∀ n, 0 ≤ ⟪y, seq n⟫_ℝ, from ge_of_tendsto' (continuous.seq_continuous
    (continuous.inner (@continuous_const _ _ _ _ y) continuous_id) htends) h,

  intro n,
  obtain ⟨_, h, hseq⟩ := hmem n,
  simpa only [← hseq, real_inner_comm] using (hinner h),
end
begin
  -- proof by contradiction
  -- suppose `b ∉ K.map f`
  intro h,
  contrapose! h,

  -- as `b ∉ K.map f`, there is a hyperplane `y` separating `b` from `K.map f`
  obtain ⟨y, hxy, hyb⟩ := convex_cone.hyperplane_separation_of_nonempty_of_is_closed_of_nmem _
    (K.map f).nonempty (K.map f).is_closed h,

  -- the rest of the proof is a straightforward algebraic manipulation
  refine ⟨y, _, hyb⟩,
  simp_rw [proper_cone.mem_dual, adjoint_inner_right],
  intros x hxK,
  apply hxy (f x),
  rw [to_convex_cone_eq_coe, proper_cone.coe_map],
  apply subset_closure,
  rw [set_like.mem_coe, convex_cone.mem_map],
  use ⟨x, hxK, rfl⟩,
end

theorem hyperplane_separation_of_nmem (K : proper_cone ℝ E) {f : E →L[ℝ] F} {b : F}
  (disj : b ∉ K.map f) : ∃ y : F, (adjoint f y) ∈ K.dual ∧ ⟪y, b⟫_ℝ < 0 :=
by { contrapose! disj, rwa K.hyperplane_separation }

end complete_space

end proper_cone
