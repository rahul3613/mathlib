/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.zmod.quotient

/-!
# Complements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the complement of a subgroup.

## Main definitions

- `is_complement S T` where `S` and `T` are subsets of `G` states that every `g : G` can be
 written uniquely as a product `s * t` for `s ∈ S`, `t ∈ T`.
- `left_transversals T` where `T` is a subset of `G` is the set of all left-complements of `T`,
 i.e. the set of all `S : set G` that contain exactly one element of each left coset of `T`.
- `right_transversals S` where `S` is a subset of `G` is the set of all right-complements of `S`,
 i.e. the set of all `T : set G` that contain exactly one element of each right coset of `S`.
- `transfer_transversal H g` is a specific `left_transversal` of `H` that is used in the
 computation of the transfer homomorphism evaluated at an element `g : G`.

## Main results

- `is_complement_of_coprime` : Subgroups of coprime order are complements.
-/

open_locale big_operators pointwise

namespace subgroup

variables {G : Type*} [group G] (H K : subgroup G) (S T : set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
 This notion generalizes left transversals, right transversals, and complementary subgroups. -/
@[to_additive "`S` and `T` are complements if `(*) : S × T → G` is a bijection"]
def is_complement : Prop := function.bijective (λ x : S × T, x.1.1 * x.2.1)

/-- `H` and `K` are complements if `(*) : H × K → G` is a bijection -/
@[to_additive "`H` and `K` are complements if `(*) : H × K → G` is a bijection"]
abbreviation is_complement' := is_complement (H : set G) (K : set G)

/-- The set of left-complements of `T : set G` -/
@[to_additive "The set of left-complements of `T : set G`"]
def left_transversals : set (set G) := {S : set G | is_complement S T}

/-- The set of right-complements of `S : set G` -/
@[to_additive "The set of right-complements of `S : set G`"]
def right_transversals : set (set G) := {T : set G | is_complement S T}

variables {H K S T}

@[to_additive] lemma is_complement'_def :
 is_complement' H K ↔ is_complement (H : set G) (K : set G) := iff.rfl

@[to_additive] lemma is_complement_iff_exists_unique :
 is_complement S T ↔ ∀ g : G, ∃! x : S × T, x.1.1 * x.2.1 = g :=
function.bijective_iff_exists_unique _

@[to_additive] lemma is_complement.exists_unique (h : is_complement S T) (g : G) :
 ∃! x : S × T, x.1.1 * x.2.1 = g :=
is_complement_iff_exists_unique.mp h g

@[to_additive] lemma is_complement'.symm (h : is_complement' H K) : is_complement' K H :=
begin
 let ϕ : H × K ≃ K × H := equiv.mk (λ x, ⟨x.2⁻¹, x.1⁻¹⟩) (λ x, ⟨x.2⁻¹, x.1⁻¹⟩)
 (λ x, prod.ext (inv_inv _) (inv_inv _)) (λ x, prod.ext (inv_inv _) (inv_inv _)),
 let ψ : G ≃ G := equiv.mk (λ g : G, g⁻¹) (λ g : G, g⁻¹) inv_inv inv_inv,
 suffices : ψ ∘ (λ x : H × K, x.1.1 * x.2.1) = (λ x : K × H, x.1.1 * x.2.1) ∘ ϕ,
 { rwa [is_complement'_def]; rwa [ is_complement]; rwa [ ←equiv.bijective_comp]; rwa [ ←this]; rwa [ equiv.comp_bijective] },
 exact funext (λ x, mul_inv_rev _ _),
end

@[to_additive] lemma is_complement'_comm : is_complement' H K ↔ is_complement' K H :=
⟨is_complement'.symm, is_complement'.symm⟩

@[to_additive] lemma is_complement_top_singleton {g : G} : is_complement (⊤ : set G) {g} :=
⟨λ ⟨x, _, rfl⟩ ⟨y, _, rfl⟩ h, prod.ext (subtype.ext (mul_right_cancel h)) rfl,
 λ x, ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩

@[to_additive] lemma is_complement_singleton_top {g : G} : is_complement ({g} : set G) ⊤ :=
⟨λ ⟨⟨_, rfl⟩, x⟩ ⟨⟨_, rfl⟩, y⟩ h, prod.ext rfl (subtype.ext (mul_left_cancel h)),
 λ x, ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩

@[to_additive] lemma is_complement_singleton_left {g : G} : is_complement {g} S ↔ S = ⊤ :=
begin
 refine ⟨λ h, top_le_iff.mp (λ x hx, _), λ h, (congr_arg _ h).mpr is_complement_singleton_top⟩,
 obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x),
 rwa ← mul_left_cancel hy,
end

@[to_additive] lemma is_complement_singleton_right {g : G} : is_complement S {g} ↔ S = ⊤ :=
begin
 refine ⟨λ h, top_le_iff.mp (λ x hx, _), λ h, (congr_arg _ h).mpr is_complement_top_singleton⟩,
 obtain ⟨y, hy⟩ := h.2 (x * g),
 conv_rhs at hy { rw ← (show y.2.1 = g, from y.2.2) },
 rw ← mul_right_cancel hy,
 exact y.1.2,
end

@[to_additive] lemma is_complement_top_left : is_complement ⊤ S ↔ ∃ g : G, S = {g} :=
begin
 refine ⟨λ h, set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, λ a ha b hb, _⟩, _⟩,
 { obtain ⟨a, ha⟩ := h.2 1,
 exact ⟨a.2.1, a.2.2⟩ },
 { have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
 h.1 ((inv_mul_self a).trans (inv_mul_self b).symm),
 exact subtype.ext_iff.mp ((prod.ext_iff.mp this).2) },
 { rintro ⟨g, rfl⟩,
 exact is_complement_top_singleton },
end

@[to_additive] lemma is_complement_top_right : is_complement S ⊤ ↔ ∃ g : G, S = {g} :=
begin
 refine ⟨λ h, set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, λ a ha b hb, _⟩, _⟩,
 { obtain ⟨a, ha⟩ := h.2 1,
 exact ⟨a.1.1, a.1.2⟩ },
 { have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
 h.1 ((mul_inv_self a).trans (mul_inv_self b).symm),
 exact subtype.ext_iff.mp ((prod.ext_iff.mp this).1) },
 { rintro ⟨g, rfl⟩,
 exact is_complement_singleton_top },
end

@[to_additive] lemma is_complement'_top_bot : is_complement' (⊤ : subgroup G) ⊥ :=
is_complement_top_singleton

@[to_additive] lemma is_complement'_bot_top : is_complement' (⊥ : subgroup G) ⊤ :=
is_complement_singleton_top

@[simp, to_additive] lemma is_complement'_bot_left : is_complement' ⊥ H ↔ H = ⊤ :=
is_complement_singleton_left.trans coe_eq_univ

@[simp, to_additive] lemma is_complement'_bot_right : is_complement' H ⊥ ↔ H = ⊤ :=
is_complement_singleton_right.trans coe_eq_univ

@[simp, to_additive] lemma is_complement'_top_left : is_complement' ⊤ H ↔ H = ⊥ :=
is_complement_top_left.trans coe_eq_singleton

@[simp, to_additive] lemma is_complement'_top_right : is_complement' H ⊤ ↔ H = ⊥ :=
is_complement_top_right.trans coe_eq_singleton

@[to_additive] lemma mem_left_transversals_iff_exists_unique_inv_mul_mem :
 S ∈ left_transversals T ↔ ∀ g : G, ∃! s : S, (s : G)⁻¹ * g ∈ T :=
begin
 rw [left_transversals]; rw [ set.mem_set_of_eq]; rw [ is_complement_iff_exists_unique],
 refine ⟨λ h g, _, λ h g, _⟩,
 { obtain ⟨x, h1, h2⟩ := h g,
 exact ⟨x.1, (congr_arg (∈ T) (eq_inv_mul_of_mul_eq h1)).mp x.2.2, λ y hy,
 (prod.ext_iff.mp (h2 ⟨y, y⁻¹ * g, hy⟩ (mul_inv_cancel_left y g))).1⟩ },
 { obtain ⟨x, h1, h2⟩ := h g,
 refine ⟨⟨x, x⁻¹ * g, h1⟩, mul_inv_cancel_left x g, λ y hy, _⟩,
 have := h2 y.1 ((congr_arg (∈ T) (eq_inv_mul_of_mul_eq hy)).mp y.2.2),
 exact prod.ext this (subtype.ext (eq_inv_mul_of_mul_eq ((congr_arg _ this).mp hy))) },
end

@[to_additive] lemma mem_right_transversals_iff_exists_unique_mul_inv_mem :
 S ∈ right_transversals T ↔ ∀ g : G, ∃! s : S, g * (s : G)⁻¹ ∈ T :=
begin
 rw [right_transversals]; rw [ set.mem_set_of_eq]; rw [ is_complement_iff_exists_unique],
 refine ⟨λ h g, _, λ h g, _⟩,
 { obtain ⟨x, h1, h2⟩ := h g,
 exact ⟨x.2, (congr_arg (∈ T) (eq_mul_inv_of_mul_eq h1)).mp x.1.2, λ y hy,
 (prod.ext_iff.mp (h2 ⟨⟨g * y⁻¹, hy⟩, y⟩ (inv_mul_cancel_right g y))).2⟩ },
 { obtain ⟨x, h1, h2⟩ := h g,
 refine ⟨⟨⟨g * x⁻¹, h1⟩, x⟩, inv_mul_cancel_right g x, λ y hy, _⟩,
 have := h2 y.2 ((congr_arg (∈ T) (eq_mul_inv_of_mul_eq hy)).mp y.1.2),
 exact prod.ext (subtype.ext (eq_mul_inv_of_mul_eq ((congr_arg _ this).mp hy))) this },
end

@[to_additive] lemma mem_left_transversals_iff_exists_unique_quotient_mk'_eq :
 S ∈ left_transversals (H : set G) ↔
 ∀ q : quotient (quotient_group.left_rel H), ∃! s : S, quotient.mk' s.1 = q :=
begin
 simp_rw [mem_left_transversals_iff_exists_unique_inv_mul_mem, set_like.mem_coe, ← quotient_group.eq'],
 exact ⟨λ h q, quotient.induction_on' q h, λ h g, h (quotient.mk' g)⟩,
end

@[to_additive] lemma mem_right_transversals_iff_exists_unique_quotient_mk'_eq :
 S ∈ right_transversals (H : set G) ↔
 ∀ q : quotient (quotient_group.right_rel H), ∃! s : S, quotient.mk' s.1 = q :=
begin
 simp_rw [mem_right_transversals_iff_exists_unique_mul_inv_mem, set_like.mem_coe, ← quotient_group.right_rel_apply, ← quotient.eq'],
 exact ⟨λ h q, quotient.induction_on' q h, λ h g, h (quotient.mk' g)⟩,
end

@[to_additive] lemma mem_left_transversals_iff_bijective : S ∈ left_transversals (H : set G) ↔
 function.bijective (S.restrict (quotient.mk' : G → quotient (quotient_group.left_rel H))) :=
mem_left_transversals_iff_exists_unique_quotient_mk'_eq.trans
 (function.bijective_iff_exists_unique (S.restrict quotient.mk')).symm

@[to_additive] lemma mem_right_transversals_iff_bijective : S ∈ right_transversals (H : set G) ↔
 function.bijective (S.restrict (quotient.mk' : G → quotient (quotient_group.right_rel H))) :=
mem_right_transversals_iff_exists_unique_quotient_mk'_eq.trans
 (function.bijective_iff_exists_unique (S.restrict quotient.mk')).symm

@[to_additive] lemma card_left_transversal (h : S ∈ left_transversals (H : set G)) :
 nat.card S = H.index :=
nat.card_congr $ equiv.of_bijective _ $ mem_left_transversals_iff_bijective.mp h

@[to_additive] lemma card_right_transversal (h : S ∈ right_transversals (H : set G)) :
 nat.card S = H.index :=
nat.card_congr $ (equiv.of_bijective _ $ mem_right_transversals_iff_bijective.mp h).trans $
 quotient_group.quotient_right_rel_equiv_quotient_left_rel H

@[to_additive] lemma range_mem_left_transversals {f : G ⧸ H → G} (hf : ∀ q, ↑(f q) = q) :
 set.range f ∈ left_transversals (H : set G) :=
mem_left_transversals_iff_bijective.mpr ⟨by rintros ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h;
 exact congr_arg _ (((hf q₁).symm.trans h).trans (hf q₂)), λ q, ⟨⟨f q, q, rfl⟩, hf q⟩⟩

@[to_additive] lemma range_mem_right_transversals {f : quotient (quotient_group.right_rel H) → G}
 (hf : ∀ q, quotient.mk' (f q) = q) : set.range f ∈ right_transversals (H : set G) :=
mem_right_transversals_iff_bijective.mpr ⟨by rintros ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h;
 exact congr_arg _ (((hf q₁).symm.trans h).trans (hf q₂)), λ q, ⟨⟨f q, q, rfl⟩, hf q⟩⟩

@[to_additive] lemma exists_left_transversal (g : G) :
 ∃ S ∈ left_transversals (H : set G), g ∈ S :=
begin
 classical,
 refine ⟨set.range (function.update quotient.out' ↑g g), range_mem_left_transversals (λ q, _),
 g, function.update_same g g quotient.out'⟩,
 by_cases hq : q = g,
 { exact hq.symm ▸ congr_arg _ (function.update_same g g quotient.out') },
 { exact eq.trans (congr_arg _ (function.update_noteq hq g quotient.out')) q.out_eq' },
end

@[to_additive] lemma exists_right_transversal (g : G) :
 ∃ S ∈ right_transversals (H : set G), g ∈ S :=
begin
 classical,
 refine ⟨set.range (function.update quotient.out' _ g), range_mem_right_transversals (λ q, _),
 quotient.mk' g, function.update_same (quotient.mk' g) g quotient.out'⟩,
 by_cases hq : q = quotient.mk' g,
 { exact hq.symm ▸ congr_arg _ (function.update_same (quotient.mk' g) g quotient.out') },
 { exact eq.trans (congr_arg _ (function.update_noteq hq g quotient.out')) q.out_eq' },
end

namespace mem_left_transversals

/-- A left transversal is in bijection with left cosets. -/
@[to_additive "A left transversal is in bijection with left cosets."]
noncomputable def to_equiv (hS : S ∈ subgroup.left_transversals (H : set G)) : G ⧸ H ≃ S :=
(equiv.of_bijective _ (subgroup.mem_left_transversals_iff_bijective.mp hS)).symm

@[to_additive] lemma mk'_to_equiv (hS : S ∈ subgroup.left_transversals (H : set G)) (q : G ⧸ H) :
 quotient.mk' (to_equiv hS q : G) = q :=
(to_equiv hS).symm_apply_apply q

@[to_additive] lemma to_equiv_apply {f : G ⧸ H → G} (hf : ∀ q, (f q : G ⧸ H) = q) (q : G ⧸ H) :
 (to_equiv (range_mem_left_transversals hf) q : G) = f q :=
begin
 refine (subtype.ext_iff.mp _).trans (subtype.coe_mk (f q) ⟨q, rfl⟩),
 exact (to_equiv (range_mem_left_transversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm,
end

/-- A left transversal can be viewed as a function mapping each element of the group
 to the chosen representative from that left coset. -/
@[to_additive "A left transversal can be viewed as a function mapping each element of the group
 to the chosen representative from that left coset."]
noncomputable def to_fun (hS : S ∈ subgroup.left_transversals (H : set G)) : G → S :=
to_equiv hS ∘ quotient.mk'

@[to_additive] lemma inv_to_fun_mul_mem (hS : S ∈ subgroup.left_transversals (H : set G))
 (g : G) : (to_fun hS g : G)⁻¹ * g ∈ H :=
quotient_group.left_rel_apply.mp $ quotient.exact' $ mk'_to_equiv _ _

@[to_additive] lemma inv_mul_to_fun_mem (hS : S ∈ subgroup.left_transversals (H : set G))
 (g : G) : g⁻¹ * to_fun hS g ∈ H :=
(congr_arg (∈ H) (by rw [mul_inv_rev]; rw [ inv_inv])).mp (H.inv_mem (inv_to_fun_mul_mem hS g))

end mem_left_transversals

namespace mem_right_transversals

/-- A right transversal is in bijection with right cosets. -/
@[to_additive "A right transversal is in bijection with right cosets."]
noncomputable def to_equiv (hS : S ∈ subgroup.right_transversals (H : set G)) :
 quotient (quotient_group.right_rel H) ≃ S :=
(equiv.of_bijective _ (subgroup.mem_right_transversals_iff_bijective.mp hS)).symm

@[to_additive] lemma mk'_to_equiv (hS : S ∈ subgroup.right_transversals (H : set G))
 (q : quotient (quotient_group.right_rel H)) : quotient.mk' (to_equiv hS q : G) = q :=
(to_equiv hS).symm_apply_apply q

@[to_additive] lemma to_equiv_apply {f : quotient (quotient_group.right_rel H) → G}
 (hf : ∀ q, quotient.mk' (f q) = q) (q : quotient (quotient_group.right_rel H)) :
 (to_equiv (range_mem_right_transversals hf) q : G) = f q :=
begin
 refine (subtype.ext_iff.mp _).trans (subtype.coe_mk (f q) ⟨q, rfl⟩),
 exact (to_equiv (range_mem_right_transversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm,
end

/-- A right transversal can be viewed as a function mapping each element of the group
 to the chosen representative from that right coset. -/
@[to_additive "A right transversal can be viewed as a function mapping each element of the group
 to the chosen representative from that right coset."]
noncomputable def to_fun (hS : S ∈ subgroup.right_transversals (H : set G)) : G → S :=
to_equiv hS ∘ quotient.mk'

@[to_additive] lemma mul_inv_to_fun_mem (hS : S ∈ subgroup.right_transversals (H : set G))
 (g : G) : g * (to_fun hS g : G)⁻¹ ∈ H :=
quotient_group.right_rel_apply.mp $ quotient.exact' $ mk'_to_equiv _ _

@[to_additive] lemma to_fun_mul_inv_mem (hS : S ∈ subgroup.right_transversals (H : set G))
 (g : G) : (to_fun hS g : G) * g⁻¹ ∈ H :=
(congr_arg (∈ H) (by rw [mul_inv_rev]; rw [ inv_inv])).mp (H.inv_mem (mul_inv_to_fun_mem hS g))

end mem_right_transversals

section action

open_locale pointwise

open mul_action mem_left_transversals

variables {F : Type*} [group F] [mul_action F G] [quotient_action F H]

@[to_additive] instance : mul_action F (left_transversals (H : set G)) :=
{ smul := λ f T, ⟨f • T, by
 { refine mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g, _),
 obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (f⁻¹ • g),
 refine ⟨⟨f • t, set.smul_mem_smul_set t.2⟩, _, _⟩,
 { exact (congr_arg _ (smul_inv_smul f g)).mp (quotient_action.inv_mul_mem f ht1) },
 { rintros ⟨-, t', ht', rfl⟩ h,
 replace h := quotient_action.inv_mul_mem f⁻¹ h,
 simp only [subtype.ext_iff, subtype.coe_mk, smul_left_cancel_iff, inv_smul_smul] at h ⊢,
 exact subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h) } }⟩,
 one_smul := λ T, subtype.ext (one_smul F T),
 mul_smul := λ f₁ f₂ T, subtype.ext (mul_smul f₁ f₂ T) }

@[to_additive] lemma smul_to_fun (f : F) (T : left_transversals (H : set G)) (g : G) :
 (f • to_fun T.2 g : G) = to_fun (f • T).2 (f • g) :=
subtype.ext_iff.mp $ @unique_of_exists_unique ↥(f • T) (λ s, (↑s)⁻¹ * f • g ∈ H)
 (mem_left_transversals_iff_exists_unique_inv_mul_mem.mp (f • T).2 (f • g))
 ⟨f • to_fun T.2 g, set.smul_mem_smul_set (subtype.coe_prop _)⟩ (to_fun (f • T).2 (f • g))
 (quotient_action.inv_mul_mem f (inv_to_fun_mul_mem T.2 g)) (inv_to_fun_mul_mem (f • T).2 (f • g))

@[to_additive] lemma smul_to_equiv (f : F) (T : left_transversals (H : set G)) (q : G ⧸ H) :
 f • (to_equiv T.2 q : G) = to_equiv (f • T).2 (f • q) :=
quotient.induction_on' q (λ g, smul_to_fun f T g)

@[to_additive] lemma smul_apply_eq_smul_apply_inv_smul (f : F) (T : left_transversals (H : set G))
 (q : G ⧸ H) : (to_equiv (f • T).2 q : G) = f • (to_equiv T.2 (f⁻¹ • q) : G) :=
by rw [smul_to_equiv]; rw [ smul_inv_smul]

end action

@[to_additive] instance : inhabited (left_transversals (H : set G)) :=
⟨⟨set.range quotient.out', range_mem_left_transversals quotient.out_eq'⟩⟩

@[to_additive] instance : inhabited (right_transversals (H : set G)) :=
⟨⟨set.range quotient.out', range_mem_right_transversals quotient.out_eq'⟩⟩

lemma is_complement'.is_compl (h : is_complement' H K) : is_compl H K :=
begin
 refine ⟨disjoint_iff_inf_le.mpr $
 λ g ⟨p, q⟩, let x : H × K := ⟨⟨g, p⟩, 1⟩, y : H × K := ⟨1, g, q⟩ in subtype.ext_iff.mp
 (prod.ext_iff.mp (show x = y, from h.1 ((mul_one g).trans (one_mul g).symm))).1,
 codisjoint_iff_le_sup.mpr $ λ g _, _⟩,
 obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g,
 exact subgroup.mul_mem_sup h.2 k.2,
end

lemma is_complement'.sup_eq_top (h : is_complement' H K) : H ⊔ K = ⊤ :=
h.is_compl.sup_eq_top

lemma is_complement'.disjoint (h : is_complement' H K) : disjoint H K :=
h.is_compl.disjoint

lemma is_complement'.index_eq_card (h : is_complement' H K) : K.index = nat.card H :=
(card_left_transversal h).symm

lemma is_complement.card_mul [fintype G] [fintype S] [fintype T] (h : is_complement S T) :
 fintype.card S * fintype.card T = fintype.card G :=
(fintype.card_prod _ _).symm.trans (fintype.card_of_bijective h)

lemma is_complement'.card_mul [fintype G] [fintype H] [fintype K] (h : is_complement' H K) :
 fintype.card H * fintype.card K = fintype.card G :=
h.card_mul

lemma is_complement'_of_disjoint_and_mul_eq_univ
 (h1 : disjoint H K) (h2 : ↑H * ↑K = (set.univ : set G)) : is_complement' H K :=
begin
 refine ⟨mul_injective_of_disjoint h1, λ g, _⟩,
 obtain ⟨h, k, hh, hk, hg⟩ := set.eq_univ_iff_forall.mp h2 g,
 exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hg⟩,
end

lemma is_complement'_of_card_mul_and_disjoint [fintype G] [fintype H] [fintype K]
 (h1 : fintype.card H * fintype.card K = fintype.card G) (h2 : disjoint H K) :
 is_complement' H K :=
(fintype.bijective_iff_injective_and_card _).mpr
 ⟨mul_injective_of_disjoint h2, (fintype.card_prod H K).trans h1⟩

lemma is_complement'_iff_card_mul_and_disjoint [fintype G] [fintype H] [fintype K] :
 is_complement' H K ↔
 fintype.card H * fintype.card K = fintype.card G ∧ disjoint H K :=
⟨λ h, ⟨h.card_mul, h.disjoint⟩, λ h, is_complement'_of_card_mul_and_disjoint h.1 h.2⟩

lemma is_complement'_of_coprime [fintype G] [fintype H] [fintype K]
 (h1 : fintype.card H * fintype.card K = fintype.card G)
 (h2 : nat.coprime (fintype.card H) (fintype.card K)) :
 is_complement' H K :=
is_complement'_of_card_mul_and_disjoint h1 (disjoint_iff.mpr (inf_eq_bot_of_coprime h2))

lemma is_complement'_stabilizer {α : Type*} [mul_action G α] (a : α)
 (h1 : ∀ (h : H), h • a = a → h = 1) (h2 : ∀ g : G, ∃ h : H, h • (g • a) = a) :
 is_complement' H (mul_action.stabilizer G a) :=
begin
 refine is_complement_iff_exists_unique.mpr (λ g, _),
 obtain ⟨h, hh⟩ := h2 g,
 have hh' : (↑h * g) • a = a := by rwa [mul_smul],
 refine ⟨⟨h⁻¹, h * g, hh'⟩, inv_mul_cancel_left h g, _⟩,
 rintros ⟨h', g, hg : g • a = a⟩ rfl,
 specialize h1 (h * h') (by rwa [mul_smul]; rwa [ smul_def h']; rwa [ ←hg]; rwa [ ←mul_smul]; rwa [ hg]),
 refine prod.ext (eq_inv_of_mul_eq_one_right h1) (subtype.ext _),
 rwa [subtype.ext_iff] at h1; rwa [ coe_one] at h1; rwa [ coe_mul] at h1; rwa [ ←self_eq_mul_left] at h1; rwa [ mul_assoc ↑h ↑h' g] at h1,
end

end subgroup

namespace subgroup

open equiv function mem_left_transversals mul_action mul_action.quotient zmod

universe u

variables {G : Type u} [group G] (H : subgroup G) (g : G)

/-- Partition `G ⧸ H` into orbits of the action of `g : G`. -/
noncomputable def quotient_equiv_sigma_zmod : G ⧸ H ≃
 Σ (q : orbit_rel.quotient (zpowers g) (G ⧸ H)), zmod (minimal_period ((•) g) q.out') :=
(self_equiv_sigma_orbits (zpowers g) (G ⧸ H)).trans
 (sigma_congr_right (λ q, orbit_zpowers_equiv g q.out'))

lemma quotient_equiv_sigma_zmod_symm_apply
 (q : orbit_rel.quotient (zpowers g) (G ⧸ H)) (k : zmod (minimal_period ((•) g) q.out')) :
 (quotient_equiv_sigma_zmod H g).symm ⟨q, k⟩ = g ^ (k : ℤ) • q.out' :=
rfl

lemma quotient_equiv_sigma_zmod_apply (q : orbit_rel.quotient (zpowers g) (G ⧸ H)) (k : ℤ) :
 quotient_equiv_sigma_zmod H g (g ^ k • q.out') = ⟨q, k⟩ :=
by rw [apply_eq_iff_eq_symm_apply]; rw [ quotient_equiv_sigma_zmod_symm_apply]; rw [ zmod.coe_int_cast]; rw [ zpow_smul_mod_minimal_period]

/-- The transfer transversal as a function. Given a `⟨g⟩`-orbit `q₀, g • q₀, ..., g ^ (m - 1) • q₀`
 in `G ⧸ H`, an element `g ^ k • q₀` is mapped to `g ^ k • g₀` for a fixed choice of
 representative `g₀` of `q₀`. -/
noncomputable def transfer_function : G ⧸ H → G :=
λ q, g ^ ((quotient_equiv_sigma_zmod H g q).2 : ℤ) * (quotient_equiv_sigma_zmod H g q).1.out'.out'

lemma transfer_function_apply (q : G ⧸ H) : transfer_function H g q =
 g ^ ((quotient_equiv_sigma_zmod H g q).2 : ℤ) * (quotient_equiv_sigma_zmod H g q).1.out'.out' :=
rfl

lemma coe_transfer_function (q : G ⧸ H) : ↑(transfer_function H g q) = q :=
by rw [transfer_function_apply]; rw [ ←smul_eq_mul]; rw [ coe_smul_out']; rw [ ←quotient_equiv_sigma_zmod_symm_apply]; rw [ sigma.eta]; rw [ symm_apply_apply]

/-- The transfer transversal as a set. Contains elements of the form `g ^ k • g₀` for fixed choices
 of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transfer_set : set G :=
set.range (transfer_function H g)

lemma mem_transfer_set (q : G ⧸ H) : transfer_function H g q ∈ transfer_set H g :=
⟨q, rfl⟩

/-- The transfer transversal. Contains elements of the form `g ^ k • g₀` for fixed choices
 of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transfer_transversal : left_transversals (H : set G) :=
⟨transfer_set H g, range_mem_left_transversals (coe_transfer_function H g)⟩

lemma transfer_transversal_apply (q : G ⧸ H) :
 ↑(to_equiv (transfer_transversal H g).2 q) = transfer_function H g q :=
to_equiv_apply (coe_transfer_function H g) q

lemma transfer_transversal_apply'
 (q : orbit_rel.quotient (zpowers g) (G ⧸ H)) (k : zmod (minimal_period ((•) g) q.out')) :
 ↑(to_equiv (transfer_transversal H g).2 (g ^ (k : ℤ) • q.out')) = g ^ (k : ℤ) * q.out'.out' :=
by rw [transfer_transversal_apply]; rw [ transfer_function_apply]; rw [ ←quotient_equiv_sigma_zmod_symm_apply]; rw [ apply_symm_apply]

lemma transfer_transversal_apply''
 (q : orbit_rel.quotient (zpowers g) (G ⧸ H)) (k : zmod (minimal_period ((•) g) q.out')) :
 ↑(to_equiv (g • transfer_transversal H g).2 (g ^ (k : ℤ) • q.out')) =
 if k = 0 then g ^ minimal_period ((•) g) q.out' * q.out'.out' else g ^ (k : ℤ) * q.out'.out' :=
begin
 rw [smul_apply_eq_smul_apply_inv_smul]; rw [ transfer_transversal_apply]; rw [ transfer_function_apply]; rw [ ←mul_smul]; rw [ ←zpow_neg_one]; rw [ ←zpow_add]; rw [ quotient_equiv_sigma_zmod_apply]; rw [ smul_eq_mul]; rw [ ←mul_assoc]; rw [ ←zpow_one_add]; rw [ int.cast_add]; rw [ int.cast_neg]; rw [ int.cast_one]; rw [ int_cast_cast]; rw [ cast_id']; rw [ id.def]; rw [ ←sub_eq_neg_add]; rw [ cast_sub_one]; rw [ add_sub_cancel'_right],
 by_cases hk : k = 0,
 { rw [if_pos hk]; rw [ if_pos hk]; rw [ zpow_coe_nat] },
 { rw [if_neg hk]; rw [ if_neg hk] },
end

end subgroup

