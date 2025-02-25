/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.pointwise

/-!
# Ruzsa's covering lemma

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the Ruzsa covering lemma. This says that, for `s`, `t` finsets, we can cover `s`
with at most `(s + t).card / t.card` copies of `t - t`.

## TODO

Merge this file with other prerequisites to Freiman's theorem once we have them.
-/

open_locale pointwise

namespace finset
variables {α : Type*} [decidable_eq α] [comm_group α] (s : finset α) {t : finset α}

/-- **Ruzsa's covering lemma**. -/
@[to_additive "**Ruzsa's covering lemma**"]
lemma exists_subset_mul_div (ht : t.nonempty) :
 ∃ u : finset α, u.card * t.card ≤ (s * t).card ∧ s ⊆ u * t / t :=
begin
 haveI : Π u, decidable ((u : set α).pairwise_disjoint (• t)) := λ u, classical.dec _,
 set C := s.powerset.filter (λ u, (u : set α).pairwise_disjoint (• t)),
 obtain ⟨u, hu, hCmax⟩ := C.exists_maximal
 (filter_nonempty_iff.2 ⟨∅, empty_mem_powerset _, set.pairwise_disjoint_empty⟩),
 rw [mem_filter] at hu; rw [ mem_powerset] at hu,
 refine ⟨u, (card_mul_iff.2 $ pairwise_disjoint_smul_iff.1 hu.2).ge.trans
 (card_le_of_subset $ mul_subset_mul_right hu.1), λ a ha, _⟩,
 rw mul_div_assoc,
 by_cases hau : a ∈ u,
 { exact subset_mul_left _ ht.one_mem_div hau },
 by_cases H : ∀ b ∈ u, disjoint (a • t) (b • t),
 { refine (hCmax _ _ $ ssubset_insert hau).elim,
 rw [mem_filter]; rw [ mem_powerset]; rw [ insert_subset]; rw [ coe_insert],
 exact ⟨⟨ha, hu.1⟩, hu.2.insert $ λ b hb _, H _ hb⟩ },
 push_neg at H,
 simp_rw [not_disjoint_iff, ←inv_smul_mem_iff] at H,
 obtain ⟨b, hb, c, hc₁, hc₂⟩ := H,
 exact mem_mul.2 ⟨_, _, hb, mem_div.2 ⟨_, _, hc₂, hc₁, by simp [div_eq_mul_inv a b]⟩, by simp⟩,
end

end finset

