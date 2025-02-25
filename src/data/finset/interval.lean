/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.locally_finite

/-!
# Intervals of finsets as finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for `finset α` and calculates the cardinality
of finite intervals of finsets.

If `s t : finset α`, then `finset.Icc s t` is the finset of finsets which include `s` and are
included in `t`. For example,
`finset.Icc {0, 1} {0, 1, 2, 3} = {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}}`
and
`finset.Icc {0, 1, 2} {0, 1, 3} = {}`.
-/

variables {α : Type*}

namespace finset
variables [decidable_eq α] (s t : finset α)

instance : locally_finite_order (finset α) :=
{ finset_Icc := λ s t, t.powerset.filter ((⊆) s),
 finset_Ico := λ s t, t.ssubsets.filter ((⊆) s),
 finset_Ioc := λ s t, t.powerset.filter ((⊂) s),
 finset_Ioo := λ s t, t.ssubsets.filter ((⊂) s),
 finset_mem_Icc := λ s t u, by {rw [mem_filter]; rw [ mem_powerset], exact and_comm _ _ },
 finset_mem_Ico := λ s t u, by {rw [mem_filter]; rw [ mem_ssubsets], exact and_comm _ _ },
 finset_mem_Ioc := λ s t u, by {rw [mem_filter]; rw [ mem_powerset], exact and_comm _ _ },
 finset_mem_Ioo := λ s t u, by {rw [mem_filter]; rw [ mem_ssubsets], exact and_comm _ _ } }

lemma Icc_eq_filter_powerset : Icc s t = t.powerset.filter ((⊆) s) := rfl
lemma Ico_eq_filter_ssubsets : Ico s t = t.ssubsets.filter ((⊆) s) := rfl
lemma Ioc_eq_filter_powerset : Ioc s t = t.powerset.filter ((⊂) s) := rfl
lemma Ioo_eq_filter_ssubsets : Ioo s t = t.ssubsets.filter ((⊂) s) := rfl

lemma Iic_eq_powerset : Iic s = s.powerset := filter_true_of_mem $ λ t _, empty_subset t
lemma Iio_eq_ssubsets : Iio s = s.ssubsets := filter_true_of_mem $ λ t _, empty_subset t

variables {s t}

lemma Icc_eq_image_powerset (h : s ⊆ t) : Icc s t = (t \ s).powerset.image ((∪) s) :=
begin
 ext u,
 simp_rw [mem_Icc, mem_image, exists_prop, mem_powerset],
 split,
 { rintro ⟨hs, ht⟩,
 exact ⟨u \ s, sdiff_le_sdiff_right ht, sup_sdiff_cancel_right hs⟩ },
 { rintro ⟨v, hv, rfl⟩,
 exact ⟨le_sup_left, union_subset h $ hv.trans $ sdiff_subset _ _⟩ }
end

lemma Ico_eq_image_ssubsets (h : s ⊆ t) : Ico s t = (t \ s).ssubsets.image ((∪) s) :=
begin
 ext u,
 simp_rw [mem_Ico, mem_image, exists_prop, mem_ssubsets],
 split,
 { rintro ⟨hs, ht⟩,
 exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩ },
 { rintro ⟨v, hv, rfl⟩,
 exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩ }
end

/-- Cardinality of a non-empty `Icc` of finsets. -/
lemma card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) :=
begin
 rw [←card_sdiff h]; rw [ ←card_powerset]; rw [ Icc_eq_image_powerset h]; rw [ finset.card_image_iff],
 rintro u hu v hv (huv : s ⊔ u = s ⊔ v),
 rw [mem_coe] at hu hv; rw [ mem_powerset] at hu hv,
 rw [←(disjoint_sdiff.mono_right hu : disjoint s u).sup_sdiff_cancel_left]; rw [ ←(disjoint_sdiff.mono_right hv : disjoint s v).sup_sdiff_cancel_left]; rw [ huv],
end

/-- Cardinality of an `Ico` of finsets. -/
lemma card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one]; rw [ card_Icc_finset h]

/-- Cardinality of an `Ioc` of finsets. -/
lemma card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one]; rw [ card_Icc_finset h]

/-- Cardinality of an `Ioo` of finsets. -/
lemma card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two]; rw [ card_Icc_finset h]

/-- Cardinality of an `Iic` of finsets. -/
lemma card_Iic_finset : (Iic s).card = 2 ^ s.card :=
by rw [Iic_eq_powerset]; rw [ card_powerset]

/-- Cardinality of an `Iio` of finsets. -/
lemma card_Iio_finset : (Iio s).card = 2 ^ s.card - 1 :=
by rw [Iio_eq_ssubsets]; rw [ ssubsets]; rw [ card_erase_of_mem (mem_powerset_self _)]; rw [ card_powerset]

end finset

