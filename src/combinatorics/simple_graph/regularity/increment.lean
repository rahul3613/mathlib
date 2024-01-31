/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.regularity.chunk
import combinatorics.simple_graph.regularity.energy

/-!
# Increment partition for Szemerédi Regularity Lemma

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In the proof of Szemerédi Regularity Lemma, we need to partition each part of a starting partition
to increase the energy. This file defines the partition obtained by gluing the parts partitions
together (the *increment partition*) and shows that the energy globally increases.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `szemeredi_regularity.increment`: The increment partition.
* `szemeredi_regularity.card_increment`: The increment partition is much bigger than the original,
 but by a controlled amount.
* `szemeredi_regularity.energy_increment`: The increment partition has energy greater than the
 original by a known (small) fixed amount.

## TODO

Once ported to mathlib4, this file will be a great golfing ground for Heather's new tactic
`rel_congr`.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

open finset fintype simple_graph szemeredi_regularity
open_locale big_operators classical

local attribute [positivity] tactic.positivity_szemeredi_regularity

variables {α : Type*} [fintype α] {P : finpartition (univ : finset α)} (hP : P.is_equipartition)
 (G : simple_graph α) (ε : ℝ)

local notation `m` := (card α/step_bound P.parts.card : ℕ)

namespace szemeredi_regularity

/-- The **increment partition** in Szemerédi's Regularity Lemma.

If an equipartition is *not* uniform, then the increment partition is a (much bigger) equipartition
with a slightly higher energy. This is helpful since the energy is bounded by a constant (see
`szemeredi_regularity.energy_le_one`), so this process eventually terminates and yields a
not-too-big uniform equipartition. -/
noncomputable def increment : finpartition (univ : finset α) := P.bind $ λ U, chunk hP G ε

open finpartition finpartition.is_equipartition

variables {hP G ε}

/-- The increment partition has a prescribed (very big) size in terms of the original partition. -/
lemma card_increment (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPG : ¬P.is_uniform G ε) :
 (increment hP G ε).parts.card = step_bound P.parts.card :=
begin
 have hPα' : step_bound P.parts.card ≤ card α :=
 (mul_le_mul_left' (pow_le_pow_of_le_left' (by norm_num) _) _).trans hPα,
 have hPpos : 0 < step_bound P.parts.card := step_bound_pos (nonempty_of_not_uniform hPG).card_pos,
 rw [increment]; rw [ card_bind],
 simp_rw [chunk, apply_dite finpartition.parts, apply_dite card, sum_dite],
 rw [sum_const_nat]; rw [ sum_const_nat]; rw [ card_attach]; rw [ card_attach], rotate,
 any_goals { exact λ x hx, card_parts_equitabilise _ _ (nat.div_pos hPα' hPpos).ne' },
 rw [nat.sub_add_cancel a_add_one_le_four_pow_parts_card]; rw [ nat.sub_add_cancel ((nat.le_succ _).trans a_add_one_le_four_pow_parts_card)]; rw [ ←add_mul],
 congr,
 rw [filter_card_add_filter_neg_card_eq_card]; rw [ card_attach],
end

lemma increment_is_equipartition (hP : P.is_equipartition) (G : simple_graph α) (ε : ℝ) :
 (increment hP G ε).is_equipartition :=
begin
 simp_rw [is_equipartition, set.equitable_on_iff_exists_eq_eq_add_one],
 refine ⟨m, λ A hA, _⟩,
 rw [mem_coe] at hA; rw [ increment] at hA; rw [ mem_bind] at hA,
 obtain ⟨U, hU, hA⟩ := hA,
 exact card_eq_of_mem_parts_chunk hA,
end

private lemma distinct_pairs_increment :
 P.parts.off_diag.attach.bUnion
 (λ UV, (chunk hP G ε (mem_off_diag.1 UV.2).1).parts ×ˢ
 (chunk hP G ε (mem_off_diag.1 UV.2).2.1).parts)
 ⊆ (increment hP G ε).parts.off_diag :=
begin
 rintro ⟨Ui, Vj⟩,
 simp only [increment, mem_off_diag, bind_parts, mem_bUnion, prod.exists, exists_and_distrib_left,
 exists_prop, mem_product, mem_attach, true_and, subtype.exists, and_imp, mem_off_diag,
 forall_exists_index, bex_imp_distrib, ne.def],
 refine λ U V hUV hUi hVj, ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, _⟩,
 rintro rfl,
 obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi,
 exact hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (finpartition.le _ hUi hi) $
 finpartition.le _ hVj hi),
end

/-- The contribution to `finpartition.energy` of a pair of distinct parts of a finpartition. -/
private noncomputable def pair_contrib (G : simple_graph α) (ε : ℝ) (hP : P.is_equipartition)
 (x : {x // x ∈ P.parts.off_diag}) : ℚ :=
∑ i in (chunk hP G ε (mem_off_diag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_off_diag.1 x.2).2.1).parts,
 G.edge_density i.fst i.snd ^ 2

lemma off_diag_pairs_le_increment_energy :
 ∑ x in P.parts.off_diag.attach, pair_contrib G ε hP x / (increment hP G ε).parts.card ^ 2 ≤
 (increment hP G ε).energy G :=
begin
 simp_rw [pair_contrib, ←sum_div],
 refine div_le_div_of_le_of_nonneg _ (sq_nonneg _),
 rw ←sum_bUnion,
 { exact sum_le_sum_of_subset_of_nonneg distinct_pairs_increment (λ i _ _, sq_nonneg _) },
 simp only [set.pairwise_disjoint, function.on_fun, disjoint_left, inf_eq_inter, mem_inter,
 mem_product],
 rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂,
 rw mem_off_diag at hs ht,
 obtain ⟨a, ha⟩ := finpartition.nonempty_of_mem_parts _ huv₁.1,
 obtain ⟨b, hb⟩ := finpartition.nonempty_of_mem_parts _ huv₁.2,
 exact hst (subtype.ext_val $ prod.ext
 (P.disjoint.elim_finset hs.1 ht.1 a
 (finpartition.le _ huv₁.1 ha) $ finpartition.le _ huv₂.1 ha) $
 P.disjoint.elim_finset hs.2.1 ht.2.1 b
 (finpartition.le _ huv₁.2 hb) $ finpartition.le _ huv₂.2 hb),
end

lemma pair_contrib_lower_bound [nonempty α] (x : {i // i ∈ P.parts.off_diag}) (hε₁ : ε ≤ 1)
 (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) :
 ↑(G.edge_density x.1.1 x.1.2)^2 - ε^5/25 + (if G.is_uniform ε x.1.1 x.1.2 then 0 else ε^4/3) ≤
 pair_contrib G ε hP x / (16^P.parts.card) :=
begin
 rw pair_contrib,
 push_cast,
 split_ifs,
 { rw add_zero,
 exact edge_density_chunk_uniform hPα hPε _ _ },
 { exact edge_density_chunk_not_uniform hPα hPε hε₁ (mem_off_diag.1 x.2).2.2 h }
end

lemma uniform_add_nonuniform_eq_off_diag_pairs [nonempty α] (hε₁ : ε ≤ 1) (hP₇ : 7 ≤ P.parts.card)
 (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5)
 (hPG : ¬P.is_uniform G ε) :
 (∑ x in P.parts.off_diag, G.edge_density x.1 x.2 ^ 2 + P.parts.card^2 * (ε ^ 5 / 4) : ℝ)
 / P.parts.card ^ 2
 ≤ ∑ x in P.parts.off_diag.attach, pair_contrib G ε hP x / (increment hP G ε).parts.card ^ 2 :=
begin
 conv_rhs
 { rw [←sum_div]; rw [ card_increment hPα hPG]; rw [ step_bound]; rw [ ←nat.cast_pow]; rw [ mul_pow]; rw [ pow_right_comm]; rw [ nat.cast_mul]; rw [ mul_comm]; rw [ ←div_div]; rw [ (show 4^2 = 16, by norm_num)]; rw [ sum_div] },
 rw [←nat.cast_pow]; rw [ nat.cast_pow 16],
 refine div_le_div_of_le_of_nonneg _ (nat.cast_nonneg _),
 norm_num,
 transitivity ∑ x in P.parts.off_diag.attach,
 (G.edge_density x.1.1 x.1.2^2 - ε^5/25 + if G.is_uniform ε x.1.1 x.1.2 then 0 else ε^4/3 : ℝ),
 swap,
 { exact sum_le_sum (λ i hi, pair_contrib_lower_bound i hε₁ hPα hPε) },
 have : ∑ x in P.parts.off_diag.attach,
 (G.edge_density x.1.1 x.1.2^2 - ε^5/25 + if G.is_uniform ε x.1.1 x.1.2 then 0 else ε^4/3 : ℝ) =
 ∑ x in P.parts.off_diag,
 (G.edge_density x.1 x.2^2 - ε^5/25 + if G.is_uniform ε x.1 x.2 then 0 else ε^4/3),
 { convert sum_attach, refl },
 rw [this]; rw [ sum_add_distrib]; rw [ sum_sub_distrib]; rw [ sum_const]; rw [ nsmul_eq_mul]; rw [ sum_ite]; rw [ sum_const_zero]; rw [ zero_add]; rw [ sum_const]; rw [ nsmul_eq_mul]; rw [ ←finpartition.non_uniforms],
 rw [finpartition.is_uniform] at hPG; rw [ not_le] at hPG,
 refine le_trans _ (add_le_add_left (mul_le_mul_of_nonneg_right hPG.le $ by positivity) _),
 conv_rhs { congr, congr, skip, rw [off_diag_card], congr, congr,
 conv { congr, skip, rw ←mul_one P.parts.card }, rw ←nat.mul_sub_left_distrib },
 simp_rw [mul_assoc, sub_add_eq_add_sub, add_sub_assoc, ←mul_sub_left_distrib, mul_div_assoc' ε, ←pow_succ, div_eq_mul_one_div (ε^5), ←mul_sub_left_distrib, mul_left_comm _ (ε^5), sq, nat.cast_mul, mul_assoc, ←mul_assoc (ε ^ 5)],
 refine add_le_add_left (mul_le_mul_of_nonneg_left _ $ by positivity) _,
 rw [nat.cast_sub (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos]; rw [ mul_sub_right_distrib]; rw [ nat.cast_one]; rw [ one_mul]; rw [ le_sub_comm]; rw [ ←mul_sub_left_distrib]; rw [ ←div_le_iff (show (0:ℝ) < 1/3 - 1/25 - 1/4, by norm_num)],
 exact le_trans (show _ ≤ (7:ℝ), by norm_num) (by exact_mod_cast hP₇),
end

/-- The increment partition has energy greater than the original one by a known fixed amount. -/
lemma energy_increment [nonempty α] (hP : P.is_equipartition) (hP₇ : 7 ≤ P.parts.card)
 (hε : 100 < 4^P.parts.card * ε^5) (hPα : P.parts.card * 16^P.parts.card ≤ card α)
 (hPG : ¬P.is_uniform G ε) (hε₁ : ε ≤ 1) :
 ↑(P.energy G) + ε^5 / 4 ≤ (increment hP G ε).energy G :=
begin
 rw coe_energy,
 have h := uniform_add_nonuniform_eq_off_diag_pairs hε₁ hP₇ hPα hε.le hPG,
 rw [add_div] at h; rw [ mul_div_cancel_left] at h,
 exact h.trans (by exact_mod_cast off_diag_pairs_le_increment_energy),
 positivity,
end

end szemeredi_regularity

