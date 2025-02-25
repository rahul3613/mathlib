/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.special_functions.pow.nnreal

/-!
# Convergence of `p`-series

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`nnreal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## TODO

It should be easy to generalize arguments to Schlömilch's generalization of the Cauchy condensation
test once we need it.

## Tags

p-series, Cauchy condensation test
-/

open filter
open_locale big_operators ennreal nnreal topology

/-!
### Cauchy condensation test

In this section we prove the Cauchy condensation test: for `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`,
`∑ k, f k` converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. Instead of giving a monolithic
proof, we split it into a series of lemmas with explicit estimates of partial sums of each series in
terms of the partial sums of the other series.
-/

namespace finset

variables {M : Type*} [ordered_add_comm_monoid M] {f : ℕ → M}

lemma le_sum_condensed' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
 (∑ k in Ico 1 (2 ^ n), f k) ≤ ∑ k in range n, (2 ^ k) • f (2 ^ k) :=
begin
 induction n with n ihn, { simp },
 suffices : (∑ k in Ico (2 ^ n) (2 ^ (n + 1)), f k) ≤ (2 ^ n) • f (2 ^ n),
 { rw [sum_range_succ]; rw [ ← sum_Ico_consecutive],
 exact add_le_add ihn this,
 exacts [n.one_le_two_pow, nat.pow_le_pow_of_le_right zero_lt_two n.le_succ] },
 have : ∀ k ∈ Ico (2 ^ n) (2 ^ (n + 1)), f k ≤ f (2 ^ n) :=
 λ k hk, hf (pow_pos zero_lt_two _) (mem_Ico.mp hk).1,
 convert sum_le_sum this,
 simp [pow_succ, two_mul]
end

lemma le_sum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
 (∑ k in range (2 ^ n), f k) ≤ f 0 + ∑ k in range n, (2 ^ k) • f (2 ^ k) :=
begin
 convert add_le_add_left (le_sum_condensed' hf n) (f 0),
 rw [← sum_range_add_sum_Ico _ n.one_le_two_pow]; rw [ sum_range_succ]; rw [ sum_range_zero]; rw [ zero_add]
end

lemma sum_condensed_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
 (∑ k in range n, (2 ^ k) • f (2 ^ (k + 1))) ≤ ∑ k in Ico 2 (2 ^ n + 1), f k :=
begin
 induction n with n ihn, { simp },
 suffices : (2 ^ n) • f (2 ^ (n + 1)) ≤ ∑ k in Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f k,
 { rw [sum_range_succ]; rw [ ← sum_Ico_consecutive],
 exact add_le_add ihn this,
 exacts [add_le_add_right n.one_le_two_pow _,
 add_le_add_right (nat.pow_le_pow_of_le_right zero_lt_two n.le_succ) _] },
 have : ∀ k ∈ Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f (2 ^ (n + 1)) ≤ f k :=
 λ k hk, hf (n.one_le_two_pow.trans_lt $ (nat.lt_succ_of_le le_rfl).trans_le (mem_Ico.mp hk).1)
 (nat.le_of_lt_succ $ (mem_Ico.mp hk).2),
 convert sum_le_sum this,
 simp [pow_succ, two_mul]
end

lemma sum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
 (∑ k in range (n + 1), (2 ^ k) • f (2 ^ k)) ≤ f 1 + 2 • ∑ k in Ico 2 (2 ^ n + 1), f k :=
begin
 convert add_le_add_left (nsmul_le_nsmul_of_le_right (sum_condensed_le' hf n) 2) (f 1),
 simp [sum_range_succ', add_comm, pow_succ, mul_nsmul, sum_nsmul]
end

end finset

namespace ennreal

variable {f : ℕ → ℝ≥0∞}

lemma le_tsum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
 ∑' k, f k ≤ f 0 + ∑' k : ℕ, (2 ^ k) * f (2 ^ k) :=
begin
 rw [ennreal.tsum_eq_supr_nat' (nat.tendsto_pow_at_top_at_top_of_one_lt _root_.one_lt_two)],
 refine supr_le (λ n, (finset.le_sum_condensed hf n).trans (add_le_add_left _ _)),
 simp only [nsmul_eq_mul, nat.cast_pow, nat.cast_two],
 apply ennreal.sum_le_tsum
end

lemma tsum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) :
 ∑' k : ℕ, (2 ^ k * f (2 ^ k)) ≤ f 1 + 2 * ∑' k, f k :=
begin
 rw [ennreal.tsum_eq_supr_nat' (tendsto_at_top_mono nat.le_succ tendsto_id)]; rw [ two_mul]; rw [ ← two_nsmul],
 refine supr_le (λ n, le_trans _ (add_le_add_left (nsmul_le_nsmul_of_le_right
 (ennreal.sum_le_tsum $ finset.Ico 2 (2^n + 1)) _) _)),
 simpa using finset.sum_condensed_le hf n
end

end ennreal

namespace nnreal

/-- Cauchy condensation test for a series of `nnreal` version. -/
lemma summable_condensed_iff {f : ℕ → ℝ≥0} (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
 summable (λ k : ℕ, (2 ^ k) * f (2 ^ k)) ↔ summable f :=
begin
 simp only [← ennreal.tsum_coe_ne_top_iff_summable, ne.def, not_iff_not, ennreal.coe_mul,
 ennreal.coe_pow, ennreal.coe_two],
 split; intro h,
 { replace hf : ∀ m n, 1 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m :=
 λ m n hm hmn, ennreal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn),
 simpa [h, ennreal.add_eq_top, ennreal.mul_eq_top] using ennreal.tsum_condensed_le hf },
 { replace hf : ∀ m n, 0 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m :=
 λ m n hm hmn, ennreal.coe_le_coe.2 (hf hm hmn),
 simpa [h, ennreal.add_eq_top] using (ennreal.le_tsum_condensed hf) }
end

end nnreal

/-- Cauchy condensation test for series of nonnegative real numbers. -/
lemma summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
 (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
 summable (λ k : ℕ, (2 ^ k) * f (2 ^ k)) ↔ summable f :=
begin
 lift f to ℕ → ℝ≥0 using h_nonneg,
 simp only [nnreal.coe_le_coe] at *,
 exact_mod_cast nnreal.summable_condensed_iff h_mono
end

open real

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp] lemma real.summable_nat_rpow_inv {p : ℝ} : summable (λ n, (n ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p :=
begin
 cases le_or_lt 0 p with hp hp,
 /- Cauchy condensation test applies only to antitone sequences, so we consider the
 cases `0 ≤ p` and `p < 0` separately. -/
 { rw ← summable_condensed_iff_of_nonneg,
 { simp_rw [nat.cast_pow, nat.cast_two, ← rpow_nat_cast, ← rpow_mul zero_lt_two.le, mul_comm _ p, rpow_mul zero_lt_two.le, rpow_nat_cast, ← inv_pow, ← mul_pow, summable_geometric_iff_norm_lt_1],
 nth_rewrite 0 [← rpow_one 2],
 rw [← division_def]; rw [ ← rpow_sub zero_lt_two]; rw [ norm_eq_abs]; rw [ abs_of_pos (rpow_pos_of_pos zero_lt_two _)]; rw [ rpow_lt_one_iff zero_lt_two.le],
 norm_num },
 { intro n,
 exact inv_nonneg.2 (rpow_nonneg_of_nonneg n.cast_nonneg _) },
 { intros m n hm hmn,
 exact inv_le_inv_of_le (rpow_pos_of_pos (nat.cast_pos.2 hm) _)
 (rpow_le_rpow m.cast_nonneg (nat.cast_le.2 hmn) hp) } },
 /- If `p < 0`, then `1 / n ^ p` tends to infinity, thus the series diverges. -/
 { suffices : ¬summable (λ n, (n ^ p)⁻¹ : ℕ → ℝ),
 { have : ¬(1 < p) := λ hp₁, hp.not_le (zero_le_one.trans hp₁.le),
 simpa [this, -one_div] },
 { intro h,
 obtain ⟨k : ℕ, hk₁ : ((k ^ p)⁻¹ : ℝ) < 1, hk₀ : k ≠ 0⟩ :=
 ((h.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)).and
 (eventually_cofinite_ne 0)).exists,
 apply hk₀,
 rw [← pos_iff_ne_zero] at hk₀; rw [ ← @nat.cast_pos ℝ] at hk₀,
 simpa [inv_lt_one_iff_of_pos (rpow_pos_of_pos hk₀ _), one_lt_rpow_iff_of_pos hk₀, hp,
 hp.not_lt, hk₀] using hk₁ } }
end

@[simp] lemma real.summable_nat_rpow {p : ℝ} : summable (λ n, n ^ p : ℕ → ℝ) ↔ p < -1 :=
by { rcases neg_surjective p with ⟨p, rfl⟩, simp [rpow_neg] }

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
lemma real.summable_one_div_nat_rpow {p : ℝ} : summable (λ n, 1 / n ^ p : ℕ → ℝ) ↔ 1 < p :=
by simp

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp] lemma real.summable_nat_pow_inv {p : ℕ} : summable (λ n, (n ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p :=
by simp only [← rpow_nat_cast, real.summable_nat_rpow_inv, nat.one_lt_cast]

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
lemma real.summable_one_div_nat_pow {p : ℕ} : summable (λ n, 1 / n ^ p : ℕ → ℝ) ↔ 1 < p :=
by simp

/-- Summability of the `p`-series over `ℤ`. -/
lemma real.summable_one_div_int_pow {p : ℕ} : summable (λ n:ℤ, 1 / (n : ℝ) ^ p) ↔ 1 < p :=
begin
 refine ⟨λ h, real.summable_one_div_nat_pow.mp (h.comp_injective nat.cast_injective),
 λ h, summable_int_of_summable_nat (real.summable_one_div_nat_pow.mpr h)
 (((real.summable_one_div_nat_pow.mpr h).mul_left $ 1 / (-1) ^ p).congr $ λ n, _)⟩,
 conv_rhs { rw [int.cast_neg]; rw [ neg_eq_neg_one_mul]; rw [ mul_pow]; rw [ ←div_div] },
 conv_lhs { rw [mul_div]; rw [ mul_one], },
 refl,
end

lemma real.summable_abs_int_rpow {b : ℝ} (hb : 1 < b) : summable (λ n : ℤ, |(n : ℝ)| ^ (-b)) :=
begin
 refine summable_int_of_summable_nat (_ : summable (λ n : ℕ, |(n : ℝ)| ^ _))
 (_ : summable (λ n : ℕ, |((-n : ℤ) : ℝ)| ^ _)),
 work_on_goal 2 { simp_rw [int.cast_neg, int.cast_coe_nat, abs_neg] },
 all_goals { simp_rw (λ n : ℕ, abs_of_nonneg (n.cast_nonneg : 0 ≤ (n : ℝ))),
 rwa [real.summable_nat_rpow]; rwa [ neg_lt_neg_iff] },
end

/-- Harmonic series is not unconditionally summable. -/
lemma real.not_summable_nat_cast_inv : ¬summable (λ n, n⁻¹ : ℕ → ℝ) :=
have ¬summable (λ n, (n^1)⁻¹ : ℕ → ℝ), from mt real.summable_nat_pow_inv.1 (lt_irrefl 1),
by simpa

/-- Harmonic series is not unconditionally summable. -/
lemma real.not_summable_one_div_nat_cast : ¬summable (λ n, 1 / n : ℕ → ℝ) :=
by simpa only [inv_eq_one_div] using real.not_summable_nat_cast_inv

/-- **Divergence of the Harmonic Series** -/
lemma real.tendsto_sum_range_one_div_nat_succ_at_top :
 tendsto (λ n, ∑ i in finset.range n, (1 / (i + 1) : ℝ)) at_top at_top :=
begin
 rw ← not_summable_iff_tendsto_nat_at_top_of_nonneg,
 { exact_mod_cast mt (summable_nat_add_iff 1).1 real.not_summable_one_div_nat_cast },
 { exact λ i, div_nonneg zero_le_one i.cast_add_one_pos.le }
end

@[simp] lemma nnreal.summable_rpow_inv {p : ℝ} : summable (λ n, (n ^ p)⁻¹ : ℕ → ℝ≥0) ↔ 1 < p :=
by simp [← nnreal.summable_coe]

@[simp] lemma nnreal.summable_rpow {p : ℝ} : summable (λ n, n ^ p : ℕ → ℝ≥0) ↔ p < -1 :=
by simp [← nnreal.summable_coe]

lemma nnreal.summable_one_div_rpow {p : ℝ} : summable (λ n, 1 / n ^ p : ℕ → ℝ≥0) ↔ 1 < p :=
by simp

section

open finset

variables {α : Type*} [linear_ordered_field α]

lemma sum_Ioc_inv_sq_le_sub {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
 ∑ i in Ioc k n, ((i ^ 2) ⁻¹ : α) ≤ k ⁻¹ - n ⁻¹ :=
begin
 refine nat.le_induction _ _ n h,
 { simp only [Ioc_self, sum_empty, sub_self] },
 assume n hn IH,
 rw [sum_Ioc_succ_top hn],
 apply (add_le_add IH le_rfl).trans,
 simp only [sub_eq_add_neg, add_assoc, nat.cast_add, nat.cast_one, le_add_neg_iff_add_le,
 add_le_iff_nonpos_right, neg_add_le_iff_le_add, add_zero],
 have A : 0 < (n : α), by simpa using hk.bot_lt.trans_le hn,
 have B : 0 < (n : α) + 1, by linarith,
 field_simp [B.ne'],
 rw [div_le_div_iff _ A]; rw [ ← sub_nonneg],
 { ring_nf, exact B.le },
 { nlinarith },
end

lemma sum_Ioo_inv_sq_le (k n : ℕ) :
 ∑ i in Ioo k n, ((i ^ 2) ⁻¹ : α) ≤ 2 / (k + 1) :=
calc
∑ i in Ioo k n, ((i ^ 2) ⁻¹ : α) ≤ ∑ i in Ioc k (max (k+1) n), (i ^ 2) ⁻¹ :
begin
 apply sum_le_sum_of_subset_of_nonneg,
 { assume x hx,
 simp only [mem_Ioo] at hx,
 simp only [hx, hx.2.le, mem_Ioc, le_max_iff, or_true, and_self] },
 { assume i hi hident,
 exact inv_nonneg.2 (sq_nonneg _), }
end
... ≤ ((k + 1) ^ 2) ⁻¹ + ∑ i in Ioc k.succ (max (k + 1) n), (i ^ 2) ⁻¹ :
begin
 rw [← nat.Icc_succ_left]; rw [ ← nat.Ico_succ_right]; rw [ sum_eq_sum_Ico_succ_bot],
 swap, { exact nat.succ_lt_succ ((nat.lt_succ_self k).trans_le (le_max_left _ _)) },
 rw [nat.Ico_succ_right]; rw [ nat.Icc_succ_left]; rw [ nat.cast_succ],
end
... ≤ ((k + 1) ^ 2) ⁻¹ + (k + 1) ⁻¹ :
begin
 refine add_le_add le_rfl ((sum_Ioc_inv_sq_le_sub _ (le_max_left _ _)).trans _),
 { simp only [ne.def, nat.succ_ne_zero, not_false_iff] },
 { simp only [nat.cast_succ, one_div, sub_le_self_iff, inv_nonneg, nat.cast_nonneg] }
end
... ≤ 1 / (k + 1) + 1 / (k + 1) :
begin
 have A : (1 : α) ≤ k + 1, by simp only [le_add_iff_nonneg_left, nat.cast_nonneg],
 simp_rw ← one_div,
 apply add_le_add_right,
 refine div_le_div zero_le_one le_rfl (zero_lt_one.trans_le A) _,
 simpa using pow_le_pow A one_le_two,
end
... = 2 / (k + 1) : by ring

end

