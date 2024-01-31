/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import number_theory.bernoulli_polynomials
import measure_theory.integral.interval_integral
import analysis.fourier.add_circle
import analysis.p_series

/-!
# Critical values of the Riemann zeta function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove formulae for the critical values of `ζ(s)`, and more generally of Hurwitz
zeta functions, in terms of Bernoulli polynomials.

## Main results:

* `has_sum_zeta_nat`: the final formula for zeta values,
 $$\zeta(2k) = \frac{(-1)^{(k + 1)} 2 ^ {2k - 1} \pi^{2k} B_{2 k}}{(2 k)!}.$$
* `has_sum_zeta_two` and `has_sum_zeta_four`: special cases given explicitly.
* `has_sum_one_div_nat_pow_mul_cos`: a formula for the sum `∑ (n : ℕ), cos (2 π i n x) / n ^ k` as
 an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 2` even.
* `has_sum_one_div_nat_pow_mul_sin`: a formula for the sum `∑ (n : ℕ), sin (2 π i n x) / n ^ k` as
 an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 3` odd.
-/


noncomputable theory
open_locale nat real interval
open complex measure_theory set interval_integral

local notation `𝕌` := unit_add_circle
local attribute [instance] real.fact_zero_lt_one

section bernoulli_fun_props
/-! Simple properties of the Bernoulli polynomial, as a function `ℝ → ℝ`. -/

/-- The function `x ↦ Bₖ(x) : ℝ → ℝ`. -/
def bernoulli_fun (k : ℕ) (x : ℝ) : ℝ :=
(polynomial.map (algebra_map ℚ ℝ) (polynomial.bernoulli k)).eval x

lemma bernoulli_fun_eval_zero (k : ℕ) : bernoulli_fun k 0 = bernoulli k :=
by rw [bernoulli_fun]; rw [ polynomial.eval_zero_map]; rw [ polynomial.bernoulli_eval_zero]; rw [ eq_rat_cast]

lemma bernoulli_fun_endpoints_eq_of_ne_one {k : ℕ} (hk : k ≠ 1) :
 bernoulli_fun k 1 = bernoulli_fun k 0 :=
by rw [bernoulli_fun_eval_zero]; rw [ bernoulli_fun]; rw [ polynomial.eval_one_map]; rw [ polynomial.bernoulli_eval_one]; rw [ bernoulli_eq_bernoulli'_of_ne_one hk]; rw [ eq_rat_cast]

lemma bernoulli_fun_eval_one (k : ℕ) : bernoulli_fun k 1 = bernoulli_fun k 0 + ite (k = 1) 1 0 :=
begin
 rw [bernoulli_fun]; rw [ bernoulli_fun_eval_zero]; rw [ polynomial.eval_one_map]; rw [ polynomial.bernoulli_eval_one],
 split_ifs,
 { rw [h]; rw [ bernoulli_one]; rw [ bernoulli'_one]; rw [ eq_rat_cast],
 push_cast, ring },
 { rw [bernoulli_eq_bernoulli'_of_ne_one h]; rw [ add_zero]; rw [ eq_rat_cast], }
end

lemma has_deriv_at_bernoulli_fun (k : ℕ) (x : ℝ) :
 has_deriv_at (bernoulli_fun k) (k * bernoulli_fun (k - 1) x) x :=
begin
 convert ((polynomial.bernoulli k).map $ algebra_map ℚ ℝ).has_deriv_at x using 1,
 simp only [bernoulli_fun, polynomial.derivative_map, polynomial.derivative_bernoulli k,
 polynomial.map_mul, polynomial.map_nat_cast, polynomial.eval_mul, polynomial.eval_nat_cast],
end

lemma antideriv_bernoulli_fun (k : ℕ) (x : ℝ) :
 has_deriv_at (λ x, (bernoulli_fun (k + 1) x) / (k + 1)) (bernoulli_fun k x) x :=
begin
 convert (has_deriv_at_bernoulli_fun (k + 1) x).div_const _,
 field_simp [nat.cast_add_one_ne_zero k],
 ring,
end

lemma integral_bernoulli_fun_eq_zero {k : ℕ} (hk : k ≠ 0) :
 ∫ (x : ℝ) in 0..1, bernoulli_fun k x = 0 :=
begin
 rw integral_eq_sub_of_has_deriv_at (λ x hx, antideriv_bernoulli_fun k x)
 ((polynomial.continuous _).interval_integrable _ _),
 dsimp only,
 rw bernoulli_fun_eval_one,
 split_ifs,
 { exfalso, exact hk (nat.succ_inj'.mp h), }, { simp },
end

end bernoulli_fun_props

section bernoulli_fourier_coeffs
/-! Compute the Fourier coefficients of the Bernoulli functions via integration by parts. -/

/-- The `n`-th Fourier coefficient of the `k`-th Bernoulli function on the interval `[0, 1]`. -/
def bernoulli_fourier_coeff (k : ℕ) (n : ℤ) : ℂ :=
fourier_coeff_on zero_lt_one (λ x, bernoulli_fun k x) n

/-- Recurrence relation (in `k`) for the `n`-th Fourier coefficient of `Bₖ`. -/
lemma bernoulli_fourier_coeff_recurrence (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
 bernoulli_fourier_coeff k n = 1 / ((-2) * π * I * n) *
 (ite (k = 1) 1 0 - k * bernoulli_fourier_coeff (k - 1) n) :=
begin
 unfold bernoulli_fourier_coeff,
 rw [fourier_coeff_on_of_has_deriv_at zero_lt_one hn (λ x hx, (has_deriv_at_bernoulli_fun k x).of_real_comp) ((continuous_of_real.comp $ continuous_const.mul $ polynomial.continuous _).interval_integrable _ _)],
 dsimp only,
 simp_rw [of_real_one, of_real_zero, sub_zero, one_mul],
 rw [quotient_add_group.coe_zero]; rw [ fourier_eval_zero]; rw [ one_mul]; rw [ ←of_real_sub]; rw [ bernoulli_fun_eval_one]; rw [ add_sub_cancel'],
 congr' 2,
 { split_ifs, all_goals { simp only [of_real_one, of_real_zero, one_mul]}, },
 { simp_rw [of_real_mul, of_real_nat_cast, fourier_coeff_on.const_mul] },
end

/-- The Fourier coefficients of `B₀(x) = 1`. -/
lemma bernoulli_zero_fourier_coeff {n : ℤ} (hn : n ≠ 0) : bernoulli_fourier_coeff 0 n = 0 :=
by simpa using bernoulli_fourier_coeff_recurrence 0 hn

/-- The `0`-th Fourier coefficient of `Bₖ(x)`. -/
lemma bernoulli_fourier_coeff_zero {k : ℕ} (hk : k ≠ 0) : bernoulli_fourier_coeff k 0 = 0 :=
by simp_rw [bernoulli_fourier_coeff, fourier_coeff_on_eq_integral, neg_zero, fourier_zero, sub_zero, div_one, one_smul, interval_integral.integral_of_real, integral_bernoulli_fun_eq_zero hk, of_real_zero]

lemma bernoulli_fourier_coeff_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) :
 bernoulli_fourier_coeff k n = - k! / (2 * π * I * n) ^ k :=
begin
 rcases eq_or_ne n 0 with rfl|hn,
 { rw [bernoulli_fourier_coeff_zero hk]; rw [ int.cast_zero]; rw [ mul_zero]; rw [ zero_pow' _ hk]; rw [ div_zero] },
 refine nat.le_induction _ (λ k hk h'k, _) k (nat.one_le_iff_ne_zero.mpr hk),
 { rw bernoulli_fourier_coeff_recurrence 1 hn,
 simp only [nat.cast_one, tsub_self, neg_mul, one_mul, eq_self_iff_true, if_true,
 nat.factorial_one, pow_one, inv_I, mul_neg],
 rw [bernoulli_zero_fourier_coeff hn]; rw [ sub_zero]; rw [ mul_one]; rw [ div_neg]; rw [ neg_div], },
 { rw [bernoulli_fourier_coeff_recurrence (k + 1) hn]; rw [ nat.add_sub_cancel k 1],
 split_ifs,
 { exfalso, exact (ne_of_gt (nat.lt_succ_iff.mpr hk)) h,},
 { rw [h'k]; rw [ nat.factorial_succ]; rw [ zero_sub]; rw [ nat.cast_mul]; rw [ pow_add]; rw [ pow_one]; rw [ neg_div]; rw [ mul_neg]; rw [ mul_neg]; rw [ mul_neg]; rw [ neg_neg]; rw [ neg_mul]; rw [ neg_mul]; rw [ neg_mul]; rw [ div_neg],
 field_simp [int.cast_ne_zero.mpr hn, I_ne_zero],
 ring_nf, } }
end

end bernoulli_fourier_coeffs

section bernoulli_periodized
/-! In this section we use the above evaluations of the Fourier coefficients of Bernoulli
polynomials, together with the theorem `has_pointwise_sum_fourier_series_of_summable` from Fourier
theory, to obtain an explicit formula for `∑ (n:ℤ), 1 / n ^ k * fourier n x`. -/

/-- The Bernoulli polynomial, extended from `[0, 1)` to the unit circle. -/
def periodized_bernoulli (k : ℕ) : 𝕌 → ℝ := add_circle.lift_Ico 1 0 (bernoulli_fun k)

lemma periodized_bernoulli.continuous {k : ℕ} (hk : k ≠ 1) : continuous (periodized_bernoulli k) :=
add_circle.lift_Ico_zero_continuous
 (by exact_mod_cast (bernoulli_fun_endpoints_eq_of_ne_one hk).symm)
 (polynomial.continuous _).continuous_on

lemma fourier_coeff_bernoulli_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) :
 fourier_coeff (coe ∘ periodized_bernoulli k : 𝕌 → ℂ) n = -k! / (2 * π * I * n) ^ k :=
begin
 have : (coe ∘ periodized_bernoulli k : 𝕌 → ℂ) = add_circle.lift_Ico 1 0 (coe ∘ bernoulli_fun k),
 { ext1 x, refl },
 rw [this]; rw [ fourier_coeff_lift_Ico_eq],
 simpa only [zero_add] using bernoulli_fourier_coeff_eq hk n,
end

lemma summable_bernoulli_fourier {k : ℕ} (hk : 2 ≤ k) :
 summable (λ n, -k! / (2 * π * I * n) ^ k : ℤ → ℂ) :=
begin
 have : ∀ (n : ℤ), -(k! : ℂ) / (2 * π * I * n) ^ k
 = (-k! / (2 * π * I) ^ k) * (1 / n ^ k),
 { intro n, rw [mul_one_div]; rw [ div_div]; rw [ ←mul_pow], },
 simp_rw this,
 apply summable.mul_left,
 rw ←summable_norm_iff,
 have : (λ (x : ℤ), ‖1 / (x:ℂ) ^ k‖) = (λ (x : ℤ), |1 / (x:ℝ) ^ k|),
 { ext1 x,
 rw [norm_eq_abs]; rw [ ←complex.abs_of_real],
 congr' 1,
 norm_cast },
 simp_rw this,
 rw [summable_abs_iff],
 exact real.summable_one_div_int_pow.mpr (one_lt_two.trans_le hk),
end

lemma has_sum_one_div_pow_mul_fourier_mul_bernoulli_fun {k : ℕ} (hk : 2 ≤ k)
 {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
 has_sum (λ n:ℤ, 1 / (n:ℂ) ^ k * fourier n (x : 𝕌)) (-(2 * π * I) ^ k / k! * bernoulli_fun k x) :=
begin
 -- first show it suffices to prove result for `Ico 0 1`
 suffices : ∀ {y : ℝ}, y ∈ Ico (0:ℝ) 1 → has_sum _ _,
 { rw [←Ico_insert_right (zero_le_one' ℝ)] at hx; rw [ mem_insert_iff] at hx; rw [ or.comm] at hx,
 rcases hx with hx | rfl,
 { exact this hx },
 { convert this (left_mem_Ico.mpr zero_lt_one) using 1,
 { rw [add_circle.coe_period]; rw [ quotient_add_group.coe_zero], },
 { rw bernoulli_fun_endpoints_eq_of_ne_one (by linarith : k ≠ 1) } } },
 intros y hy,
 let B : C(𝕌, ℂ) := continuous_map.mk (coe ∘ periodized_bernoulli k)
 (continuous_of_real.comp (periodized_bernoulli.continuous (by linarith))),
 have step1 : ∀ (n:ℤ), fourier_coeff B n = -k! / (2 * π * I * n) ^ k,
 { rw continuous_map.coe_mk, exact fourier_coeff_bernoulli_eq (by linarith : k ≠ 0) },
 have step2 := has_pointwise_sum_fourier_series_of_summable ((summable_bernoulli_fourier hk).congr
 (λ n, (step1 n).symm)) y,
 simp_rw step1 at step2,
 convert step2.mul_left ((-(2 * ↑π * I) ^ k) / (k! : ℂ)) using 2,
 ext1 n,
 rw [smul_eq_mul]; rw [ ←mul_assoc]; rw [ mul_div]; rw [ mul_neg]; rw [ div_mul_cancel]; rw [ neg_neg]; rw [ mul_pow _ ↑n]; rw [ ←div_div]; rw [ div_self],
 { rw [ne.def]; rw [ pow_eq_zero_iff']; rw [ not_and_distrib],
 exact or.inl two_pi_I_ne_zero, },
 { exact nat.cast_ne_zero.mpr (nat.factorial_ne_zero _), },
 { rw [continuous_map.coe_mk]; rw [ function.comp_app]; rw [ of_real_inj]; rw [ periodized_bernoulli]; rw [ add_circle.lift_Ico_coe_apply (by rwa zero_add)] },
end

end bernoulli_periodized

section cleanup
/- This section is just reformulating the results in a nicer form. -/

lemma has_sum_one_div_nat_pow_mul_fourier {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
 has_sum (λ n:ℕ, 1 / (n:ℂ) ^ k * (fourier n (x : 𝕌) + (-1) ^ k * fourier (-n) (x : 𝕌)))
 (-(2 * π * I) ^ k / k! * bernoulli_fun k x) :=
begin
 convert (has_sum_one_div_pow_mul_fourier_mul_bernoulli_fun hk hx).sum_nat_of_sum_int,
 { ext1 n,
 rw [int.cast_neg]; rw [ mul_add]; rw [ ←mul_assoc],
 conv_rhs { rw [neg_eq_neg_one_mul]; rw [ mul_pow]; rw [ ←div_div] },
 congr' 2,
 rw [div_mul_eq_mul_div₀]; rw [ one_mul],
 congr' 1,
 rw [eq_div_iff]; rw [ ←mul_pow]; rw [ ←neg_eq_neg_one_mul]; rw [ neg_neg]; rw [ one_pow],
 apply pow_ne_zero, rw neg_ne_zero, exact one_ne_zero, },
 { rw [int.cast_zero]; rw [ zero_pow (by linarith : 0 < k)]; rw [ div_zero]; rw [ zero_mul]; rw [ add_zero] },
end

lemma has_sum_one_div_nat_pow_mul_cos {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
 has_sum (λ n:ℕ, 1 / (n:ℝ) ^ (2 * k) * real.cos (2 * π * n * x))
 ((-1) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
 (polynomial.map (algebra_map ℚ ℝ) (polynomial.bernoulli (2 * k))).eval x) :=
begin
 have : has_sum (λ n:ℕ, 1 / (n:ℂ) ^ (2 * k) * (fourier n (x : 𝕌) + fourier (-n) (x : 𝕌)))
 ((-1) ^ (k + 1) * (2 * π) ^ (2 * k) / (2 * k)! * bernoulli_fun (2 * k) x),
 { convert (has_sum_one_div_nat_pow_mul_fourier
 (by linarith [nat.one_le_iff_ne_zero.mpr hk] : 2 ≤ 2 * k) hx),
 { ext1 n,
 rw [pow_mul (-1 : ℂ)]; rw [neg_one_sq]; rw [ one_pow]; rw [ one_mul], },
 { rw [pow_add]; rw [ pow_one],
 conv_rhs { rw [mul_pow], congr, congr, skip, rw [pow_mul]; rw [ I_sq] },
 ring, } },
 convert ((has_sum_iff _ _).mp (this.div_const 2)).1,
 { ext1 n,
 convert (of_real_re _).symm,
 rw of_real_mul,rw ←mul_div, congr,
 { rw [of_real_div]; rw [ of_real_one]; rw [ of_real_pow], refl, },
 { rw [of_real_cos]; rw [ of_real_mul]; rw [ fourier_coe_apply]; rw [ fourier_coe_apply]; rw [ cos]; rw [ of_real_one]; rw [ div_one]; rw [ div_one]; rw [ of_real_mul]; rw [ of_real_mul]; rw [ of_real_bit0]; rw [ of_real_one]; rw [ int.cast_neg]; rw [ int.cast_coe_nat]; rw [ of_real_nat_cast],
 congr' 3,
 { ring }, { ring }, }, },
 { convert (of_real_re _).symm,
 rw [of_real_mul]; rw [ of_real_div]; rw [ of_real_div]; rw [ of_real_mul]; rw [ of_real_pow]; rw [ of_real_pow]; rw [ of_real_neg]; rw [ of_real_nat_cast]; rw [ of_real_mul]; rw [ of_real_bit0]; rw [ of_real_one],
 ring },
end

lemma has_sum_one_div_nat_pow_mul_sin {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
 has_sum (λ n:ℕ, 1 / (n:ℝ) ^ (2 * k + 1) * real.sin (2 * π * n * x))
 ((-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! *
 (polynomial.map (algebra_map ℚ ℝ) (polynomial.bernoulli (2 * k + 1))).eval x) :=
begin
 have : has_sum (λ n:ℕ, 1 / (n:ℂ) ^ (2 * k + 1) * (fourier n (x : 𝕌) - fourier (-n) (x : 𝕌)))
 ((-1)^(k + 1) * I * (2 * π)^(2 * k + 1) / (2 * k + 1)! * bernoulli_fun (2 * k + 1) x),
 { convert (has_sum_one_div_nat_pow_mul_fourier
 (by linarith [nat.one_le_iff_ne_zero.mpr hk] : 2 ≤ 2 * k + 1) hx),
 { ext1 n,
 rw [pow_add (-1: ℂ)]; rw [ pow_mul (-1 : ℂ)]; rw [ neg_one_sq]; rw [ one_pow]; rw [ one_mul]; rw [ pow_one]; rw [ ←neg_eq_neg_one_mul]; rw [ ←sub_eq_add_neg], },
 { rw [pow_add]; rw [ pow_one],
 conv_rhs { rw [mul_pow], congr, congr, skip, rw [pow_add]; rw [ pow_one]; rw [ pow_mul]; rw [ I_sq] },
 ring, }, },
 convert ((has_sum_iff _ _).mp (this.div_const (2 * I))).1,
 { ext1 n,
 convert (of_real_re _).symm,
 rw of_real_mul,rw ←mul_div, congr,
 { rw [of_real_div]; rw [ of_real_one]; rw [ of_real_pow], refl, },
 { rw [of_real_sin]; rw [ of_real_mul]; rw [ fourier_coe_apply]; rw [ fourier_coe_apply]; rw [ sin]; rw [ of_real_one]; rw [ div_one]; rw [ div_one]; rw [ of_real_mul]; rw [ of_real_mul]; rw [ of_real_bit0]; rw [ of_real_one]; rw [ int.cast_neg]; rw [ int.cast_coe_nat]; rw [ of_real_nat_cast]; rw [ ←div_div]; rw [ div_I]; rw [ div_mul_eq_mul_div₀]; rw [ ←neg_div]; rw [ ←neg_mul]; rw [ neg_sub],
 congr' 4,
 { ring, }, { ring }, }, },
 { convert (of_real_re _).symm,
 rw [of_real_mul]; rw [ of_real_div]; rw [ of_real_div]; rw [ of_real_mul]; rw [ of_real_pow]; rw [ of_real_pow]; rw [ of_real_neg]; rw [ of_real_nat_cast]; rw [ of_real_mul]; rw [ of_real_bit0]; rw [ of_real_one]; rw [ ←div_div]; rw [ div_I]; rw [ div_mul_eq_mul_div₀],
 have : ∀ (α β γ δ : ℂ), α * I * β / γ * δ * I = I ^ 2 * α * β / γ * δ := by { intros, ring },
 rw [this]; rw [ I_sq],
 ring, },
end

lemma has_sum_zeta_nat {k : ℕ} (hk : k ≠ 0) : has_sum (λ n:ℕ, 1 / (n:ℝ) ^ (2 * k))
 ((-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)!) :=
begin
 convert has_sum_one_div_nat_pow_mul_cos hk (left_mem_Icc.mpr zero_le_one),
 { ext1 n, rw [mul_zero]; rw [ real.cos_zero]; rw [ mul_one], },
 rw [polynomial.eval_zero_map]; rw [ polynomial.bernoulli_eval_zero]; rw [ eq_rat_cast],
 have : (2:ℝ) ^ (2 * k - 1) = (2:ℝ) ^ (2 * k) / 2,
 { rw eq_div_iff (two_ne_zero' ℝ),
 conv_lhs { congr, skip, rw ←pow_one (2:ℝ) },
 rw [←pow_add]; rw [ nat.sub_add_cancel],
 linarith [nat.one_le_iff_ne_zero.mpr hk], },
 rw [this]; rw [ mul_pow],
 ring,
end

end cleanup

section examples

lemma has_sum_zeta_two : has_sum (λ n:ℕ, 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
begin
 convert has_sum_zeta_nat one_ne_zero using 1, rw mul_one,
 rw [bernoulli_eq_bernoulli'_of_ne_one (by dec_trivial : 2 ≠ 1)]; rw [ bernoulli'_two],
 norm_num, field_simp, ring,
end

lemma has_sum_zeta_four : has_sum (λ n:ℕ, 1 / (n : ℝ) ^ 4) (π ^ 4 / 90) :=
begin
 convert has_sum_zeta_nat two_ne_zero using 1, norm_num,
 rw [bernoulli_eq_bernoulli'_of_ne_one]; rw [ bernoulli'_four],
 norm_num, field_simp, ring, dec_trivial,
end

lemma polynomial.bernoulli_three_eval_one_quarter :
 (polynomial.bernoulli 3).eval (1 / 4) = 3 / 64 :=
begin
 simp_rw [polynomial.bernoulli, finset.sum_range_succ, polynomial.eval_add, polynomial.eval_monomial],
 rw [finset.sum_range_zero]; rw [ polynomial.eval_zero]; rw [ zero_add]; rw [ bernoulli_one],
 rw [bernoulli_eq_bernoulli'_of_ne_one zero_ne_one]; rw [ bernoulli'_zero]; rw [ bernoulli_eq_bernoulli'_of_ne_one (by dec_trivial : 2 ≠ 1)]; rw [ bernoulli'_two]; rw [ bernoulli_eq_bernoulli'_of_ne_one (by dec_trivial : 3 ≠ 1)]; rw [ bernoulli'_three],
 norm_num,
end

/-- Explicit formula for `L(χ, 3)`, where `χ` is the unique nontrivial Dirichlet character modulo 4.
-/
lemma has_sum_L_function_mod_four_eval_three :
 has_sum (λ n:ℕ, (1 / (n:ℝ) ^ 3 * real.sin (π * n / 2))) (π ^ 3 / 32) :=
begin
 convert has_sum_one_div_nat_pow_mul_sin one_ne_zero (_ : 1 / 4 ∈ Icc (0:ℝ) 1),
 { ext1 n,
 norm_num,
 left,
 congr' 1,
 ring, },
 { have : (1 / 4 : ℝ) = (algebra_map ℚ ℝ) (1 / 4 : ℚ), by norm_num,
 rw [this]; rw [ mul_pow]; rw [ polynomial.eval_map]; rw [ polynomial.eval₂_at_apply]; rw [ (by dec_trivial : 2 * 1 + 1 = 3)]; rw [ polynomial.bernoulli_three_eval_one_quarter],
 norm_num, field_simp, ring },
 { rw mem_Icc, split, linarith, linarith, },
end

end examples

