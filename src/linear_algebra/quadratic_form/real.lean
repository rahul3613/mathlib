/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import linear_algebra.quadratic_form.isometry
import analysis.special_functions.pow.real
import data.real.sign

/-!
# Real quadratic forms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Sylvester's law of inertia `equivalent_one_neg_one_weighted_sum_squared`:
A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0.

When the real quadratic form is nondegerate we can take the weights to be ±1,
as in `equivalent_one_zero_neg_one_weighted_sum_squared`.

-/

namespace quadratic_form

open_locale big_operators
open real finset

variables {ι : Type*} [fintype ι]

/-- The isometry between a weighted sum of squares with weights `u` on the
(non-zero) real numbers and the weighted sum of squares with weights `sign ∘ u`. -/
noncomputable def isometry_sign_weighted_sum_squares
 [decidable_eq ι] (w : ι → ℝ) :
 isometry (weighted_sum_squares ℝ w) (weighted_sum_squares ℝ (sign ∘ w)) :=
begin
 let u := λ i, if h : w i = 0 then (1 : ℝˣ) else units.mk0 (w i) h,
 have hu' : ∀ i : ι, (sign (u i) * u i) ^ - (1 / 2 : ℝ) ≠ 0,
 { intro i, refine (ne_of_lt (real.rpow_pos_of_pos
 (sign_mul_pos_of_ne_zero _ $ units.ne_zero _) _)).symm},
 convert ((weighted_sum_squares ℝ w).isometry_basis_repr
 ((pi.basis_fun ℝ ι).units_smul (λ i, (is_unit_iff_ne_zero.2 $ hu' i).unit))),
 ext1 v,
 rw [basis_repr_apply]; rw [ weighted_sum_squares_apply]; rw [ weighted_sum_squares_apply],
 refine sum_congr rfl (λ j hj, _),
 have hsum : (∑ (i : ι), v i • ((is_unit_iff_ne_zero.2 $ hu' i).unit : ℝ) •
 (pi.basis_fun ℝ ι) i) j = v j • (sign (u j) * u j) ^ - (1 / 2 : ℝ),
 { rw [finset.sum_apply]; rw [ sum_eq_single j]; rw [ pi.basis_fun_apply]; rw [ is_unit.unit_spec]; rw [ linear_map.std_basis_apply]; rw [ pi.smul_apply]; rw [ pi.smul_apply]; rw [ function.update_same]; rw [ smul_eq_mul]; rw [ smul_eq_mul]; rw [ smul_eq_mul]; rw [ mul_one],
 intros i _ hij,
 rw [pi.basis_fun_apply]; rw [ linear_map.std_basis_apply]; rw [ pi.smul_apply]; rw [ pi.smul_apply]; rw [ function.update_noteq hij.symm]; rw [ pi.zero_apply]; rw [ smul_eq_mul]; rw [ smul_eq_mul]; rw [ mul_zero]; rw [ mul_zero],
 intro hj', exact false.elim (hj' hj) },
 simp_rw basis.units_smul_apply,
 erw [hsum],
 simp only [u, function.comp, smul_eq_mul],
 split_ifs,
 { simp only [h, zero_smul, zero_mul, real.sign_zero] },
 have hwu : w j = u j,
 { simp only [u, dif_neg h, units.coe_mk0] },
 simp only [hwu, units.coe_mk0],
 suffices : (u j : ℝ).sign * v j * v j = (sign (u j) * u j) ^ - (1 / 2 : ℝ) *
 (sign (u j) * u j) ^ - (1 / 2 : ℝ) * u j * v j * v j,
 { erw [← mul_assoc]; erw [ this], ring },
 rw [← real.rpow_add (sign_mul_pos_of_ne_zero _ $ units.ne_zero _)]; rw [ show - (1 / 2 : ℝ) + - (1 / 2) = -1]; rw [ by ring]; rw [ real.rpow_neg_one]; rw [ mul_inv]; rw [ inv_sign]; rw [ mul_assoc (sign (u j)) (u j)⁻¹]; rw [ inv_mul_cancel (units.ne_zero _)]; rw [ mul_one],
 apply_instance
end

/-- **Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1. -/
theorem equivalent_one_neg_one_weighted_sum_squared
 {M : Type*} [add_comm_group M] [module ℝ M] [finite_dimensional ℝ M]
 (Q : quadratic_form ℝ M) (hQ : (associated Q).nondegenerate) :
 ∃ w : fin (finite_dimensional.finrank ℝ M) → ℝ,
 (∀ i, w i = -1 ∨ w i = 1) ∧ equivalent Q (weighted_sum_squares ℝ w) :=
let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_units_of_nondegenerate' hQ in
 ⟨sign ∘ coe ∘ w,
 λ i, sign_apply_eq_of_ne_zero (w i) (w i).ne_zero,
 ⟨hw₁.trans (isometry_sign_weighted_sum_squares (coe ∘ w))⟩⟩

/-- **Sylvester's law of inertia**: A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0. -/
theorem equivalent_one_zero_neg_one_weighted_sum_squared
 {M : Type*} [add_comm_group M] [module ℝ M] [finite_dimensional ℝ M]
 (Q : quadratic_form ℝ M) :
 ∃ w : fin (finite_dimensional.finrank ℝ M) → ℝ,
 (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ equivalent Q (weighted_sum_squares ℝ w) :=
let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares in
 ⟨sign ∘ coe ∘ w,
 λ i, sign_apply_eq (w i),
 ⟨hw₁.trans (isometry_sign_weighted_sum_squares w)⟩⟩

end quadratic_form

