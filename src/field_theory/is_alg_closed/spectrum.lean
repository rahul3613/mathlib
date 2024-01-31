/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import algebra.algebra.spectrum
import field_theory.is_alg_closed.basic

/-!
# Spectrum mapping theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops proves the spectral mapping theorem for polynomials over algebraically closed
fields. In particular, if `a` is an element of an `𝕜`-algebra `A` where `𝕜` is a field, and
`p : 𝕜[X]` is a polynomial, then the spectrum of `polynomial.aeval a p` contains the image of the
spectrum of `a` under `(λ k, polynomial.eval k p)`. When `𝕜` is algebraically closed, these are in
fact equal (assuming either that the spectrum of `a` is nonempty or the polynomial has positive
degree), which is the **spectral mapping theorem**.

In addition, this file contains the fact that every element of a finite dimensional nontrivial
algebra over an algebraically closed field has nonempty spectrum. In particular, this is used in
`module.End.exists_eigenvalue` to show that every linear map from a vector space to itself has an
eigenvalue.

## Main statements

* `spectrum.subset_polynomial_aeval`, `spectrum.map_polynomial_aeval_of_degree_pos`,
  `spectrum.map_polynomial_aeval_of_nonempty`: variations on the **spectral mapping theorem**.
* `spectrum.nonempty_of_is_alg_closed_of_finite_dimensional`: the spectrum is nonempty for any
  element of a nontrivial finite dimensional algebra over an algebraically closed field.

## Notations

* `σ a` : `spectrum R a` of `a : A`
-/

namespace spectrum

open set polynomial
open_locale pointwise polynomial

universes u v

section scalar_ring

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] [algebra R A]

local notation `σ` := spectrum R
local notation `↑ₐ` := algebra_map R A

lemma exists_mem_of_not_is_unit_aeval_prod [is_domain R] {p : R[X]} {a : A} (hp : p ≠ 0)
  (h : ¬is_unit (aeval a (multiset.map (λ (x : R), X - C x) p.roots).prod)) :
  ∃ k : R, k ∈ σ a ∧ eval k p = 0 :=
begin
  rw [←multiset.prod_to_list, alg_hom.map_list_prod] at h,
  replace h := mt list.prod_is_unit h,
  simp only [not_forall, exists_prop, aeval_C, multiset.mem_to_list,
    list.mem_map, aeval_X, exists_exists_and_eq_and, multiset.mem_map, alg_hom.map_sub] at h,
  rcases h with ⟨r, r_mem, r_nu⟩,
  exact ⟨r, by rwa [mem_iff, ←is_unit.sub_iff], by rwa [←is_root.def, ←mem_roots hp]⟩
end

end scalar_ring

section scalar_field

variables {𝕜 : Type u} {A : Type v}
variables [field 𝕜] [ring A] [algebra 𝕜 A]

local notation `σ` := spectrum 𝕜
local notation `↑ₐ` := algebra_map 𝕜 A

open polynomial
/-- Half of the spectral mapping theorem for polynomials. We prove it separately
because it holds over any field, whereas `spectrum.map_polynomial_aeval_of_degree_pos` and
`spectrum.map_polynomial_aeval_of_nonempty` need the field to be algebraically closed. -/
theorem subset_polynomial_aeval (a : A) (p : 𝕜[X]) :
  (λ k, eval k p) '' (σ a) ⊆ σ (aeval a p) :=
begin
  rintros _ ⟨k, hk, rfl⟩,
  let q := C (eval k p) - p,
  have hroot : is_root q k, by simp only [eval_C, eval_sub, sub_self, is_root.def],
  rw [←mul_div_eq_iff_is_root, ←neg_mul_neg, neg_sub] at hroot,
  have aeval_q_eq : ↑ₐ(eval k p) - aeval a p = aeval a q,
    by simp only [aeval_C, alg_hom.map_sub, sub_left_inj],
  rw [mem_iff, aeval_q_eq, ←hroot, aeval_mul],
  have hcomm := (commute.all (C k - X) (- (q / (X - C k)))).map (aeval a),
  apply mt (λ h, (hcomm.is_unit_mul_iff.mp h).1),
  simpa only [aeval_X, aeval_C, alg_hom.map_sub] using hk,
end

/-- The *spectral mapping theorem* for polynomials.  Note: the assumption `degree p > 0`
is necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right-hand side,
assuming `[nontrivial A]`, is `{k}` where `p = polynomial.C k`. -/
theorem map_polynomial_aeval_of_degree_pos [is_alg_closed 𝕜] (a : A) (p : 𝕜[X])
  (hdeg : 0 < degree p) : σ (aeval a p) = (λ k, eval k p) '' (σ a) :=
begin
  /- handle the easy direction via `spectrum.subset_polynomial_aeval` -/
  refine set.eq_of_subset_of_subset (λ k hk, _) (subset_polynomial_aeval a p),
  /- write `C k - p` product of linear factors and a constant; show `C k - p ≠ 0`. -/
  have hprod := eq_prod_roots_of_splits_id (is_alg_closed.splits (C k - p)),
  have h_ne : C k - p ≠ 0, from ne_zero_of_degree_gt
    (by rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hdeg)]),
  have lead_ne := leading_coeff_ne_zero.mpr h_ne,
  have lead_unit := (units.map (↑ₐ).to_monoid_hom (units.mk0 _ lead_ne)).is_unit,
  /- leading coefficient is a unit so product of linear factors is not a unit;
  apply `exists_mem_of_not_is_unit_aeval_prod`. -/
  have p_a_eq : aeval a (C k - p) = ↑ₐk - aeval a p,
    by simp only [aeval_C, alg_hom.map_sub, sub_left_inj],
  rw [mem_iff, ←p_a_eq, hprod, aeval_mul,
    ((commute.all _ _).map (aeval a)).is_unit_mul_iff, aeval_C] at hk,
  replace hk := exists_mem_of_not_is_unit_aeval_prod h_ne (not_and.mp hk lead_unit),
  rcases hk with ⟨r, r_mem, r_ev⟩,
  exact ⟨r, r_mem, symm (by simpa [eval_sub, eval_C, sub_eq_zero] using r_ev)⟩,
end

/-- In this version of the spectral mapping theorem, we assume the spectrum
is nonempty instead of assuming the degree of the polynomial is positive. -/
theorem map_polynomial_aeval_of_nonempty [is_alg_closed 𝕜] (a : A) (p : 𝕜[X])
  (hnon : (σ a).nonempty) : σ (aeval a p) = (λ k, eval k p) '' (σ a) :=
begin
  nontriviality A,
  refine or.elim (le_or_gt (degree p) 0) (λ h, _) (map_polynomial_aeval_of_degree_pos a p),
  { rw eq_C_of_degree_le_zero h,
    simp only [set.image_congr, eval_C, aeval_C, scalar_eq, set.nonempty.image_const hnon] },
end

/-- A specialization of `spectrum.subset_polynomial_aeval` to monic monomials for convenience. -/
lemma pow_image_subset (a : A) (n : ℕ) : (λ x, x ^ n) '' (σ a) ⊆ σ (a ^ n) :=
by simpa only [eval_pow, eval_X, aeval_X_pow] using subset_polynomial_aeval a (X ^ n : 𝕜[X])

/-- A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
convenience. -/
lemma map_pow_of_pos [is_alg_closed 𝕜] (a : A) {n : ℕ} (hn : 0 < n) :
  σ (a ^ n) = (λ x, x ^ n) '' (σ a) :=
by simpa only [aeval_X_pow, eval_pow, eval_X] using
  map_polynomial_aeval_of_degree_pos a (X ^ n : 𝕜[X]) (by { rw_mod_cast degree_X_pow, exact hn })

/-- A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
convenience. -/
lemma map_pow_of_nonempty [is_alg_closed 𝕜] {a : A} (ha : (σ a).nonempty) (n : ℕ) :
  σ (a ^ n) = (λ x, x ^ n) '' (σ a) :=
by simpa only [aeval_X_pow, eval_pow, eval_X] using map_polynomial_aeval_of_nonempty a (X ^ n) ha

variable (𝕜)
/--
Every element `a` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `𝕜` has non-empty spectrum. -/
-- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
lemma nonempty_of_is_alg_closed_of_finite_dimensional [is_alg_closed 𝕜]
  [nontrivial A] [I : finite_dimensional 𝕜 A] (a : A) :
  (σ a).nonempty :=
begin
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := is_integral_of_noetherian (is_noetherian.iff_fg.2 I) a,
  have nu : ¬ is_unit (aeval a p), { rw [←aeval_def] at h_eval_p, rw h_eval_p, simp, },
  rw [eq_prod_roots_of_monic_of_splits_id h_mon (is_alg_closed.splits p)] at nu,
  obtain ⟨k, hk, _⟩ := exists_mem_of_not_is_unit_aeval_prod (monic.ne_zero h_mon) nu,
  exact ⟨k, hk⟩
end

end scalar_field

end spectrum
