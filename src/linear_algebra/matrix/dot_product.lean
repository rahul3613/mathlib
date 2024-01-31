/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/

import algebra.star.order
import data.matrix.basic
import linear_algebra.std_basis

/-!
# Dot product of two vectors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results on the map `matrix.dot_product`, which maps two
vectors `v w : n → R` to the sum of the entrywise products `v i * w i`.

## Main results

* `matrix.dot_product_std_basis_one`: the dot product of `v` with the `i`th
  standard basis vector is `v i`
* `matrix.dot_product_eq_zero_iff`: if `v`'s' dot product with all `w` is zero,
  then `v` is zero

## Tags

matrix, reindex

-/

universes v w
variables {R : Type v} {n : Type w}

namespace matrix

section semiring
variables [semiring R] [fintype n]

@[simp] lemma dot_product_std_basis_eq_mul [decidable_eq n] (v : n → R) (c : R) (i : n) :
  dot_product v (linear_map.std_basis R (λ _, R) i c) = v i * c :=
begin
  rw [dot_product, finset.sum_eq_single i, linear_map.std_basis_same],
  exact λ _ _ hb, by rw [linear_map.std_basis_ne _ _ _ _ hb, mul_zero],
  exact λ hi, false.elim (hi $ finset.mem_univ _)
end

@[simp] lemma dot_product_std_basis_one [decidable_eq n] (v : n → R) (i : n) :
  dot_product v (linear_map.std_basis R (λ _, R) i 1) = v i :=
by rw [dot_product_std_basis_eq_mul, mul_one]

lemma dot_product_eq
  (v w : n → R) (h : ∀ u, dot_product v u = dot_product w u) : v = w :=
begin
  funext x,
  classical,
  rw [← dot_product_std_basis_one v x, ← dot_product_std_basis_one w x, h],
end

lemma dot_product_eq_iff {v w : n → R} :
  (∀ u, dot_product v u = dot_product w u) ↔ v = w :=
⟨λ h, dot_product_eq v w h, λ h _, h ▸ rfl⟩

lemma dot_product_eq_zero (v : n → R) (h : ∀ w, dot_product v w = 0) : v = 0 :=
dot_product_eq _ _ $ λ u, (h u).symm ▸ (zero_dot_product u).symm

lemma dot_product_eq_zero_iff {v : n → R} : (∀ w, dot_product v w = 0) ↔ v = 0 :=
⟨λ h, dot_product_eq_zero v h, λ h w, h.symm ▸ zero_dot_product w⟩

end semiring

section self
variables [fintype n]

@[simp] lemma dot_product_self_eq_zero [linear_ordered_ring R] {v : n → R} :
  dot_product v v = 0 ↔ v = 0 :=
(finset.sum_eq_zero_iff_of_nonneg $ λ i _, mul_self_nonneg (v i)).trans $
  by simp [function.funext_iff]

/-- Note that this applies to `ℂ` via `complex.strict_ordered_comm_ring`. -/
@[simp] lemma dot_product_star_self_eq_zero
  [partial_order R] [non_unital_ring R] [star_ordered_ring R] [no_zero_divisors R] {v : n → R} :
  dot_product (star v) v = 0 ↔ v = 0 :=
(finset.sum_eq_zero_iff_of_nonneg $ λ i _, (@star_mul_self_nonneg _ _ _ _ (v i) : _)).trans $
  by simp [function.funext_iff, mul_eq_zero]

/-- Note that this applies to `ℂ` via `complex.strict_ordered_comm_ring`. -/
@[simp] lemma dot_product_self_star_eq_zero
  [partial_order R] [non_unital_ring R] [star_ordered_ring R] [no_zero_divisors R] {v : n → R} :
  dot_product v (star v) = 0 ↔ v = 0 :=
(finset.sum_eq_zero_iff_of_nonneg $ λ i _, (@star_mul_self_nonneg' _ _ _ _ (v i) : _)).trans $
  by simp [function.funext_iff, mul_eq_zero]

end self

end matrix
