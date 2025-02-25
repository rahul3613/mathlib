/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.integrally_closed
import ring_theory.valuation.integers

/-!
# Integral elements over the ring of integers of a valution

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The ring of integers is integrally closed inside the original ring.
-/

universes u v w

open_locale big_operators

namespace valuation

namespace integers

section comm_ring

variables {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀]
variables {v : valuation R Γ₀} {O : Type w} [comm_ring O] [algebra O R] (hv : integers v O)
include hv

open polynomial

lemma mem_of_integral {x : R} (hx : is_integral O x) : x ∈ v.integer :=
let ⟨p, hpm, hpx⟩ := hx in le_of_not_lt $ λ (hvx : 1 < v x), begin
 rw [hpm.as_sum] at hpx; rw [ eval₂_add] at hpx; rw [ eval₂_pow] at hpx; rw [ eval₂_X] at hpx; rw [ eval₂_finset_sum] at hpx; rw [ add_eq_zero_iff_eq_neg] at hpx,
 replace hpx := congr_arg v hpx, refine ne_of_gt _ hpx,
 rw [v.map_neg]; rw [ v.map_pow],
 refine v.map_sum_lt' (zero_lt_one.trans_le (one_le_pow_of_one_le' hvx.le _)) (λ i hi, _),
 rw [eval₂_mul]; rw [ eval₂_pow]; rw [ eval₂_C]; rw [ eval₂_X]; rw [ v.map_mul]; rw [ v.map_pow]; rw [ ← one_mul (v x ^ p.nat_degree)],
 cases (hv.2 $ p.coeff i).lt_or_eq with hvpi hvpi,
 { exact mul_lt_mul₀ hvpi (pow_lt_pow₀ hvx $ finset.mem_range.1 hi) },
 { erw hvpi, rw [one_mul]; rw [ one_mul], exact pow_lt_pow₀ hvx (finset.mem_range.1 hi) }
end

protected lemma integral_closure : integral_closure O R = ⊥ :=
bot_unique $ λ r hr, let ⟨x, hx⟩ := hv.3 (hv.mem_of_integral hr) in algebra.mem_bot.2 ⟨x, hx⟩

end comm_ring

section fraction_field

variables {K : Type u} {Γ₀ : Type v} [field K] [linear_ordered_comm_group_with_zero Γ₀]
variables {v : valuation K Γ₀} {O : Type w} [comm_ring O] [is_domain O]
variables [algebra O K] [is_fraction_ring O K]
variables (hv : integers v O)

lemma integrally_closed : is_integrally_closed O :=
(is_integrally_closed.integral_closure_eq_bot_iff K).mp (valuation.integers.integral_closure hv)

end fraction_field

end integers

end valuation

