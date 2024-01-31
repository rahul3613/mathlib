/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.int.cast.lemmas
import algebra.field.defs
import algebra.group_with_zero.units.lemmas

/-!
# Cast of integers into fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file concerns the canonical homomorphism `ℤ → F`, where `F` is a field.

## Main results

 * `int.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/

namespace int

open nat
variables {α : Type*}

/--
Auxiliary lemma for norm_cast to move the cast `-↑n` upwards to `↑-↑n`.

(The restriction to `division_ring` is necessary, otherwise this would also apply in the case where
`R = ℤ` and cause nontermination.)
-/
@[norm_cast]
lemma cast_neg_nat_cast {R} [division_ring R] (n : ℕ) : ((-n : ℤ) : R) = -n := by simp

@[simp] theorem cast_div [division_ring α] {m n : ℤ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) :
  ((m / n : ℤ) : α) = m / n :=
begin
  rcases n_dvd with ⟨k, rfl⟩,
  have : n ≠ 0, { rintro rfl, simpa using n_nonzero },
  rw [int.mul_div_cancel_left _ this, mul_comm n k, int.cast_mul, mul_div_cancel _ n_nonzero],
end

end int
