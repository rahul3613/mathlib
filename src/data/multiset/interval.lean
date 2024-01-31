/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.finset.locally_finite
import data.dfinsupp.interval
import data.dfinsupp.multiset
import data.nat.interval

/-!
# Finite intervals of multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for `multiset α` and calculates the
cardinality of its finite intervals.

## Implementation notes

We implement the intervals via the intervals on `dfinsupp`, rather than via filtering
`multiset.powerset`; this is because `(multiset.replicate n x).powerset` has `2^n` entries not `n+1`
entries as it contains duplicates. We do not go via `finsupp` as this would be noncomputable, and
multisets are typically used computationally.

-/

open finset dfinsupp function
open_locale big_operators pointwise

variables {α : Type*}

namespace multiset
variables [decidable_eq α] (s t : multiset α)

instance : locally_finite_order (multiset α) :=
locally_finite_order.of_Icc (multiset α)
  (λ s t, (finset.Icc s.to_dfinsupp t.to_dfinsupp).map
    (multiset.equiv_dfinsupp.to_equiv.symm.to_embedding))
  (λ s t x, by simp)

lemma Icc_eq :
  finset.Icc s t =
    (finset.Icc s.to_dfinsupp t.to_dfinsupp).map
      (multiset.equiv_dfinsupp.to_equiv.symm.to_embedding) := rfl

lemma uIcc_eq :
  uIcc s t =
    (uIcc s.to_dfinsupp t.to_dfinsupp).map
      (multiset.equiv_dfinsupp.to_equiv.symm.to_embedding) :=
(Icc_eq _ _).trans $ by simp [uIcc]

lemma card_Icc  :
  (finset.Icc s t).card = ∏ i in s.to_finset ∪ t.to_finset, (t.count i + 1 - s.count i) :=
by simp_rw [Icc_eq, finset.card_map, dfinsupp.card_Icc, nat.card_Icc, multiset.to_dfinsupp_apply,
  to_dfinsupp_support]

lemma card_Ico :
  (finset.Ico s t).card = ∏ i in s.to_finset ∪ t.to_finset, (t.count i + 1 - s.count i) - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioc :
  (finset.Ioc s t).card = ∏ i in s.to_finset ∪ t.to_finset, (t.count i + 1 - s.count i) - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioo :
  (finset.Ioo s t).card = ∏ i in s.to_finset ∪ t.to_finset, (t.count i + 1 - s.count i) - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

lemma card_uIcc :
  (uIcc s t).card = ∏ i in s.to_finset ∪ t.to_finset, ((t.count i - s.count i : ℤ).nat_abs + 1) :=
by simp_rw [uIcc_eq, finset.card_map, dfinsupp.card_uIcc, nat.card_uIcc, multiset.to_dfinsupp_apply,
  to_dfinsupp_support]

lemma card_Iic :
  (finset.Iic s).card = ∏ i in s.to_finset, (s.count i + 1) :=
by simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, to_finset_zero, empty_union, count_zero, tsub_zero]

end multiset
