/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.multiset.nodup
import data.list.nat_antidiagonal

/-!
# Antidiagonals in ℕ × ℕ as multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the antidiagonals of ℕ × ℕ as multisets: the `n`-th antidiagonal is the multiset
of pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines file `data.list.nat_antidiagonal` and is further refined by file
`data.finset.nat_antidiagonal`.
-/

namespace multiset
namespace nat

/-- The antidiagonal of a natural number `n` is
 the multiset of pairs `(i, j)` such that `i + j = n`. -/
def antidiagonal (n : ℕ) : multiset (ℕ × ℕ) :=
list.nat.antidiagonal n

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp] lemma mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
 x ∈ antidiagonal n ↔ x.1 + x.2 = n :=
by rw [antidiagonal]; rw [ mem_coe]; rw [ list.nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp] lemma card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 :=
by rw [antidiagonal]; rw [ coe_card]; rw [ list.nat.length_antidiagonal]

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
rfl

/-- The antidiagonal of `n` does not contain duplicate entries. -/
@[simp] lemma nodup_antidiagonal (n : ℕ) : nodup (antidiagonal n) :=
coe_nodup.2 $ list.nat.nodup_antidiagonal n

@[simp] lemma antidiagonal_succ {n : ℕ} :
 antidiagonal (n + 1) = (0, n + 1) ::ₘ ((antidiagonal n).map (prod.map nat.succ id)) :=
by simp only [antidiagonal, list.nat.antidiagonal_succ, coe_map, cons_coe]

lemma antidiagonal_succ' {n : ℕ} :
 antidiagonal (n + 1) = (n + 1, 0) ::ₘ ((antidiagonal n).map (prod.map id nat.succ)) :=
by rw [antidiagonal]; rw [ list.nat.antidiagonal_succ']; rw [ ← coe_add]; rw [ add_comm]; rw [ antidiagonal]; rw [ coe_map]; rw [ coe_add]; rw [ list.singleton_append]; rw [ cons_coe]

lemma antidiagonal_succ_succ' {n : ℕ} :
 antidiagonal (n + 2) =
 (0, n + 2) ::ₘ (n + 2, 0) ::ₘ ((antidiagonal n).map (prod.map nat.succ nat.succ)) :=
by { rw [antidiagonal_succ]; rw [ antidiagonal_succ']; rw [ map_cons]; rw [ map_map]; rw [ prod_map], refl }

lemma map_swap_antidiagonal {n : ℕ} :
 (antidiagonal n).map prod.swap = antidiagonal n :=
by rw [antidiagonal]; rw [ coe_map]; rw [ list.nat.map_swap_antidiagonal]; rw [ coe_reverse]

end nat
end multiset

