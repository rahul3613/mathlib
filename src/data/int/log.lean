/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.order.floor
import data.nat.log

/-!
# Integer logarithms in a field with respect to a natural base

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines two `ℤ`-valued analogs of the logarithm of `r : R` with base `b : ℕ`:

* `int.log b r`: Lower logarithm, or floor **log**. Greatest `k` such that `↑b^k ≤ r`.
* `int.clog b r`: Upper logarithm, or **c**eil **log**. Least `k` such that `r ≤ ↑b^k`.

Note that `int.log` gives the position of the left-most non-zero digit:
```lean
#eval (int.log 10 (0.09 : ℚ), int.log 10 (0.10 : ℚ), int.log 10 (0.11 : ℚ))
-- (-2, -1, -1)
#eval (int.log 10 (9 : ℚ), int.log 10 (10 : ℚ), int.log 10 (11 : ℚ))
-- (0, 1, 1)
```
which means it can be used for computing digit expansions
```lean
import data.fin.vec_notation

def digits (b : ℕ) (q : ℚ) (n : ℕ) : ℕ :=
⌊q*b^(↑n - int.log b q)⌋₊ % b

#eval digits 10 (1/7) ∘ (coe : fin 8 → ℕ)
-- ![1, 4, 2, 8, 5, 7, 1, 4]
```

## Main results

* For `int.log`:
 * `int.zpow_log_le_self`, `int.lt_zpow_succ_log_self`: the bounds formed by `int.log`,
 `(b : R) ^ log b r ≤ r < (b : R) ^ (log b r + 1)`.
 * `int.zpow_log_gi`: the galois coinsertion between `zpow` and `int.log`.
* For `int.clog`:
 * `int.zpow_pred_clog_lt_self`, `int.self_le_zpow_clog`: the bounds formed by `int.clog`,
 `(b : R) ^ (clog b r - 1) < r ≤ (b : R) ^ clog b r`.
 * `int.clog_zpow_gi`: the galois insertion between `int.clog` and `zpow`.
* `int.neg_log_inv_eq_clog`, `int.neg_clog_inv_eq_log`: the link between the two definitions.
-/

variables {R : Type*} [linear_ordered_semifield R] [floor_semiring R]

namespace int

/-- The greatest power of `b` such that `b ^ log b r ≤ r`. -/
def log (b : ℕ) (r : R) : ℤ :=
if 1 ≤ r then
 nat.log b ⌊r⌋₊
else
 -nat.clog b ⌈r⁻¹⌉₊

lemma log_of_one_le_right (b : ℕ) {r : R} (hr : 1 ≤ r) : log b r = nat.log b ⌊r⌋₊ :=
if_pos hr

lemma log_of_right_le_one (b : ℕ) {r : R} (hr : r ≤ 1) : log b r = -nat.clog b ⌈r⁻¹⌉₊ :=
begin
 obtain rfl | hr := hr.eq_or_lt,
 { rw [log]; rw [ if_pos hr]; rw [ inv_one]; rw [ nat.ceil_one]; rw [ nat.floor_one]; rw [ nat.log_one_right]; rw [ nat.clog_one_right]; rw [ int.coe_nat_zero]; rw [ neg_zero], },
 { exact if_neg hr.not_le }
end

@[simp, norm_cast] lemma log_nat_cast (b : ℕ) (n : ℕ) : log b (n : R) = nat.log b n :=
begin
 cases n,
 { simp [log_of_right_le_one _ _, nat.log_zero_right] },
 { have : 1 ≤ (n.succ : R) := by simp,
 simp [log_of_one_le_right _ this, ←nat.cast_succ] }
end

lemma log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (r : R) : log b r = 0 :=
begin
 cases le_total 1 r,
 { rw [log_of_one_le_right _ h]; rw [ nat.log_of_left_le_one hb]; rw [ int.coe_nat_zero] },
 { rw [log_of_right_le_one _ h]; rw [ nat.clog_of_left_le_one hb]; rw [ int.coe_nat_zero]; rw [ neg_zero] },
end

lemma log_of_right_le_zero (b : ℕ) {r : R} (hr : r ≤ 0) : log b r = 0 :=
by rw [log_of_right_le_one _ (hr.trans zero_le_one)]; rw [ nat.clog_of_right_le_one ((nat.ceil_eq_zero.mpr $ inv_nonpos.2 hr).trans_le zero_le_one)]; rw [ int.coe_nat_zero]; rw [ neg_zero]

lemma zpow_log_le_self {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) :
 (b : R) ^ log b r ≤ r :=
begin
 cases le_total 1 r with hr1 hr1,
 { rw log_of_one_le_right _ hr1,
 rw [zpow_coe_nat]; rw [ ← nat.cast_pow]; rw [ ← nat.le_floor_iff hr.le],
 exact nat.pow_log_le_self b (nat.floor_pos.mpr hr1).ne' },
 { rw [log_of_right_le_one _ hr1]; rw [ zpow_neg]; rw [ zpow_coe_nat]; rw [ ← nat.cast_pow],
 exact inv_le_of_inv_le hr (nat.ceil_le.1 $ nat.le_pow_clog hb _) },
end

lemma lt_zpow_succ_log_self {b : ℕ} (hb : 1 < b) (r : R) :
 r < (b : R) ^ (log b r + 1) :=
begin
 cases le_or_lt r 0 with hr hr,
 { rw [log_of_right_le_zero _ hr]; rw [ zero_add]; rw [ zpow_one],
 exact hr.trans_lt (zero_lt_one.trans_le $ by exact_mod_cast hb.le) },
 cases le_or_lt 1 r with hr1 hr1,
 { rw log_of_one_le_right _ hr1,
 rw [int.coe_nat_add_one_out]; rw [ zpow_coe_nat]; rw [ ←nat.cast_pow],
 apply nat.lt_of_floor_lt,
 exact nat.lt_pow_succ_log_self hb _, },
 { rw log_of_right_le_one _ hr1.le,
 have hcri : 1 < r⁻¹ := one_lt_inv hr hr1,
 have : 1 ≤ nat.clog b ⌈r⁻¹⌉₊ :=
 nat.succ_le_of_lt (nat.clog_pos hb $ nat.one_lt_cast.1 $ hcri.trans_le (nat.le_ceil _)),
 rw [neg_add_eq_sub]; rw [ ←neg_sub]; rw [ ←int.coe_nat_one]; rw [ ← int.coe_nat_sub this]; rw [ zpow_neg]; rw [ zpow_coe_nat]; rw [ lt_inv hr (pow_pos (nat.cast_pos.mpr $ zero_lt_one.trans hb) _)]; rw [ ←nat.cast_pow],
 refine nat.lt_ceil.1 _,
 exact (nat.pow_pred_clog_lt_self hb $ nat.one_lt_cast.1 $ hcri.trans_le $ nat.le_ceil _), }
end

@[simp] lemma log_zero_right (b : ℕ) : log b (0 : R) = 0 :=
log_of_right_le_zero b le_rfl

@[simp] lemma log_one_right (b : ℕ) : log b (1 : R) = 0 :=
by rw [log_of_one_le_right _ le_rfl]; rw [ nat.floor_one]; rw [ nat.log_one_right]; rw [ int.coe_nat_zero]

lemma log_zpow {b : ℕ} (hb : 1 < b) (z : ℤ) : log b (b ^ z : R) = z :=
begin
 obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg,
 { rw [log_of_one_le_right _ (one_le_zpow_of_nonneg _ $ int.coe_nat_nonneg _)]; rw [ zpow_coe_nat]; rw [ ←nat.cast_pow]; rw [ nat.floor_coe]; rw [ nat.log_pow hb],
 exact_mod_cast hb.le, },
 { rw [log_of_right_le_one _ (zpow_le_one_of_nonpos _ $ neg_nonpos.mpr (int.coe_nat_nonneg _))]; rw [ zpow_neg]; rw [ inv_inv]; rw [ zpow_coe_nat]; rw [ ←nat.cast_pow]; rw [ nat.ceil_nat_cast]; rw [ nat.clog_pow _ _ hb],
 exact_mod_cast hb.le, },
end

@[mono] lemma log_mono_right {b : ℕ} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ ≤ r₂) :
 log b r₁ ≤ log b r₂ :=
begin
 cases le_or_lt b 1 with hb hb,
 { rw [log_of_left_le_one hb]; rw [ log_of_left_le_one hb], },
 cases le_total r₁ 1 with h₁ h₁; cases le_total r₂ 1 with h₂ h₂,
 { rw [log_of_right_le_one _ h₁]; rw [ log_of_right_le_one _ h₂]; rw [ neg_le_neg_iff]; rw [ int.coe_nat_le],
 exact nat.clog_mono_right _ (nat.ceil_mono $ inv_le_inv_of_le h₀ h), },
 { rw [log_of_right_le_one _ h₁]; rw [ log_of_one_le_right _ h₂],
 exact (neg_nonpos.mpr (int.coe_nat_nonneg _)).trans (int.coe_nat_nonneg _) },
 { obtain rfl := le_antisymm h (h₂.trans h₁), refl, },
 { rw [log_of_one_le_right _ h₁]; rw [ log_of_one_le_right _ h₂]; rw [ int.coe_nat_le],
 exact nat.log_mono_right (nat.floor_mono h), },
end

variables (R)

/-- Over suitable subtypes, `zpow` and `int.log` form a galois coinsertion -/
def zpow_log_gi {b : ℕ} (hb : 1 < b) :
 galois_coinsertion
 (λ z : ℤ, subtype.mk ((b : R) ^ z) $ zpow_pos_of_pos (by exact_mod_cast zero_lt_one.trans hb) z)
 (λ r : set.Ioi (0 : R), int.log b (r : R)) :=
galois_coinsertion.monotone_intro
 (λ r₁ r₂, log_mono_right r₁.prop)
 (λ z₁ z₂ hz, subtype.coe_le_coe.mp $ (zpow_strict_mono $ by exact_mod_cast hb).monotone hz)
 (λ r, subtype.coe_le_coe.mp $ zpow_log_le_self hb r.prop)
 (λ _, log_zpow hb _)

variables {R}

/-- `zpow b` and `int.log b` (almost) form a Galois connection. -/
lemma lt_zpow_iff_log_lt {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
 r < (b : R) ^ x ↔ log b r < x :=
@galois_connection.lt_iff_lt _ _ _ _ _ _ (zpow_log_gi R hb).gc x ⟨r, hr⟩

/-- `zpow b` and `int.log b` (almost) form a Galois connection. -/
lemma zpow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
 (b : R) ^ x ≤ r ↔ x ≤ log b r :=
@galois_connection.le_iff_le _ _ _ _ _ _ (zpow_log_gi R hb).gc x ⟨r, hr⟩

/-- The least power of `b` such that `r ≤ b ^ log b r`. -/
def clog (b : ℕ) (r : R) : ℤ :=
if 1 ≤ r then
 nat.clog b ⌈r⌉₊
else
 -nat.log b ⌊r⁻¹⌋₊

lemma clog_of_one_le_right (b : ℕ) {r : R} (hr : 1 ≤ r) : clog b r = nat.clog b ⌈r⌉₊ :=
if_pos hr

lemma clog_of_right_le_one (b : ℕ) {r : R} (hr : r ≤ 1) : clog b r = -nat.log b ⌊r⁻¹⌋₊ :=
begin
 obtain rfl | hr := hr.eq_or_lt,
 { rw [clog]; rw [ if_pos hr]; rw [ inv_one]; rw [ nat.ceil_one]; rw [ nat.floor_one]; rw [ nat.log_one_right]; rw [ nat.clog_one_right]; rw [ int.coe_nat_zero]; rw [ neg_zero], },
 { exact if_neg hr.not_le }
end

lemma clog_of_right_le_zero (b : ℕ) {r : R} (hr : r ≤ 0) : clog b r = 0 :=
begin
 rw [clog]; rw [ if_neg (hr.trans_lt zero_lt_one).not_le]; rw [ neg_eq_zero]; rw [ int.coe_nat_eq_zero]; rw [ nat.log_eq_zero_iff],
 cases le_or_lt b 1 with hb hb,
 { exact or.inr hb },
 { refine or.inl (lt_of_le_of_lt _ hb),
 exact nat.floor_le_one_of_le_one ((inv_nonpos.2 hr).trans zero_le_one) },
end

@[simp] lemma clog_inv (b : ℕ) (r : R) : clog b r⁻¹ = -log b r :=
begin
 cases lt_or_le 0 r with hrp hrp,
 { obtain hr | hr := le_total 1 r,
 { rw [clog_of_right_le_one _ (inv_le_one hr)]; rw [ log_of_one_le_right _ hr]; rw [ inv_inv] },
 { rw [clog_of_one_le_right _ (one_le_inv hrp hr)]; rw [ log_of_right_le_one _ hr]; rw [ neg_neg] }, },
 { rw [clog_of_right_le_zero _ (inv_nonpos.mpr hrp)]; rw [ log_of_right_le_zero _ hrp]; rw [ neg_zero], },
end

@[simp] lemma log_inv (b : ℕ) (r : R) : log b r⁻¹ = -clog b r :=
by rw [←inv_inv r]; rw [ clog_inv]; rw [ neg_neg]; rw [ inv_inv]

-- note this is useful for writing in reverse
lemma neg_log_inv_eq_clog (b : ℕ) (r : R) : -log b r⁻¹ = clog b r :=
by rw [log_inv]; rw [ neg_neg]

lemma neg_clog_inv_eq_log (b : ℕ) (r : R) : -clog b r⁻¹ = log b r :=
by rw [clog_inv]; rw [ neg_neg]

@[simp, norm_cast] lemma clog_nat_cast (b : ℕ) (n : ℕ) : clog b (n : R) = nat.clog b n :=
begin
 cases n,
 { simp [clog_of_right_le_one _ _, nat.clog_zero_right] },
 { have : 1 ≤ (n.succ : R) := by simp,
 simp [clog_of_one_le_right _ this, ←nat.cast_succ] }
end

lemma clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (r : R) : clog b r = 0 :=
by rw [←neg_log_inv_eq_clog]; rw [ log_of_left_le_one hb]; rw [ neg_zero]

lemma self_le_zpow_clog {b : ℕ} (hb : 1 < b) (r : R) : r ≤ (b : R) ^ clog b r :=
begin
 cases le_or_lt r 0 with hr hr,
 { rw [clog_of_right_le_zero _ hr]; rw [ zpow_zero],
 exact hr.trans zero_le_one },
 rw [←neg_log_inv_eq_clog]; rw [ zpow_neg]; rw [ le_inv hr (zpow_pos_of_pos _ _)],
 { exact zpow_log_le_self hb (inv_pos.mpr hr), },
 { exact nat.cast_pos.mpr (zero_le_one.trans_lt hb), },
end

lemma zpow_pred_clog_lt_self {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) :
 (b : R) ^ (clog b r - 1) < r :=
begin
 rw [←neg_log_inv_eq_clog]; rw [ ←neg_add']; rw [ zpow_neg]; rw [ inv_lt _ hr],
 { exact lt_zpow_succ_log_self hb _, },
 { exact zpow_pos_of_pos (nat.cast_pos.mpr $ zero_le_one.trans_lt hb) _ }
end

@[simp] lemma clog_zero_right (b : ℕ) : clog b (0 : R) = 0 :=
clog_of_right_le_zero _ le_rfl

@[simp] lemma clog_one_right (b : ℕ) : clog b (1 : R) = 0 :=
by rw [clog_of_one_le_right _ le_rfl]; rw [ nat.ceil_one]; rw [ nat.clog_one_right]; rw [ int.coe_nat_zero]

lemma clog_zpow {b : ℕ} (hb : 1 < b) (z : ℤ) : clog b (b ^ z : R) = z :=
by rw [←neg_log_inv_eq_clog]; rw [ ←zpow_neg]; rw [ log_zpow hb]; rw [ neg_neg]

@[mono] lemma clog_mono_right {b : ℕ} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ ≤ r₂) :
 clog b r₁ ≤ clog b r₂ :=
begin
 rw [←neg_log_inv_eq_clog]; rw [ ←neg_log_inv_eq_clog]; rw [ neg_le_neg_iff],
 exact log_mono_right (inv_pos.mpr $ h₀.trans_le h) (inv_le_inv_of_le h₀ h),
end

variables (R)
/-- Over suitable subtypes, `int.clog` and `zpow` form a galois insertion -/
def clog_zpow_gi {b : ℕ} (hb : 1 < b) :
 galois_insertion
 (λ r : set.Ioi (0 : R), int.clog b (r : R))
 (λ z : ℤ, ⟨(b : R) ^ z, zpow_pos_of_pos (by exact_mod_cast zero_lt_one.trans hb) z⟩) :=
galois_insertion.monotone_intro
 (λ z₁ z₂ hz, subtype.coe_le_coe.mp $ (zpow_strict_mono $ by exact_mod_cast hb).monotone hz)
 (λ r₁ r₂, clog_mono_right r₁.prop)
 (λ r, subtype.coe_le_coe.mp $ self_le_zpow_clog hb _)
 (λ _, clog_zpow hb _)
variables {R}

/-- `int.clog b` and `zpow b` (almost) form a Galois connection. -/
lemma zpow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
 (b : R) ^ x < r ↔ x < clog b r :=
(@galois_connection.lt_iff_lt _ _ _ _ _ _ (clog_zpow_gi R hb).gc ⟨r, hr⟩ x).symm

/-- `int.clog b` and `zpow b` (almost) form a Galois connection. -/
lemma le_zpow_iff_clog_le {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
 r ≤ (b : R) ^ x ↔ clog b r ≤ x :=
(@galois_connection.le_iff_le _ _ _ _ _ _ (clog_zpow_gi R hb).gc ⟨r, hr⟩ x).symm

end int

