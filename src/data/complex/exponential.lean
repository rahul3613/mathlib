/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
import algebra.geom_sum
import data.complex.basic
import data.nat.choose.sum

/-!
# Exponential, trigonometric and hyperbolic trigonometric functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definitions of the real and complex exponential, sine, cosine, tangent,
hyperbolic sine, hyperbolic cosine, and hyperbolic tangent functions.

-/

local notation `abs'` := has_abs.abs
open is_absolute_value
open_locale classical big_operators nat complex_conjugate

section
open real is_absolute_value finset

section
variables {α : Type*} {β : Type*} [ring β]
 [linear_ordered_field α] [archimedean α] {abv : β → α} [is_absolute_value abv]

lemma is_cau_of_decreasing_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
 (hnm : ∀ n ≥ m, f n.succ ≤ f n) : is_cau_seq abs f :=
λ ε ε0,
let ⟨k, hk⟩ := archimedean.arch a ε0 in
have h : ∃ l, ∀ n ≥ m, a - l • ε < f n :=
 ⟨k + k + 1, λ n hnm, lt_of_lt_of_le
 (show a - (k + (k + 1)) • ε < -|f n|,
 from lt_neg.1 $ lt_of_le_of_lt (ham n hnm) (begin
 rw [neg_sub]; rw [ lt_sub_iff_add_lt]; rw [ add_nsmul]; rw [ add_nsmul]; rw [ one_nsmul],
 exact add_lt_add_of_le_of_lt hk (lt_of_le_of_lt hk
 (lt_add_of_pos_right _ ε0)),
 end))
 (neg_le.2 $ (abs_neg (f n)) ▸ le_abs_self _)⟩,
let l := nat.find h in
have hl : ∀ (n : ℕ), n ≥ m → f n > a - l • ε := nat.find_spec h,
have hl0 : l ≠ 0 := λ hl0, not_lt_of_ge (ham m le_rfl)
 (lt_of_lt_of_le (by have := hl m (le_refl m); simpa [hl0] using this) (le_abs_self (f m))),
begin
 cases not_forall.1
 (nat.find_min h (nat.pred_lt hl0)) with i hi,
 rw [not_imp] at hi; rw [ not_lt] at hi,
 existsi i,
 assume j hj,
 have hfij : f j ≤ f i := (nat.rel_of_forall_rel_succ_of_le_of_le (≥) hnm hi.1 hj).le,
 rw [abs_of_nonpos (sub_nonpos.2 hfij)]; rw [ neg_sub]; rw [ sub_lt_iff_lt_add'],
 calc f i ≤ a - (nat.pred l) • ε : hi.2
 ... = a - l • ε + ε :
 by conv {to_rhs, rw [← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hl0)]; rw [ succ_nsmul']; rw [ sub_add]; rw [ add_sub_cancel] }
 ... < f j + ε : add_lt_add_right (hl j (le_trans hi.1 hj)) _
end

lemma is_cau_of_mono_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
 (hnm : ∀ n ≥ m, f n ≤ f n.succ) : is_cau_seq abs f :=
begin
 refine @eq.rec_on (ℕ → α) _ (is_cau_seq abs) _ _
 (-⟨_, @is_cau_of_decreasing_bounded _ _ _ (λ n, -f n) a m (by simpa) (by simpa)⟩ :
 cau_seq α abs).2,
 ext,
 exact neg_neg _
end

end

section no_archimedean
variables {α : Type*} {β : Type*} [ring β]
 [linear_ordered_field α] {abv : β → α} [is_absolute_value abv]

lemma is_cau_series_of_abv_le_cau {f : ℕ → β} {g : ℕ → α} (n : ℕ) :
 (∀ m, n ≤ m → abv (f m) ≤ g m) →
 is_cau_seq abs (λ n, ∑ i in range n, g i) →
 is_cau_seq abv (λ n, ∑ i in range n, f i) :=
begin
 assume hm hg ε ε0,
 cases hg (ε / 2) (div_pos ε0 (by norm_num)) with i hi,
 existsi max n i,
 assume j ji,
 have hi₁ := hi j (le_trans (le_max_right n i) ji),
 have hi₂ := hi (max n i) (le_max_right n i),
 have sub_le := abs_sub_le (∑ k in range j, g k) (∑ k in range i, g k)
 (∑ k in range (max n i), g k),
 have := add_lt_add hi₁ hi₂,
 rw [abs_sub_comm (∑ k in range (max n i), g k)] at this; rw [ add_halves ε] at this,
 refine lt_of_le_of_lt (le_trans (le_trans _ (le_abs_self _)) sub_le) this,
 generalize hk : j - max n i = k,
 clear this hi₂ hi₁ hi ε0 ε hg sub_le,
 rw tsub_eq_iff_eq_add_of_le ji at hk,
 rw hk,
 clear hk ji j,
 induction k with k' hi,
 { simp [abv_zero abv] },
 { simp only [nat.succ_add, sum_range_succ_comm, sub_eq_add_neg, add_assoc],
 refine le_trans (abv_add _ _ _) _,
 simp only [sub_eq_add_neg] at hi,
 exact add_le_add (hm _ (le_add_of_nonneg_of_le (nat.zero_le _) (le_max_left _ _))) hi },
end

lemma is_cau_series_of_abv_cau {f : ℕ → β} : is_cau_seq abs (λ m, ∑ n in range m, abv (f n))
 → is_cau_seq abv (λ m, ∑ n in range m, f n) :=
is_cau_series_of_abv_le_cau 0 (λ n h, le_rfl)

end no_archimedean

section
variables {α : Type*} [linear_ordered_field α] [archimedean α]

lemma is_cau_geo_series {β : Type*} [ring β] [nontrivial β] {abv : β → α} [is_absolute_value abv]
 (x : β) (hx1 : abv x < 1) : is_cau_seq abv (λ n, ∑ m in range n, x ^ m) :=
have hx1' : abv x ≠ 1 := λ h, by simpa [h, lt_irrefl] using hx1,
is_cau_series_of_abv_cau
begin
 simp only [abv_pow abv, geom_sum_eq hx1'],
 conv in (_ / _) { rw [← neg_div_neg_eq]; rw [ neg_sub]; rw [ neg_sub] },
 refine @is_cau_of_mono_bounded _ _ _ _ ((1 : α) / (1 - abv x)) 0 _ _,
 { assume n hn,
 rw abs_of_nonneg,
 refine div_le_div_of_le (le_of_lt $ sub_pos.2 hx1)
 (sub_le_self _ (abv_pow abv x n ▸ abv_nonneg _ _)),
 refine div_nonneg (sub_nonneg.2 _) (sub_nonneg.2 $ le_of_lt hx1),
 clear hn,
 induction n with n ih,
 { simp },
 { rw [pow_succ]; rw [ ← one_mul (1 : α)],
 refine mul_le_mul (le_of_lt hx1) ih (abv_pow abv x n ▸ abv_nonneg _ _) (by norm_num) } },
 { assume n hn,
 refine div_le_div_of_le (le_of_lt $ sub_pos.2 hx1) (sub_le_sub_left _ _),
 rw [← one_mul (_ ^ n)]; rw [ pow_succ],
 exact mul_le_mul_of_nonneg_right (le_of_lt hx1) (pow_nonneg (abv_nonneg _ _) _) }
end

lemma is_cau_geo_series_const (a : α) {x : α} (hx1 : |x| < 1) :
 is_cau_seq abs (λ m, ∑ n in range m, a * x ^ n) :=
have is_cau_seq abs (λ m, a * ∑ n in range m, x ^ n) :=
 (cau_seq.const abs a * ⟨_, is_cau_geo_series x hx1⟩).2,
by simpa only [mul_sum]

variables {β : Type*} [ring β] {abv : β → α} [is_absolute_value abv]

lemma series_ratio_test {f : ℕ → β} (n : ℕ) (r : α)
 (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ m, n ≤ m → abv (f m.succ) ≤ r * abv (f m)) :
 is_cau_seq abv (λ m, ∑ n in range m, f n) :=
have har1 : |r| < 1, by rwa abs_of_nonneg hr0,
begin
 refine is_cau_series_of_abv_le_cau n.succ _
 (is_cau_geo_series_const (abv (f n.succ) * r⁻¹ ^ n.succ) har1),
 assume m hmn,
 cases classical.em (r = 0) with r_zero r_ne_zero,
 { have m_pos := lt_of_lt_of_le (nat.succ_pos n) hmn,
 have := h m.pred (nat.le_of_succ_le_succ (by rwa [nat.succ_pred_eq_of_pos m_pos])),
 simpa [r_zero, nat.succ_pred_eq_of_pos m_pos, pow_succ] },
 generalize hk : m - n.succ = k,
 have r_pos : 0 < r := lt_of_le_of_ne hr0 (ne.symm r_ne_zero),
 replace hk : m = k + n.succ := (tsub_eq_iff_eq_add_of_le hmn).1 hk,
 induction k with k ih generalizing m n,
 { rw [hk]; rw [ zero_add]; rw [ mul_right_comm]; rw [ inv_pow _ _]; rw [ ← div_eq_mul_inv]; rw [ mul_div_cancel],
 exact (ne_of_lt (pow_pos r_pos _)).symm },
 { have kn : k + n.succ ≥ n.succ, by rw ← zero_add n.succ; exact add_le_add (zero_le _) (by simp),
 rw [hk]; rw [ nat.succ_add]; rw [ pow_succ' r]; rw [ ← mul_assoc],
 exact le_trans (by rw mul_comm; exact h _ (nat.le_of_succ_le kn))
 (mul_le_mul_of_nonneg_right (ih (k + n.succ) n h kn rfl) hr0) }
end

lemma sum_range_diag_flip {α : Type*} [add_comm_monoid α] (n : ℕ) (f : ℕ → ℕ → α) :
 ∑ m in range n, ∑ k in range (m + 1), f k (m - k) =
 ∑ m in range n, ∑ k in range (n - m), f m k :=
by rw [sum_sigma']; rw [ sum_sigma']; exact sum_bij
(λ a _, ⟨a.2, a.1 - a.2⟩)
(λ a ha, have h₁ : a.1 < n := mem_range.1 (mem_sigma.1 ha).1,
 have h₂ : a.2 < nat.succ a.1 := mem_range.1 (mem_sigma.1 ha).2,
 mem_sigma.2 ⟨mem_range.2 (lt_of_lt_of_le h₂ h₁),
 mem_range.2 ((tsub_lt_tsub_iff_right (nat.le_of_lt_succ h₂)).2 h₁)⟩)
(λ _ _, rfl)
(λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h,
 have ha : a₁ < n ∧ a₂ ≤ a₁ :=
 ⟨mem_range.1 (mem_sigma.1 ha).1, nat.le_of_lt_succ (mem_range.1 (mem_sigma.1 ha).2)⟩,
 have hb : b₁ < n ∧ b₂ ≤ b₁ :=
 ⟨mem_range.1 (mem_sigma.1 hb).1, nat.le_of_lt_succ (mem_range.1 (mem_sigma.1 hb).2)⟩,
 have h : a₂ = b₂ ∧ _ := sigma.mk.inj h,
 have h' : a₁ = b₁ - b₂ + a₂ := (tsub_eq_iff_eq_add_of_le ha.2).1 (eq_of_heq h.2),
 sigma.mk.inj_iff.2
 ⟨tsub_add_cancel_of_le hb.2 ▸ h'.symm ▸ h.1 ▸ rfl,
 (heq_of_eq h.1)⟩)
(λ ⟨a₁, a₂⟩ ha,
 have ha : a₁ < n ∧ a₂ < n - a₁ :=
 ⟨mem_range.1 (mem_sigma.1 ha).1, (mem_range.1 (mem_sigma.1 ha).2)⟩,
 ⟨⟨a₂ + a₁, a₁⟩, ⟨mem_sigma.2 ⟨mem_range.2 (lt_tsub_iff_right.1 ha.2),
 mem_range.2 (nat.lt_succ_of_le (nat.le_add_left _ _))⟩,
 sigma.mk.inj_iff.2 ⟨rfl, heq_of_eq (add_tsub_cancel_right _ _).symm⟩⟩⟩)

end

section no_archimedean
variables {α : Type*} {β : Type*} [linear_ordered_field α] {abv : β → α}

section
variables [semiring β] [is_absolute_value abv]

lemma abv_sum_le_sum_abv {γ : Type*} (f : γ → β) (s : finset γ) :
 abv (∑ k in s, f k) ≤ ∑ k in s, abv (f k) :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s (by simp [abv_zero abv])
 (λ a s has ih, by rw [sum_insert has]; rw [ sum_insert has];
 exact le_trans (abv_add abv _ _) (add_le_add_left ih _))

end

section
variables [ring β] [is_absolute_value abv]

lemma cauchy_product {a b : ℕ → β}
 (ha : is_cau_seq abs (λ m, ∑ n in range m, abv (a n)))
 (hb : is_cau_seq abv (λ m, ∑ n in range m, b n)) (ε : α) (ε0 : 0 < ε) :
 ∃ i : ℕ, ∀ j ≥ i, abv ((∑ k in range j, a k) * (∑ k in range j, b k) -
 ∑ n in range j, ∑ m in range (n + 1), a m * b (n - m)) < ε :=
let ⟨Q, hQ⟩ := cau_seq.bounded ⟨_, hb⟩ in
let ⟨P, hP⟩ := cau_seq.bounded ⟨_, ha⟩ in
have hP0 : 0 < P, from lt_of_le_of_lt (abs_nonneg _) (hP 0),
have hPε0 : 0 < ε / (2 * P),
 from div_pos ε0 (mul_pos (show (2 : α) > 0, from by norm_num) hP0),
let ⟨N, hN⟩ := cau_seq.cauchy₂ ⟨_, hb⟩ hPε0 in
have hQε0 : 0 < ε / (4 * Q),
 from div_pos ε0 (mul_pos (show (0 : α) < 4, by norm_num)
 (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))),
let ⟨M, hM⟩ := cau_seq.cauchy₂ ⟨_, ha⟩ hQε0 in
⟨2 * (max N M + 1), λ K hK,
have h₁ : ∑ m in range K, ∑ k in range (m + 1), a k * b (m - k) =
 ∑ m in range K, ∑ n in range (K - m), a m * b n,
 by simpa using sum_range_diag_flip K (λ m n, a m * b n),
have h₂ : (λ i, ∑ k in range (K - i), a i * b k) = (λ i, a i * ∑ k in range (K - i), b k),
 by simp [finset.mul_sum],
have h₃ : ∑ i in range K, a i * ∑ k in range (K - i), b k =
 ∑ i in range K, a i * (∑ k in range (K - i), b k - ∑ k in range K, b k)
 + ∑ i in range K, a i * ∑ k in range K, b k,
 by rw ← sum_add_distrib; simp [(mul_add _ _ _).symm],
have two_mul_two : (4 : α) = 2 * 2, by norm_num,
have hQ0 : Q ≠ 0, from λ h, by simpa [h, lt_irrefl] using hQε0,
have h2Q0 : 2 * Q ≠ 0, from mul_ne_zero two_ne_zero hQ0,
have hε : ε / (2 * P) * P + ε / (4 * Q) * (2 * Q) = ε,
 by rw [← div_div]; rw [ div_mul_cancel _ (ne.symm (ne_of_lt hP0))]; rw [ two_mul_two]; rw [ mul_assoc]; rw [ ← div_div]; rw [ div_mul_cancel _ h2Q0]; rw [ add_halves],
have hNMK : max N M + 1 < K,
 from lt_of_lt_of_le (by rw two_mul; exact lt_add_of_pos_left _ (nat.succ_pos _)) hK,
have hKN : N < K,
 from calc N ≤ max N M : le_max_left _ _
 ... < max N M + 1 : nat.lt_succ_self _
 ... < K : hNMK,
have hsumlesum : ∑ i in range (max N M + 1), abv (a i) *
 abv (∑ k in range (K - i), b k - ∑ k in range K, b k) ≤
 ∑ i in range (max N M + 1), abv (a i) * (ε / (2 * P)),
 from sum_le_sum (λ m hmJ, mul_le_mul_of_nonneg_left
 (le_of_lt (hN (K - m)
 (le_tsub_of_add_le_left (le_trans
 (by rw two_mul; exact add_le_add (le_of_lt (mem_range.1 hmJ))
 (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))) hK)) K
 (le_of_lt hKN))) (abv_nonneg abv _)),
have hsumltP : ∑ n in range (max N M + 1), abv (a n) < P :=
 calc ∑ n in range (max N M + 1), abv (a n)
 = |∑ n in range (max N M + 1), abv (a n)| :
 eq.symm (abs_of_nonneg (sum_nonneg (λ x h, abv_nonneg abv (a x))))
 ... < P : hP (max N M + 1),
begin
 rw [h₁]; rw [ h₂]; rw [ h₃]; rw [ sum_mul]; rw [ ← sub_sub]; rw [ sub_right_comm]; rw [ sub_self]; rw [ zero_sub]; rw [ abv_neg abv],
 refine lt_of_le_of_lt (abv_sum_le_sum_abv _ _) _,
 suffices : ∑ i in range (max N M + 1),
 abv (a i) * abv (∑ k in range (K - i), b k - ∑ k in range K, b k) +
 (∑ i in range K, abv (a i) * abv (∑ k in range (K - i), b k - ∑ k in range K, b k) -
 ∑ i in range (max N M + 1), abv (a i) * abv (∑ k in range (K - i), b k - ∑ k in range K, b k)) <
 ε / (2 * P) * P + ε / (4 * Q) * (2 * Q),
 { rw hε at this, simpa [abv_mul abv] },
 refine add_lt_add (lt_of_le_of_lt hsumlesum
 (by rw [← sum_mul]; rw [ mul_comm]; exact (mul_lt_mul_left hPε0).mpr hsumltP)) _,
 rw sum_range_sub_sum_range (le_of_lt hNMK),
 calc ∑ i in (range K).filter (λ k, max N M + 1 ≤ k),
 abv (a i) * abv (∑ k in range (K - i), b k - ∑ k in range K, b k)
 ≤ ∑ i in (range K).filter (λ k, max N M + 1 ≤ k), abv (a i) * (2 * Q) :
 sum_le_sum (λ n hn, begin
 refine mul_le_mul_of_nonneg_left _ (abv_nonneg _ _),
 rw sub_eq_add_neg,
 refine le_trans (abv_add _ _ _) _,
 rw [two_mul]; rw [ abv_neg abv],
 exact add_le_add (le_of_lt (hQ _)) (le_of_lt (hQ _)),
 end)
 ... < ε / (4 * Q) * (2 * Q) :
 by rw [← sum_mul]; rw [ ← sum_range_sub_sum_range (le_of_lt hNMK)];
 refine (mul_lt_mul_right $ by rw two_mul;
 exact add_pos (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))
 (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))).2
 (lt_of_le_of_lt (le_abs_self _)
 (hM _ (le_trans (nat.le_succ_of_le (le_max_right _ _)) (le_of_lt hNMK)) _
 (nat.le_succ_of_le (le_max_right _ _))))
end⟩

end

end no_archimedean

end

open finset

open cau_seq

namespace complex

lemma is_cau_abs_exp (z : ℂ) : is_cau_seq has_abs.abs
 (λ n, ∑ m in range n, abs (z ^ m / m!)) :=
let ⟨n, hn⟩ := exists_nat_gt (abs z) in
have hn0 : (0 : ℝ) < n, from lt_of_le_of_lt (abs.nonneg _) hn,
series_ratio_test n (complex.abs z / n) (div_nonneg (abs.nonneg _) (le_of_lt hn0))
 (by rwa [div_lt_iff hn0]; rwa [ one_mul])
 (λ m hm,
 by rw [abs_abs]; rw [ abs_abs]; rw [ nat.factorial_succ]; rw [ pow_succ]; rw [ mul_comm m.succ]; rw [ nat.cast_mul]; rw [ ← div_div]; rw [ mul_div_assoc]; rw [ mul_div_right_comm]; rw [ abs.map_mul]; rw [ map_div₀]; rw [ abs_cast_nat];
 exact mul_le_mul_of_nonneg_right
 (div_le_div_of_le_left (abs.nonneg _) hn0
 (nat.cast_le.2 (le_trans hm (nat.le_succ _)))) (abs.nonneg _))

noncomputable theory

lemma is_cau_exp (z : ℂ) :
 is_cau_seq abs (λ n, ∑ m in range n, z ^ m / m!) :=
is_cau_series_of_abv_cau (is_cau_abs_exp z)

/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
@[pp_nodot] def exp' (z : ℂ) :
 cau_seq ℂ complex.abs :=
⟨λ n, ∑ m in range n, z ^ m / m!, is_cau_exp z⟩

/-- The complex exponential function, defined via its Taylor series -/
@[irreducible, pp_nodot] def exp (z : ℂ) : ℂ := lim (exp' z)

/-- The complex sine function, defined via `exp` -/
@[pp_nodot] def sin (z : ℂ) : ℂ := ((exp (-z * I) - exp (z * I)) * I) / 2

/-- The complex cosine function, defined via `exp` -/
@[pp_nodot] def cos (z : ℂ) : ℂ := (exp (z * I) + exp (-z * I)) / 2

/-- The complex tangent function, defined as `sin z / cos z` -/
@[pp_nodot] def tan (z : ℂ) : ℂ := sin z / cos z

/-- The complex hyperbolic sine function, defined via `exp` -/
@[pp_nodot] def sinh (z : ℂ) : ℂ := (exp z - exp (-z)) / 2

/-- The complex hyperbolic cosine function, defined via `exp` -/
@[pp_nodot] def cosh (z : ℂ) : ℂ := (exp z + exp (-z)) / 2

/-- The complex hyperbolic tangent function, defined as `sinh z / cosh z` -/
@[pp_nodot] def tanh (z : ℂ) : ℂ := sinh z / cosh z

end complex

namespace real

open complex

/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot] def exp (x : ℝ) : ℝ := (exp x).re

/-- The real sine function, defined as the real part of the complex sine -/
@[pp_nodot] def sin (x : ℝ) : ℝ := (sin x).re

/-- The real cosine function, defined as the real part of the complex cosine -/
@[pp_nodot] def cos (x : ℝ) : ℝ := (cos x).re

/-- The real tangent function, defined as the real part of the complex tangent -/
@[pp_nodot] def tan (x : ℝ) : ℝ := (tan x).re

/-- The real hypebolic sine function, defined as the real part of the complex hyperbolic sine -/
@[pp_nodot] def sinh (x : ℝ) : ℝ := (sinh x).re

/-- The real hypebolic cosine function, defined as the real part of the complex hyperbolic cosine -/
@[pp_nodot] def cosh (x : ℝ) : ℝ := (cosh x).re

/-- The real hypebolic tangent function, defined as the real part of
the complex hyperbolic tangent -/
@[pp_nodot] def tanh (x : ℝ) : ℝ := (tanh x).re

end real

namespace complex

variables (x y : ℂ)

@[simp] lemma exp_zero : exp 0 = 1 :=
begin
 rw exp,
 refine lim_eq_of_equiv_const (λ ε ε0, ⟨1, λ j hj, _⟩),
 convert ε0,
 cases j,
 { exact absurd hj (not_le_of_gt zero_lt_one) },
 { dsimp [exp'],
 induction j with j ih,
 { dsimp [exp']; simp },
 { rw ← ih dec_trivial,
 simp only [sum_range_succ, pow_succ],
 simp } }
end

lemma exp_add : exp (x + y) = exp x * exp y :=
begin
 have hj : ∀ j : ℕ, ∑ m in range j, (x + y) ^ m / m! =
 ∑ i in range j, ∑ k in range (i + 1), x ^ k / k! * (y ^ (i - k) / (i - k)!),
 { assume j,
 refine finset.sum_congr rfl (λ m hm, _),
 rw [add_pow]; rw [ div_eq_mul_inv]; rw [ sum_mul],
 refine finset.sum_congr rfl (λ i hi, _),
 have h₁ : (m.choose i : ℂ) ≠ 0 := nat.cast_ne_zero.2
 (pos_iff_ne_zero.1 (nat.choose_pos (nat.le_of_lt_succ (mem_range.1 hi)))),
 have h₂ := nat.choose_mul_factorial_mul_factorial (nat.le_of_lt_succ $ finset.mem_range.1 hi),
 rw [← h₂]; rw [ nat.cast_mul]; rw [ nat.cast_mul]; rw [ mul_inv]; rw [ mul_inv],
 simp only [mul_left_comm (m.choose i : ℂ), mul_assoc, mul_left_comm (m.choose i : ℂ)⁻¹,
 mul_comm (m.choose i : ℂ)],
 rw inv_mul_cancel h₁,
 simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] },
 simp_rw [exp, exp', lim_mul_lim],
 apply (lim_eq_lim_of_equiv _).symm,
 simp only [hj],
 exact cauchy_product (is_cau_abs_exp x) (is_cau_exp y)
end

lemma exp_list_sum (l : list ℂ) : exp l.sum = (l.map exp).prod :=
@monoid_hom.map_list_prod (multiplicative ℂ) ℂ _ _ ⟨exp, exp_zero, exp_add⟩ l

lemma exp_multiset_sum (s : multiset ℂ) : exp s.sum = (s.map exp).prod :=
@monoid_hom.map_multiset_prod (multiplicative ℂ) ℂ _ _ ⟨exp, exp_zero, exp_add⟩ s

lemma exp_sum {α : Type*} (s : finset α) (f : α → ℂ) : exp (∑ x in s, f x) = ∏ x in s, exp (f x) :=
@monoid_hom.map_prod (multiplicative ℂ) α ℂ _ _ ⟨exp, exp_zero, exp_add⟩ f s

lemma exp_nat_mul (x : ℂ) : ∀ n : ℕ, exp(n*x) = (exp x)^n
| 0 := by rw [nat.cast_zero]; rw [ zero_mul]; rw [ exp_zero]; rw [ pow_zero]
| (nat.succ n) := by rw [pow_succ']; rw [ nat.cast_add_one]; rw [ add_mul]; rw [ exp_add]; rw [ ←exp_nat_mul]; rw [ one_mul]

lemma exp_ne_zero : exp x ≠ 0 :=
λ h, zero_ne_one $ by rw [← exp_zero]; rw [ ← add_neg_self x]; rw [ exp_add]; rw [ h]; simp

lemma exp_neg : exp (-x) = (exp x)⁻¹ :=
by rw [← mul_right_inj' (exp_ne_zero x)]; rw [ ← exp_add];
 simp [mul_inv_cancel (exp_ne_zero x)]

lemma exp_sub : exp (x - y) = exp x / exp y :=
by simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

lemma exp_int_mul (z : ℂ) (n : ℤ) : complex.exp (n * z) = (complex.exp z) ^ n :=
begin
 cases n,
 { apply complex.exp_nat_mul },
 { simpa [complex.exp_neg, add_comm, ← neg_mul]
 using complex.exp_nat_mul (-z) (1 + n) },
end

@[simp] lemma exp_conj : exp (conj x) = conj (exp x) :=
begin
 dsimp [exp],
 rw [← lim_conj],
 refine congr_arg lim (cau_seq.ext (λ _, _)),
 dsimp [exp', function.comp, cau_seq_conj],
 rw (star_ring_end _).map_sum,
 refine sum_congr rfl (λ n hn, _),
 rw [map_div₀]; rw [ map_pow]; rw [ ← of_real_nat_cast]; rw [ conj_of_real]
end

@[simp] lemma of_real_exp_of_real_re (x : ℝ) : ((exp x).re : ℂ) = exp x :=
conj_eq_iff_re.1 $ by rw [← exp_conj]; rw [ conj_of_real]

@[simp, norm_cast] lemma of_real_exp (x : ℝ) : (real.exp x : ℂ) = exp x :=
of_real_exp_of_real_re _

@[simp] lemma exp_of_real_im (x : ℝ) : (exp x).im = 0 :=
by rw [← of_real_exp_of_real_re]; rw [ of_real_im]

lemma exp_of_real_re (x : ℝ) : (exp x).re = real.exp x := rfl

lemma two_sinh : 2 * sinh x = exp x - exp (-x) :=
mul_div_cancel' _ two_ne_zero

lemma two_cosh : 2 * cosh x = exp x + exp (-x) :=
mul_div_cancel' _ two_ne_zero

@[simp] lemma sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp] lemma sinh_neg : sinh (-x) = -sinh x :=
by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

private lemma sinh_add_aux {a b c d : ℂ} :
 (a - b) * (c + d) + (a + b) * (c - d) = 2 * (a * c - b * d) := by ring

lemma sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y :=
begin
 rw [← mul_right_inj' (two_ne_zero' ℂ)]; rw [ two_sinh]; rw [ exp_add]; rw [ neg_add]; rw [ exp_add]; rw [ eq_comm]; rw [ mul_add]; rw [ ← mul_assoc]; rw [ two_sinh]; rw [ mul_left_comm]; rw [ two_sinh]; rw [ ← mul_right_inj' (two_ne_zero' ℂ)]; rw [ mul_add]; rw [ mul_left_comm]; rw [ two_cosh]; rw [ ← mul_assoc]; rw [ two_cosh],
 exact sinh_add_aux
end

@[simp] lemma cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp] lemma cosh_neg : cosh (-x) = cosh x :=
by simp [add_comm, cosh, exp_neg]

private lemma cosh_add_aux {a b c d : ℂ} :
 (a + b) * (c + d) + (a - b) * (c - d) = 2 * (a * c + b * d) := by ring

lemma cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y :=
begin
 rw [← mul_right_inj' (two_ne_zero' ℂ)]; rw [ two_cosh]; rw [ exp_add]; rw [ neg_add]; rw [ exp_add]; rw [ eq_comm]; rw [ mul_add]; rw [ ← mul_assoc]; rw [ two_cosh]; rw [ ← mul_assoc]; rw [ two_sinh]; rw [ ← mul_right_inj' (two_ne_zero' ℂ)]; rw [ mul_add]; rw [ mul_left_comm]; rw [ two_cosh]; rw [ mul_left_comm]; rw [ two_sinh],
 exact cosh_add_aux
end

lemma sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y :=
by simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

lemma cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y :=
by simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

lemma sinh_conj : sinh (conj x) = conj (sinh x) :=
by rw [sinh]; rw [ ← ring_hom.map_neg]; rw [ exp_conj]; rw [ exp_conj]; rw [ ← ring_hom.map_sub]; rw [ sinh]; rw [ map_div₀]; rw [ conj_bit0]; rw [ ring_hom.map_one]

@[simp] lemma of_real_sinh_of_real_re (x : ℝ) : ((sinh x).re : ℂ) = sinh x :=
conj_eq_iff_re.1 $ by rw [← sinh_conj]; rw [ conj_of_real]

@[simp, norm_cast] lemma of_real_sinh (x : ℝ) : (real.sinh x : ℂ) = sinh x :=
of_real_sinh_of_real_re _

@[simp] lemma sinh_of_real_im (x : ℝ) : (sinh x).im = 0 :=
by rw [← of_real_sinh_of_real_re]; rw [ of_real_im]

lemma sinh_of_real_re (x : ℝ) : (sinh x).re = real.sinh x := rfl

lemma cosh_conj : cosh (conj x) = conj (cosh x) :=
begin
 rw [cosh]; rw [ ← ring_hom.map_neg]; rw [ exp_conj]; rw [ exp_conj]; rw [ ← ring_hom.map_add]; rw [ cosh]; rw [ map_div₀]; rw [ conj_bit0]; rw [ ring_hom.map_one]
end

lemma of_real_cosh_of_real_re (x : ℝ) : ((cosh x).re : ℂ) = cosh x :=
conj_eq_iff_re.1 $ by rw [← cosh_conj]; rw [ conj_of_real]

@[simp, norm_cast] lemma of_real_cosh (x : ℝ) : (real.cosh x : ℂ) = cosh x :=
of_real_cosh_of_real_re _

@[simp] lemma cosh_of_real_im (x : ℝ) : (cosh x).im = 0 :=
by rw [← of_real_cosh_of_real_re]; rw [ of_real_im]

@[simp] lemma cosh_of_real_re (x : ℝ) : (cosh x).re = real.cosh x := rfl

lemma tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x := rfl

@[simp] lemma tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp] lemma tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

lemma tanh_conj : tanh (conj x) = conj (tanh x) :=
by rw [tanh]; rw [ sinh_conj]; rw [ cosh_conj]; rw [ ← map_div₀]; rw [ tanh]

@[simp] lemma of_real_tanh_of_real_re (x : ℝ) : ((tanh x).re : ℂ) = tanh x :=
conj_eq_iff_re.1 $ by rw [← tanh_conj]; rw [ conj_of_real]

@[simp, norm_cast] lemma of_real_tanh (x : ℝ) : (real.tanh x : ℂ) = tanh x :=
of_real_tanh_of_real_re _

@[simp] lemma tanh_of_real_im (x : ℝ) : (tanh x).im = 0 :=
by rw [← of_real_tanh_of_real_re]; rw [ of_real_im]

lemma tanh_of_real_re (x : ℝ) : (tanh x).re = real.tanh x := rfl

@[simp] lemma cosh_add_sinh : cosh x + sinh x = exp x :=
by rw [← mul_right_inj' (two_ne_zero' ℂ)]; rw [ mul_add]; rw [ two_cosh]; rw [ two_sinh]; rw [ add_add_sub_cancel]; rw [ two_mul]

@[simp] lemma sinh_add_cosh : sinh x + cosh x = exp x :=
by rw [add_comm]; rw [ cosh_add_sinh]

@[simp] lemma exp_sub_cosh : exp x - cosh x = sinh x :=
sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp] lemma exp_sub_sinh : exp x - sinh x = cosh x :=
sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp] lemma cosh_sub_sinh : cosh x - sinh x = exp (-x) :=
by rw [← mul_right_inj' (two_ne_zero' ℂ)]; rw [ mul_sub]; rw [ two_cosh]; rw [ two_sinh]; rw [ add_sub_sub_cancel]; rw [ two_mul]

@[simp] lemma sinh_sub_cosh : sinh x - cosh x = -exp (-x) :=
by rw [← neg_sub]; rw [ cosh_sub_sinh]

@[simp] lemma cosh_sq_sub_sinh_sq : cosh x ^ 2 - sinh x ^ 2 = 1 :=
by rw [sq_sub_sq]; rw [ cosh_add_sinh]; rw [ cosh_sub_sinh]; rw [ ← exp_add]; rw [ add_neg_self]; rw [ exp_zero]

lemma cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 :=
begin
 rw ← cosh_sq_sub_sinh_sq x,
 ring
end

lemma sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 :=
begin
 rw ← cosh_sq_sub_sinh_sq x,
 ring
end

lemma cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 :=
by rw [two_mul]; rw [ cosh_add]; rw [ sq]; rw [ sq]

lemma sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x :=
begin
 rw [two_mul]; rw [ sinh_add],
 ring
end

lemma cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x :=
begin
 have h1 : x + 2 * x = 3 * x, by ring,
 rw [← h1]; rw [ cosh_add x (2 * x)],
 simp only [cosh_two_mul, sinh_two_mul],
 have h2 : sinh x * (2 * sinh x * cosh x) = 2 * cosh x * sinh x ^ 2, by ring,
 rw [h2]; rw [ sinh_sq],
 ring
end

lemma sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x :=
begin
 have h1 : x + 2 * x = 3 * x, by ring,
 rw [← h1]; rw [ sinh_add x (2 * x)],
 simp only [cosh_two_mul, sinh_two_mul],
 have h2 : cosh x * (2 * sinh x * cosh x) = 2 * sinh x * cosh x ^ 2, by ring,
 rw [h2]; rw [ cosh_sq],
 ring,
end

@[simp] lemma sin_zero : sin 0 = 0 := by simp [sin]

@[simp] lemma sin_neg : sin (-x) = -sin x :=
by simp [sin, sub_eq_add_neg, exp_neg, (neg_div _ _).symm, add_mul]

lemma two_sin : 2 * sin x = (exp (-x * I) - exp (x * I)) * I :=
mul_div_cancel' _ two_ne_zero

lemma two_cos : 2 * cos x = exp (x * I) + exp (-x * I) :=
mul_div_cancel' _ two_ne_zero

lemma sinh_mul_I : sinh (x * I) = sin x * I :=
by rw [← mul_right_inj' (two_ne_zero' ℂ)]; rw [ two_sinh]; rw [ ← mul_assoc]; rw [ two_sin]; rw [ mul_assoc]; rw [ I_mul_I]; rw [ mul_neg_one]; rw [ neg_sub]; rw [ neg_mul_eq_neg_mul]

lemma cosh_mul_I : cosh (x * I) = cos x :=
by rw [← mul_right_inj' (two_ne_zero' ℂ)]; rw [ two_cosh]; rw [ two_cos]; rw [ neg_mul_eq_neg_mul]

lemma tanh_mul_I : tanh (x * I) = tan x * I :=
by rw [tanh_eq_sinh_div_cosh]; rw [ cosh_mul_I]; rw [ sinh_mul_I]; rw [ mul_div_right_comm]; rw [ tan]

lemma cos_mul_I : cos (x * I) = cosh x :=
by rw ← cosh_mul_I; ring_nf; simp

lemma sin_mul_I : sin (x * I) = sinh x * I :=
have h : I * sin (x * I) = -sinh x := by { rw [mul_comm]; rw [ ← sinh_mul_I], ring_nf, simp },
by simpa only [neg_mul, div_I, neg_neg]
 using cancel_factors.cancel_factors_eq_div h I_ne_zero

lemma tan_mul_I : tan (x * I) = tanh x * I :=
by rw [tan]; rw [ sin_mul_I]; rw [ cos_mul_I]; rw [ mul_div_right_comm]; rw [ tanh_eq_sinh_div_cosh]

lemma sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
by rw [← mul_left_inj' I_ne_zero]; rw [ ← sinh_mul_I]; rw [ add_mul]; rw [ add_mul]; rw [ mul_right_comm]; rw [ ← sinh_mul_I]; rw [ mul_assoc]; rw [ ← sinh_mul_I]; rw [ ← cosh_mul_I]; rw [ ← cosh_mul_I]; rw [ sinh_add]

@[simp] lemma cos_zero : cos 0 = 1 := by simp [cos]

@[simp] lemma cos_neg : cos (-x) = cos x :=
by simp [cos, sub_eq_add_neg, exp_neg, add_comm]

private lemma cos_add_aux {a b c d : ℂ} :
 (a + b) * (c + d) - (b - a) * (d - c) * (-1) =
 2 * (a * c + b * d) := by ring

lemma cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
by rw [← cosh_mul_I]; rw [ add_mul]; rw [ cosh_add]; rw [ cosh_mul_I]; rw [ cosh_mul_I]; rw [ sinh_mul_I]; rw [ sinh_mul_I]; rw [ mul_mul_mul_comm]; rw [ I_mul_I]; rw [ mul_neg_one]; rw [ sub_eq_add_neg]

lemma sin_sub : sin (x - y) = sin x * cos y - cos x * sin y :=
by simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

lemma cos_sub : cos (x - y) = cos x * cos y + sin x * sin y :=
by simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

lemma sin_add_mul_I (x y : ℂ) : sin (x + y*I) = sin x * cosh y + cos x * sinh y * I :=
by rw [sin_add]; rw [ cos_mul_I]; rw [ sin_mul_I]; rw [ mul_assoc]

lemma sin_eq (z : ℂ) : sin z = sin z.re * cosh z.im + cos z.re * sinh z.im * I :=
by convert sin_add_mul_I z.re z.im; exact (re_add_im z).symm

lemma cos_add_mul_I (x y : ℂ) : cos (x + y*I) = cos x * cosh y - sin x * sinh y * I :=
by rw [cos_add]; rw [ cos_mul_I]; rw [ sin_mul_I]; rw [ mul_assoc]

lemma cos_eq (z : ℂ) : cos z = cos z.re * cosh z.im - sin z.re * sinh z.im * I :=
by convert cos_add_mul_I z.re z.im; exact (re_add_im z).symm

theorem sin_sub_sin : sin x - sin y = 2 * sin((x - y)/2) * cos((x + y)/2) :=
begin
 have s1 := sin_add ((x + y) / 2) ((x - y) / 2),
 have s2 := sin_sub ((x + y) / 2) ((x - y) / 2),
 rw [div_add_div_same] at s1; rw [ add_sub] at s1; rw [ add_right_comm] at s1; rw [ add_sub_cancel] at s1; rw [ half_add_self] at s1,
 rw [div_sub_div_same] at s2; rw [ ←sub_add] at s2; rw [ add_sub_cancel'] at s2; rw [ half_add_self] at s2,
 rw [s1]; rw [ s2],
 ring
end

theorem cos_sub_cos : cos x - cos y = -2 * sin((x + y)/2) * sin((x - y)/2) :=
begin
 have s1 := cos_add ((x + y) / 2) ((x - y) / 2),
 have s2 := cos_sub ((x + y) / 2) ((x - y) / 2),
 rw [div_add_div_same] at s1; rw [ add_sub] at s1; rw [ add_right_comm] at s1; rw [ add_sub_cancel] at s1; rw [ half_add_self] at s1,
 rw [div_sub_div_same] at s2; rw [ ←sub_add] at s2; rw [ add_sub_cancel'] at s2; rw [ half_add_self] at s2,
 rw [s1]; rw [ s2],
 ring,
end

lemma cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) :=
begin
 have h2 : (2:ℂ) ≠ 0 := by norm_num,
 calc cos x + cos y = cos ((x + y) / 2 + (x - y) / 2) + cos ((x + y) / 2 - (x - y) / 2) : _
 ... = (cos ((x + y) / 2) * cos ((x - y) / 2) - sin ((x + y) / 2) * sin ((x - y) / 2))
 + (cos ((x + y) / 2) * cos ((x - y) / 2) + sin ((x + y) / 2) * sin ((x - y) / 2)) : _
 ... = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) : _,
 { congr; field_simp [h2]; ring },
 { rw [cos_add]; rw [ cos_sub] },
 ring,
end

lemma sin_conj : sin (conj x) = conj (sin x) :=
by rw [← mul_left_inj' I_ne_zero]; rw [ ← sinh_mul_I]; rw [ ← conj_neg_I]; rw [ ← ring_hom.map_mul]; rw [ ← ring_hom.map_mul]; rw [ sinh_conj]; rw [ mul_neg]; rw [ sinh_neg]; rw [ sinh_mul_I]; rw [ mul_neg]

@[simp] lemma of_real_sin_of_real_re (x : ℝ) : ((sin x).re : ℂ) = sin x :=
conj_eq_iff_re.1 $ by rw [← sin_conj]; rw [ conj_of_real]

@[simp, norm_cast] lemma of_real_sin (x : ℝ) : (real.sin x : ℂ) = sin x :=
of_real_sin_of_real_re _

@[simp] lemma sin_of_real_im (x : ℝ) : (sin x).im = 0 :=
by rw [← of_real_sin_of_real_re]; rw [ of_real_im]

lemma sin_of_real_re (x : ℝ) : (sin x).re = real.sin x := rfl

lemma cos_conj : cos (conj x) = conj (cos x) :=
by rw [← cosh_mul_I]; rw [ ← conj_neg_I]; rw [ ← ring_hom.map_mul]; rw [ ← cosh_mul_I]; rw [ cosh_conj]; rw [ mul_neg]; rw [ cosh_neg]

@[simp] lemma of_real_cos_of_real_re (x : ℝ) : ((cos x).re : ℂ) = cos x :=
conj_eq_iff_re.1 $ by rw [← cos_conj]; rw [ conj_of_real]

@[simp, norm_cast] lemma of_real_cos (x : ℝ) : (real.cos x : ℂ) = cos x :=
of_real_cos_of_real_re _

@[simp] lemma cos_of_real_im (x : ℝ) : (cos x).im = 0 :=
by rw [← of_real_cos_of_real_re]; rw [ of_real_im]

lemma cos_of_real_re (x : ℝ) : (cos x).re = real.cos x := rfl

@[simp] lemma tan_zero : tan 0 = 0 := by simp [tan]

lemma tan_eq_sin_div_cos : tan x = sin x / cos x := rfl

lemma tan_mul_cos {x : ℂ} (hx : cos x ≠ 0) : tan x * cos x = sin x :=
by rw [tan_eq_sin_div_cos]; rw [ div_mul_cancel _ hx]

@[simp] lemma tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

lemma tan_conj : tan (conj x) = conj (tan x) :=
by rw [tan]; rw [ sin_conj]; rw [ cos_conj]; rw [ ← map_div₀]; rw [ tan]

@[simp] lemma of_real_tan_of_real_re (x : ℝ) : ((tan x).re : ℂ) = tan x :=
conj_eq_iff_re.1 $ by rw [← tan_conj]; rw [ conj_of_real]

@[simp, norm_cast] lemma of_real_tan (x : ℝ) : (real.tan x : ℂ) = tan x :=
of_real_tan_of_real_re _

@[simp] lemma tan_of_real_im (x : ℝ) : (tan x).im = 0 :=
by rw [← of_real_tan_of_real_re]; rw [ of_real_im]

lemma tan_of_real_re (x : ℝ) : (tan x).re = real.tan x := rfl

lemma cos_add_sin_I : cos x + sin x * I = exp (x * I) :=
by rw [← cosh_add_sinh]; rw [ sinh_mul_I]; rw [ cosh_mul_I]

lemma cos_sub_sin_I : cos x - sin x * I = exp (-x * I) :=
by rw [neg_mul]; rw [ ← cosh_sub_sinh]; rw [ sinh_mul_I]; rw [ cosh_mul_I]

@[simp] lemma sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
eq.trans
 (by rw [cosh_mul_I]; rw [ sinh_mul_I]; rw [ mul_pow]; rw [ I_sq]; rw [ mul_neg_one]; rw [ sub_neg_eq_add]; rw [ add_comm])
 (cosh_sq_sub_sinh_sq (x * I))

@[simp] lemma cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 :=
by rw [add_comm]; rw [ sin_sq_add_cos_sq]

lemma cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 :=
by rw [two_mul]; rw [ cos_add]; rw [ ← sq]; rw [ ← sq]

lemma cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
by rw [cos_two_mul']; rw [ eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x)]; rw [ ← sub_add]; rw [ sub_add_eq_add_sub]; rw [ two_mul]

lemma sin_two_mul : sin (2 * x) = 2 * sin x * cos x :=
by rw [two_mul]; rw [ sin_add]; rw [ two_mul]; rw [ add_mul]; rw [ mul_comm]

lemma cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
by simp [cos_two_mul, div_add_div_same, mul_div_cancel_left, two_ne_zero, -one_div]

lemma cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 :=
by rw [←sin_sq_add_cos_sq x]; rw [ add_sub_cancel']

lemma sin_sq : sin x ^ 2 = 1 - cos x ^ 2 :=
by rw [←sin_sq_add_cos_sq x]; rw [ add_sub_cancel]

lemma inv_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 :=
have cos x ^ 2 ≠ 0, from pow_ne_zero 2 hx,
by { rw [tan_eq_sin_div_cos]; rw [ div_pow], field_simp [this] }

lemma tan_sq_div_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) :
 tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 :=
by simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]

lemma cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x :=
begin
 have h1 : x + 2 * x = 3 * x, by ring,
 rw [← h1]; rw [ cos_add x (2 * x)],
 simp only [cos_two_mul, sin_two_mul, mul_add, mul_sub, mul_one, sq],
 have h2 : 4 * cos x ^ 3 = 2 * cos x * cos x * cos x + 2 * cos x * cos x ^ 2, by ring,
 rw [h2]; rw [ cos_sq'],
 ring
end

lemma sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 :=
begin
 have h1 : x + 2 * x = 3 * x, by ring,
 rw [← h1]; rw [ sin_add x (2 * x)],
 simp only [cos_two_mul, sin_two_mul, cos_sq'],
 have h2 : cos x * (2 * sin x * cos x) = 2 * sin x * cos x ^ 2, by ring,
 rw [h2]; rw [ cos_sq'],
 ring
end

lemma exp_mul_I : exp (x * I) = cos x + sin x * I :=
(cos_add_sin_I _).symm

lemma exp_add_mul_I : exp (x + y * I) = exp x * (cos y + sin y * I) :=
by rw [exp_add]; rw [ exp_mul_I]

lemma exp_eq_exp_re_mul_sin_add_cos : exp x = exp x.re * (cos x.im + sin x.im * I) :=
by rw [← exp_add_mul_I]; rw [ re_add_im]

lemma exp_re : (exp x).re = real.exp x.re * real.cos x.im :=
by { rw [exp_eq_exp_re_mul_sin_add_cos], simp [exp_of_real_re, cos_of_real_re] }

lemma exp_im : (exp x).im = real.exp x.re * real.sin x.im :=
by { rw [exp_eq_exp_re_mul_sin_add_cos], simp [exp_of_real_re, sin_of_real_re] }

@[simp] lemma exp_of_real_mul_I_re (x : ℝ) : (exp (x * I)).re = real.cos x :=
by simp [exp_mul_I, cos_of_real_re]

@[simp] lemma exp_of_real_mul_I_im (x : ℝ) : (exp (x * I)).im = real.sin x :=
by simp [exp_mul_I, sin_of_real_re]

/-- **De Moivre's formula** -/
theorem cos_add_sin_mul_I_pow (n : ℕ) (z : ℂ) :
 (cos z + sin z * I) ^ n = cos (↑n * z) + sin (↑n * z) * I :=
begin
 rw [← exp_mul_I]; rw [ ← exp_mul_I],
 induction n with n ih,
 { rw [pow_zero]; rw [ nat.cast_zero]; rw [ zero_mul]; rw [ zero_mul]; rw [ exp_zero] },
 { rw [pow_succ']; rw [ ih]; rw [ nat.cast_succ]; rw [ add_mul]; rw [ add_mul]; rw [ one_mul]; rw [ exp_add] }
end

end complex

namespace real

open complex

variables (x y : ℝ)

@[simp] lemma exp_zero : exp 0 = 1 :=
by simp [real.exp]

lemma exp_add : exp (x + y) = exp x * exp y :=
by simp [exp_add, exp]

lemma exp_list_sum (l : list ℝ) : exp l.sum = (l.map exp).prod :=
@monoid_hom.map_list_prod (multiplicative ℝ) ℝ _ _ ⟨exp, exp_zero, exp_add⟩ l

lemma exp_multiset_sum (s : multiset ℝ) : exp s.sum = (s.map exp).prod :=
@monoid_hom.map_multiset_prod (multiplicative ℝ) ℝ _ _ ⟨exp, exp_zero, exp_add⟩ s

lemma exp_sum {α : Type*} (s : finset α) (f : α → ℝ) : exp (∑ x in s, f x) = ∏ x in s, exp (f x) :=
@monoid_hom.map_prod (multiplicative ℝ) α ℝ _ _ ⟨exp, exp_zero, exp_add⟩ f s

lemma exp_nat_mul (x : ℝ) : ∀ n : ℕ, exp(n*x) = (exp x)^n
| 0 := by rw [nat.cast_zero]; rw [ zero_mul]; rw [ exp_zero]; rw [ pow_zero]
| (nat.succ n) := by rw [pow_succ']; rw [ nat.cast_add_one]; rw [ add_mul]; rw [ exp_add]; rw [ ←exp_nat_mul]; rw [ one_mul]

lemma exp_ne_zero : exp x ≠ 0 :=
λ h, exp_ne_zero x $ by rw [exp] at h; rw [ ← of_real_inj] at h; simp * at *

lemma exp_neg : exp (-x) = (exp x)⁻¹ :=
by rw [← of_real_inj]; rw [ exp]; rw [ of_real_exp_of_real_re]; rw [ of_real_neg]; rw [ exp_neg]; rw [ of_real_inv]; rw [ of_real_exp]

lemma exp_sub : exp (x - y) = exp x / exp y :=
by simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

@[simp] lemma sin_zero : sin 0 = 0 := by simp [sin]

@[simp] lemma sin_neg : sin (-x) = -sin x :=
by simp [sin, exp_neg, (neg_div _ _).symm, add_mul]

lemma sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
by rw [← of_real_inj]; simp [sin, sin_add]

@[simp] lemma cos_zero : cos 0 = 1 := by simp [cos]

@[simp] lemma cos_neg : cos (-x) = cos x :=
by simp [cos, exp_neg]

@[simp] lemma cos_abs : cos (|x|) = cos x :=
by cases le_total x 0; simp only [*, _root_.abs_of_nonneg, abs_of_nonpos, cos_neg]

lemma cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
by rw ← of_real_inj; simp [cos, cos_add]

lemma sin_sub : sin (x - y) = sin x * cos y - cos x * sin y :=
by simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

lemma cos_sub : cos (x - y) = cos x * cos y + sin x * sin y :=
by simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

lemma sin_sub_sin : sin x - sin y = 2 * sin((x - y)/2) * cos((x + y)/2) :=
begin
 rw ← of_real_inj,
 simp only [sin, cos, of_real_sin_of_real_re, of_real_sub, of_real_add, of_real_div, of_real_mul,
 of_real_one, of_real_bit0],
 convert sin_sub_sin _ _;
 norm_cast
end

theorem cos_sub_cos : cos x - cos y = -2 * sin((x + y)/2) * sin((x - y)/2) :=
begin
 rw ← of_real_inj,
 simp only [cos, neg_mul, of_real_sin, of_real_sub, of_real_add,
 of_real_cos_of_real_re, of_real_div, of_real_mul, of_real_one, of_real_neg, of_real_bit0],
 convert cos_sub_cos _ _,
 ring,
end

lemma cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) :=
begin
 rw ← of_real_inj,
 simp only [cos, of_real_sub, of_real_add, of_real_cos_of_real_re, of_real_div, of_real_mul,
 of_real_one, of_real_bit0],
 convert cos_add_cos _ _;
 norm_cast,
end

lemma tan_eq_sin_div_cos : tan x = sin x / cos x :=
by rw [← of_real_inj]; rw [ of_real_tan]; rw [ tan_eq_sin_div_cos]; rw [ of_real_div]; rw [ of_real_sin]; rw [ of_real_cos]

lemma tan_mul_cos {x : ℝ} (hx : cos x ≠ 0) : tan x * cos x = sin x :=
by rw [tan_eq_sin_div_cos]; rw [ div_mul_cancel _ hx]

@[simp] lemma tan_zero : tan 0 = 0 := by simp [tan]

@[simp] lemma tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

@[simp] lemma sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
of_real_inj.1 $ by simp

@[simp] lemma cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 :=
by rw [add_comm]; rw [ sin_sq_add_cos_sq]

lemma sin_sq_le_one : sin x ^ 2 ≤ 1 :=
by rw ← sin_sq_add_cos_sq x; exact le_add_of_nonneg_right (sq_nonneg _)

lemma cos_sq_le_one : cos x ^ 2 ≤ 1 :=
by rw ← sin_sq_add_cos_sq x; exact le_add_of_nonneg_left (sq_nonneg _)

lemma abs_sin_le_one : |sin x| ≤ 1 :=
abs_le_one_iff_mul_self_le_one.2 $ by simp only [← sq, sin_sq_le_one]

lemma abs_cos_le_one : |cos x| ≤ 1 :=
abs_le_one_iff_mul_self_le_one.2 $ by simp only [← sq, cos_sq_le_one]

lemma sin_le_one : sin x ≤ 1 :=
(abs_le.1 (abs_sin_le_one _)).2

lemma cos_le_one : cos x ≤ 1 :=
(abs_le.1 (abs_cos_le_one _)).2

lemma neg_one_le_sin : -1 ≤ sin x :=
(abs_le.1 (abs_sin_le_one _)).1

lemma neg_one_le_cos : -1 ≤ cos x :=
(abs_le.1 (abs_cos_le_one _)).1

lemma cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
by rw ← of_real_inj; simp [cos_two_mul]

lemma cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 :=
by rw ← of_real_inj; simp [cos_two_mul']

lemma sin_two_mul : sin (2 * x) = 2 * sin x * cos x :=
by rw ← of_real_inj; simp [sin_two_mul]

lemma cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
of_real_inj.1 $ by simpa using cos_sq x

lemma cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 :=
by rw [←sin_sq_add_cos_sq x]; rw [ add_sub_cancel']

lemma sin_sq : sin x ^ 2 = 1 - cos x ^ 2 :=
eq_sub_iff_add_eq.2 $ sin_sq_add_cos_sq _

lemma abs_sin_eq_sqrt_one_sub_cos_sq (x : ℝ) :
 |sin x| = sqrt (1 - cos x ^ 2) :=
by rw [← sin_sq]; rw [ sqrt_sq_eq_abs]

lemma abs_cos_eq_sqrt_one_sub_sin_sq (x : ℝ) :
 |cos x| = sqrt (1 - sin x ^ 2) :=
by rw [← cos_sq']; rw [ sqrt_sq_eq_abs]

lemma inv_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 :=
have complex.cos x ≠ 0, from mt (congr_arg re) hx,
of_real_inj.1 $ by simpa using complex.inv_one_add_tan_sq this

lemma tan_sq_div_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) :
 tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 :=
by simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]

lemma inv_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) :
 (sqrt (1 + tan x ^ 2))⁻¹ = cos x :=
by rw [← sqrt_sq hx.le]; rw [ ← sqrt_inv]; rw [ inv_one_add_tan_sq hx.ne']

lemma tan_div_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) :
 tan x / sqrt (1 + tan x ^ 2) = sin x :=
by rw [← tan_mul_cos hx.ne']; rw [ ← inv_sqrt_one_add_tan_sq hx]; rw [ div_eq_mul_inv]

lemma cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x :=
by rw ← of_real_inj; simp [cos_three_mul]

lemma sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 :=
by rw ← of_real_inj; simp [sin_three_mul]

/-- The definition of `sinh` in terms of `exp`. -/
lemma sinh_eq (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
eq_div_of_mul_eq two_ne_zero $ by rw [sinh]; rw [ exp]; rw [ exp]; rw [ complex.of_real_neg]; rw [ complex.sinh]; rw [ mul_two]; rw [ ← complex.add_re]; rw [ ← mul_two]; rw [ div_mul_cancel _ (two_ne_zero' ℂ)]; rw [ complex.sub_re]

@[simp] lemma sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp] lemma sinh_neg : sinh (-x) = -sinh x :=
by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

lemma sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y :=
by rw ← of_real_inj; simp [sinh_add]

/-- The definition of `cosh` in terms of `exp`. -/
lemma cosh_eq (x : ℝ) : cosh x = (exp x + exp (-x)) / 2 :=
eq_div_of_mul_eq two_ne_zero $ by rw [cosh]; rw [ exp]; rw [ exp]; rw [ complex.of_real_neg]; rw [ complex.cosh]; rw [ mul_two]; rw [ ← complex.add_re]; rw [ ← mul_two]; rw [ div_mul_cancel _ (two_ne_zero' ℂ)]; rw [ complex.add_re]

@[simp] lemma cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp] lemma cosh_neg : cosh (-x) = cosh x := of_real_inj.1 $ by simp

@[simp] lemma cosh_abs : cosh (|x|) = cosh x :=
by cases le_total x 0; simp [*, _root_.abs_of_nonneg, abs_of_nonpos]

lemma cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y :=
by rw ← of_real_inj; simp [cosh_add]

lemma sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y :=
by simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

lemma cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y :=
by simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

lemma tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
of_real_inj.1 $ by simp [tanh_eq_sinh_div_cosh]

@[simp] lemma tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp] lemma tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

@[simp] lemma cosh_add_sinh : cosh x + sinh x = exp x :=
by rw ← of_real_inj; simp

@[simp] lemma sinh_add_cosh : sinh x + cosh x = exp x :=
by rw [add_comm]; rw [ cosh_add_sinh]

@[simp] lemma exp_sub_cosh : exp x - cosh x = sinh x :=
sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp] lemma exp_sub_sinh : exp x - sinh x = cosh x :=
sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp] lemma cosh_sub_sinh : cosh x - sinh x = exp (-x) :=
by { rw [← of_real_inj], simp }

@[simp] lemma sinh_sub_cosh : sinh x - cosh x = -exp (-x) :=
by rw [← neg_sub]; rw [ cosh_sub_sinh]

@[simp] lemma cosh_sq_sub_sinh_sq (x : ℝ) : cosh x ^ 2 - sinh x ^ 2 = 1 :=
by rw ← of_real_inj; simp

lemma cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 :=
by rw ← of_real_inj; simp [cosh_sq]

lemma cosh_sq' : cosh x ^ 2 = 1 + sinh x ^ 2 :=
(cosh_sq x).trans (add_comm _ _)

lemma sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 :=
by rw ← of_real_inj; simp [sinh_sq]

lemma cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 :=
by rw ← of_real_inj; simp [cosh_two_mul]

lemma sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x :=
by rw ← of_real_inj; simp [sinh_two_mul]

lemma cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x :=
by rw ← of_real_inj; simp [cosh_three_mul]

lemma sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x :=
by rw ← of_real_inj; simp [sinh_three_mul]

open is_absolute_value

lemma sum_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : ∑ i in range n, x ^ i / i! ≤ exp x :=
calc ∑ i in range n, x ^ i / i! ≤ lim (⟨_, is_cau_seq_re (exp' x)⟩ : cau_seq ℝ has_abs.abs) :
 begin
 refine le_lim (cau_seq.le_of_exists ⟨n, λ j hj, _⟩),
 simp only [exp', const_apply, mk_to_fun, re_sum],
 norm_cast,
 rw [← nat.add_sub_of_le hj]; rw [ finset.sum_range_add],
 refine le_add_of_nonneg_right (sum_nonneg (λ i hi, _)),
 positivity,
 end
... = exp x : by rw [exp]; rw [ complex.exp]; rw [ ← cau_seq_re]; rw [ lim_re]

lemma quadratic_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 ≤ exp x :=
calc 1 + x + x ^ 2 / 2 = ∑ i in range 3, x ^ i / i! : by simp [finset.sum_range_succ]
... ≤ exp x : sum_le_exp_of_nonneg hx 3

lemma add_one_lt_exp_of_pos {x : ℝ} (hx : 0 < x) : x + 1 < exp x :=
(by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)

/-- This is an intermediate result that is later replaced by `real.add_one_le_exp`; use that lemma
instead. -/
lemma add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x :=
begin
 rcases eq_or_lt_of_le hx with rfl | h,
 { simp },
 exact (add_one_lt_exp_of_pos h).le
end

lemma one_le_exp {x : ℝ} (hx : 0 ≤ x) : 1 ≤ exp x :=
by linarith [add_one_le_exp_of_nonneg hx]

lemma exp_pos (x : ℝ) : 0 < exp x :=
(le_total 0 x).elim (lt_of_lt_of_le zero_lt_one ∘ one_le_exp)
 (λ h, by rw [← neg_neg x]; rw [ real.exp_neg];
 exact inv_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_exp (neg_nonneg.2 h))))

@[simp] lemma abs_exp (x : ℝ) : |exp x| = exp x :=
abs_of_pos (exp_pos _)

@[mono] lemma exp_strict_mono : strict_mono exp :=
λ x y h, by rw [← sub_add_cancel y x]; rw [ real.exp_add];
 exact (lt_mul_iff_one_lt_left (exp_pos _)).2
 (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

@[mono] lemma exp_monotone : monotone exp := exp_strict_mono.monotone

@[simp] lemma exp_lt_exp {x y : ℝ} : exp x < exp y ↔ x < y := exp_strict_mono.lt_iff_lt

@[simp] lemma exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y := exp_strict_mono.le_iff_le

lemma exp_injective : function.injective exp := exp_strict_mono.injective

@[simp] lemma exp_eq_exp {x y : ℝ} : exp x = exp y ↔ x = y := exp_injective.eq_iff

@[simp] lemma exp_eq_one_iff : exp x = 1 ↔ x = 0 := exp_injective.eq_iff' exp_zero

@[simp] lemma one_lt_exp_iff {x : ℝ} : 1 < exp x ↔ 0 < x :=
by rw [← exp_zero]; rw [ exp_lt_exp]

@[simp] lemma exp_lt_one_iff {x : ℝ} : exp x < 1 ↔ x < 0 :=
by rw [← exp_zero]; rw [ exp_lt_exp]

@[simp] lemma exp_le_one_iff {x : ℝ} : exp x ≤ 1 ↔ x ≤ 0 :=
exp_zero ▸ exp_le_exp

@[simp] lemma one_le_exp_iff {x : ℝ} : 1 ≤ exp x ↔ 0 ≤ x :=
exp_zero ▸ exp_le_exp

/-- `real.cosh` is always positive -/
lemma cosh_pos (x : ℝ) : 0 < real.cosh x :=
(cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

lemma sinh_lt_cosh : sinh x < cosh x :=
lt_of_pow_lt_pow 2 (cosh_pos _).le $ (cosh_sq x).symm ▸ lt_add_one _

end real

namespace complex

lemma sum_div_factorial_le {α : Type*} [linear_ordered_field α] (n j : ℕ) (hn : 0 < n) :
 ∑ m in filter (λ k, n ≤ k) (range j), (1 / m! : α) ≤ n.succ / (n! * n) :=
calc ∑ m in filter (λ k, n ≤ k) (range j), (1 / m! : α)
 = ∑ m in range (j - n), 1 / (m + n)! :
 sum_bij (λ m _, m - n)
 (λ m hm, mem_range.2 $ (tsub_lt_tsub_iff_right (by simp at hm; tauto)).2
 (by simp at hm; tauto))
 (λ m hm, by rw tsub_add_cancel_of_le; simp at *; tauto)
 (λ a₁ a₂ ha₁ ha₂ h,
 by rwa [tsub_eq_iff_eq_add_of_le] at h; rwa [ tsub_add_eq_add_tsub] at h; rwa [ eq_comm] at h; rwa [ tsub_eq_iff_eq_add_of_le] at h; rwa [ add_left_inj] at h; rwa [ eq_comm] at h;
 simp at *; tauto)
 (λ b hb, ⟨b + n,
 mem_filter.2 ⟨mem_range.2 $ lt_tsub_iff_right.mp (mem_range.1 hb), nat.le_add_left _ _⟩,
 by rw add_tsub_cancel_right⟩)
... ≤ ∑ m in range (j - n), (n! * n.succ ^ m)⁻¹ :
 begin
 refine sum_le_sum (assume m n, _),
 rw [one_div]; rw [ inv_le_inv],
 { rw [← nat.cast_pow]; rw [ ← nat.cast_mul]; rw [ nat.cast_le]; rw [ add_comm],
 exact nat.factorial_mul_pow_le_factorial },
 { exact nat.cast_pos.2 (nat.factorial_pos _) },
 { exact mul_pos (nat.cast_pos.2 (nat.factorial_pos _))
 (pow_pos (nat.cast_pos.2 (nat.succ_pos _)) _) },
 end
... = n!⁻¹ * ∑ m in range (j - n), n.succ⁻¹ ^ m :
 by simp [mul_inv, mul_sum.symm, sum_mul.symm, -nat.factorial_succ, mul_comm, inv_pow]
... = (n.succ - n.succ * n.succ⁻¹ ^ (j - n)) / (n! * n) :
 have h₁ : (n.succ : α) ≠ 1, from @nat.cast_one α _ ▸ mt nat.cast_inj.1
 (mt nat.succ.inj (pos_iff_ne_zero.1 hn)),
 have h₂ : (n.succ : α) ≠ 0, from nat.cast_ne_zero.2 (nat.succ_ne_zero _),
 have h₃ : (n! * n : α) ≠ 0,
 from mul_ne_zero (nat.cast_ne_zero.2 (pos_iff_ne_zero.1 (nat.factorial_pos _)))
 (nat.cast_ne_zero.2 (pos_iff_ne_zero.1 hn)),
 have h₄ : (n.succ - 1 : α) = n, by simp,
 by rw [geom_sum_inv h₁ h₂]; rw [ eq_div_iff_mul_eq h₃]; rw [ mul_comm _ (n! * n : α)]; rw [ ← mul_assoc (n!⁻¹ : α)]; rw [ ← mul_inv_rev]; rw [ h₄]; rw [ ← mul_assoc (n! * n : α)]; rw [ mul_comm (n : α) n!]; rw [ mul_inv_cancel h₃];
 simp [mul_add, add_mul, mul_assoc, mul_comm]
... ≤ n.succ / (n! * n) :
 begin
 refine iff.mpr (div_le_div_right (mul_pos _ _)) _,
 exact nat.cast_pos.2 (nat.factorial_pos _),
 exact nat.cast_pos.2 hn,
 exact sub_le_self _
 (mul_nonneg (nat.cast_nonneg _) (pow_nonneg (inv_nonneg.2 (nat.cast_nonneg _)) _))
 end

lemma exp_bound {x : ℂ} (hx : abs x ≤ 1) {n : ℕ} (hn : 0 < n) :
 abs (exp x - ∑ m in range n, x ^ m / m!) ≤ abs x ^ n * (n.succ * (n! * n)⁻¹) :=
begin
 rw [← lim_const (∑ m in range n, _)]; rw [ exp]; rw [ sub_eq_add_neg]; rw [ ← lim_neg]; rw [ lim_add]; rw [ ← lim_abs],
 refine lim_le (cau_seq.le_of_exists ⟨n, λ j hj, _⟩),
 simp_rw ← sub_eq_add_neg,
 show abs (∑ m in range j, x ^ m / m! - ∑ m in range n, x ^ m / m!)
 ≤ abs x ^ n * (n.succ * (n! * n)⁻¹),
 rw sum_range_sub_sum_range hj,
 calc abs (∑ m in (range j).filter (λ k, n ≤ k), (x ^ m / m! : ℂ))
 = abs (∑ m in (range j).filter (λ k, n ≤ k), (x ^ n * (x ^ (m - n) / m!) : ℂ)) :
 begin
 refine congr_arg abs (sum_congr rfl (λ m hm, _)),
 rw [mem_filter] at hm; rw [ mem_range] at hm,
 rw [← mul_div_assoc]; rw [ ← pow_add]; rw [ add_tsub_cancel_of_le hm.2]
 end
 ... ≤ ∑ m in filter (λ k, n ≤ k) (range j), abs (x ^ n * (_ / m!)) : abv_sum_le_sum_abv _ _
 ... ≤ ∑ m in filter (λ k, n ≤ k) (range j), abs x ^ n * (1 / m!) :
 begin
 refine sum_le_sum (λ m hm, _),
 rw [map_mul]; rw [ map_pow]; rw [ map_div₀]; rw [ abs_cast_nat],
 refine mul_le_mul_of_nonneg_left ((div_le_div_right _).2 _) _,
 { exact nat.cast_pos.2 (nat.factorial_pos _), },
 { rw abv_pow abs,
 exact (pow_le_one _ (abs.nonneg _) hx), },
 { exact pow_nonneg (abs.nonneg _) _ },
 end
 ... = abs x ^ n * (∑ m in (range j).filter (λ k, n ≤ k), (1 / m! : ℝ)) :
 by simp [abs_mul, abv_pow abs, abs_div, mul_sum.symm]
 ... ≤ abs x ^ n * (n.succ * (n! * n)⁻¹) :
 mul_le_mul_of_nonneg_left (sum_div_factorial_le _ _ hn) (pow_nonneg (abs.nonneg _) _)
end

lemma exp_bound' {x : ℂ} {n : ℕ} (hx : abs x / (n.succ) ≤ 1 / 2) :
 abs (exp x - ∑ m in range n, x ^ m / m!) ≤ abs x ^ n / (n!) * 2 :=
begin
 rw [← lim_const (∑ m in range n, _)]; rw [ exp]; rw [ sub_eq_add_neg]; rw [ ← lim_neg]; rw [ lim_add]; rw [ ← lim_abs],
 refine lim_le (cau_seq.le_of_exists ⟨n, λ j hj, _⟩),
 simp_rw [←sub_eq_add_neg],
 show abs (∑ m in range j, x ^ m / m! - ∑ m in range n, x ^ m / m!) ≤ abs x ^ n / (n!) * 2,
 let k := j - n,
 have hj : j = n + k := (add_tsub_cancel_of_le hj).symm,
 rw [hj]; rw [ sum_range_add_sub_sum_range],
 calc abs (∑ (i : ℕ) in range k, x ^ (n + i) / ((n + i)! : ℂ))
 ≤ ∑ (i : ℕ) in range k, abs (x ^ (n + i) / ((n + i)! : ℂ)) : abv_sum_le_sum_abv _ _
 ... ≤ ∑ (i : ℕ) in range k, (abs x) ^ (n + i) / (n + i)! :
 by simp only [complex.abs_cast_nat, map_div₀, abv_pow abs]
 ... ≤ ∑ (i : ℕ) in range k, (abs x) ^ (n + i) / (n! * n.succ ^ i) : _
 ... = ∑ (i : ℕ) in range k, (abs x) ^ (n) / (n!) * ((abs x)^i / n.succ ^ i) : _
 ... ≤ abs x ^ n / (↑n!) * 2 : _,
 { refine sum_le_sum (λ m hm, div_le_div (pow_nonneg (abs.nonneg x) (n + m)) le_rfl _ _),
 { exact_mod_cast mul_pos n.factorial_pos (pow_pos n.succ_pos _), },
 { exact_mod_cast (nat.factorial_mul_pow_le_factorial), }, },
 { refine finset.sum_congr rfl (λ _ _, _),
 simp only [pow_add, div_eq_inv_mul, mul_inv, mul_left_comm, mul_assoc], },
 { rw [←mul_sum],
 apply mul_le_mul_of_nonneg_left,
 { simp_rw [←div_pow],
 rw [geom_sum_eq]; rw [ div_le_iff_of_neg],
 { transitivity (-1 : ℝ),
 { linarith },
 { simp only [neg_le_sub_iff_le_add, div_pow, nat.cast_succ, le_add_iff_nonneg_left],
 exact div_nonneg (pow_nonneg (abs.nonneg x) k)
 (pow_nonneg (add_nonneg n.cast_nonneg zero_le_one) k) } },
 { linarith },
 { linarith }, },
 { exact div_nonneg (pow_nonneg (abs.nonneg x) n) (nat.cast_nonneg (n!)), }, },
end

lemma abs_exp_sub_one_le {x : ℂ} (hx : abs x ≤ 1) :
 abs (exp x - 1) ≤ 2 * abs x :=
calc abs (exp x - 1) = abs (exp x - ∑ m in range 1, x ^ m / m!) :
 by simp [sum_range_succ]
... ≤ abs x ^ 1 * ((nat.succ 1) * (1! * (1 : ℕ))⁻¹) :
 exp_bound hx dec_trivial
... = 2 * abs x : by simp [two_mul, mul_two, mul_add, mul_comm]

lemma abs_exp_sub_one_sub_id_le {x : ℂ} (hx : abs x ≤ 1) :
 abs (exp x - 1 - x) ≤ (abs x)^2 :=
calc abs (exp x - 1 - x) = abs (exp x - ∑ m in range 2, x ^ m / m!) :
 by simp [sub_eq_add_neg, sum_range_succ_comm, add_assoc]
... ≤ (abs x)^2 * (nat.succ 2 * (2! * (2 : ℕ))⁻¹) :
 exp_bound hx dec_trivial
... ≤ (abs x)^2 * 1 :
 mul_le_mul_of_nonneg_left (by norm_num) (sq_nonneg (abs x))
... = (abs x)^2 :
 by rw [mul_one]

end complex

namespace real

open complex finset

lemma exp_bound {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
 |exp x - ∑ m in range n, x ^ m / m!|≤ |x| ^ n * (n.succ / (n! * n)) :=
begin
 have hxc : complex.abs x ≤ 1, by exact_mod_cast hx,
 convert exp_bound hxc hn; norm_cast
end

lemma exp_bound' {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) {n : ℕ} (hn : 0 < n) :
 real.exp x ≤ ∑ m in finset.range n, x ^ m / m! + x ^ n * (n + 1) / (n! * n) :=
begin
 have h3 : |x| = x := by simpa,
 have h4 : |x| ≤ 1 := by rwa h3,
 have h' := real.exp_bound h4 hn,
 rw h3 at h',
 have h'' := (abs_sub_le_iff.1 h').1,
 have t := sub_le_iff_le_add'.1 h'',
 simpa [mul_div_assoc] using t
end

lemma abs_exp_sub_one_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1| ≤ 2 * |x| :=
begin
 have : complex.abs x ≤ 1 := by exact_mod_cast hx,
 exact_mod_cast complex.abs_exp_sub_one_le this,
end

lemma abs_exp_sub_one_sub_id_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1 - x| ≤ x ^ 2 :=
begin
 rw ←_root_.sq_abs,
 have : complex.abs x ≤ 1 := by exact_mod_cast hx,
 exact_mod_cast complex.abs_exp_sub_one_sub_id_le this,
end

/-- A finite initial segment of the exponential series, followed by an arbitrary tail.
For fixed `n` this is just a linear map wrt `r`, and each map is a simple linear function
of the previous (see `exp_near_succ`), with `exp_near n x r ⟶ exp x` as `n ⟶ ∞`,
for any `r`. -/
def exp_near (n : ℕ) (x r : ℝ) : ℝ := ∑ m in range n, x ^ m / m! + x ^ n / n! * r

@[simp] theorem exp_near_zero (x r) : exp_near 0 x r = r := by simp [exp_near]

@[simp] theorem exp_near_succ (n x r) : exp_near (n + 1) x r = exp_near n x (1 + x / (n+1) * r) :=
by simp [exp_near, range_succ, mul_add, add_left_comm, add_assoc, pow_succ, div_eq_mul_inv,
 mul_inv]; ac_refl

theorem exp_near_sub (n x r₁ r₂) : exp_near n x r₁ - exp_near n x r₂ = x ^ n / n! * (r₁ - r₂) :=
by simp [exp_near, mul_sub]

lemma exp_approx_end (n m : ℕ) (x : ℝ)
 (e₁ : n + 1 = m) (h : |x| ≤ 1) :
 |exp x - exp_near m x 0| ≤ |x| ^ m / m! * ((m+1)/m) :=
by { simp [exp_near], convert exp_bound h _ using 1, field_simp [mul_comm], linarith }

lemma exp_approx_succ {n} {x a₁ b₁ : ℝ} (m : ℕ)
 (e₁ : n + 1 = m) (a₂ b₂ : ℝ)
 (e : |1 + x / m * a₂ - a₁| ≤ b₁ - |x| / m * b₂)
 (h : |exp x - exp_near m x a₂| ≤ |x| ^ m / m! * b₂) :
 |exp x - exp_near n x a₁| ≤ |x| ^ n / n! * b₁ :=
begin
 refine (_root_.abs_sub_le _ _ _).trans ((add_le_add_right h _).trans _),
 subst e₁, rw [exp_near_succ]; rw [ exp_near_sub]; rw [ _root_.abs_mul],
 convert mul_le_mul_of_nonneg_left (le_sub_iff_add_le'.1 e) _,
 { simp [mul_add, pow_succ', div_eq_mul_inv, _root_.abs_mul, _root_.abs_inv, ← pow_abs, mul_inv],
 ac_refl },
 { simp [_root_.div_nonneg, _root_.abs_nonneg] }
end

lemma exp_approx_end' {n} {x a b : ℝ} (m : ℕ)
 (e₁ : n + 1 = m) (rm : ℝ) (er : ↑m = rm) (h : |x| ≤ 1)
 (e : |1 - a| ≤ b - |x| / rm * ((rm+1)/rm)) :
 |exp x - exp_near n x a| ≤ |x| ^ n / n! * b :=
by subst er; exact
exp_approx_succ _ e₁ _ _ (by simpa using e) (exp_approx_end _ _ _ e₁ h)

lemma exp_1_approx_succ_eq {n} {a₁ b₁ : ℝ} {m : ℕ}
 (en : n + 1 = m) {rm : ℝ} (er : ↑m = rm)
 (h : |exp 1 - exp_near m 1 ((a₁ - 1) * rm)| ≤ |1| ^ m / m! * (b₁ * rm)) :
 |exp 1 - exp_near n 1 a₁| ≤ |1| ^ n / n! * b₁ :=
begin
 subst er,
 refine exp_approx_succ _ en _ _ _ h,
 field_simp [show (m : ℝ) ≠ 0, by norm_cast; linarith],
end

lemma exp_approx_start (x a b : ℝ)
 (h : |exp x - exp_near 0 x a| ≤ |x| ^ 0 / 0! * b) :
 |exp x - a| ≤ b :=
by simpa using h

lemma cos_bound {x : ℝ} (hx : |x| ≤ 1) :
 |cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 * (5 / 96) :=
calc |cos x - (1 - x ^ 2 / 2)| = abs (complex.cos x - (1 - x ^ 2 / 2)) :
 by rw ← abs_of_real; simp [of_real_bit0, of_real_one, of_real_inv]
... = abs ((complex.exp (x * I) + complex.exp (-x * I) - (2 - x ^ 2)) / 2) :
 by simp [complex.cos, sub_div, add_div, neg_div, div_self (two_ne_zero' ℂ)]
... = abs (((complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m!) +
 ((complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m!))) / 2) :
 congr_arg abs (congr_arg (λ x : ℂ, x / 2) begin
 simp only [sum_range_succ],
 simp [pow_succ],
 apply complex.ext; simp [div_eq_mul_inv, norm_sq]; ring
 end)
... ≤ abs ((complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m!) / 2) +
 abs ((complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m!) / 2) :
 by rw add_div; exact complex.abs.add_le _ _
... = (abs ((complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m!)) / 2 +
 abs ((complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m!)) / 2) :
 by simp [map_div₀]
... ≤ ((complex.abs (x * I) ^ 4 * (nat.succ 4 * (4! * (4 : ℕ))⁻¹)) / 2 +
 (complex.abs (-x * I) ^ 4 * (nat.succ 4 * (4! * (4 : ℕ))⁻¹)) / 2) :
 add_le_add ((div_le_div_right (by norm_num)).2 (complex.exp_bound (by simpa) dec_trivial))
 ((div_le_div_right (by norm_num)).2 (complex.exp_bound (by simpa) dec_trivial))
... ≤ |x| ^ 4 * (5 / 96) : by norm_num; simp [mul_assoc, mul_comm, mul_left_comm, mul_div_assoc]

lemma sin_bound {x : ℝ} (hx : |x| ≤ 1) :
 |sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 4 * (5 / 96) :=
calc |sin x - (x - x ^ 3 / 6)| = abs (complex.sin x - (x - x ^ 3 / 6)) :
 by rw ← abs_of_real; simp [of_real_bit0, of_real_one, of_real_inv]
... = abs (((complex.exp (-x * I) - complex.exp (x * I)) * I - (2 * x - x ^ 3 / 3)) / 2) :
 by simp [complex.sin, sub_div, add_div, neg_div, mul_div_cancel_left _ (two_ne_zero' ℂ),
 div_div, show (3 : ℂ) * 2 = 6, by norm_num]
... = abs ((((complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m!) -
 (complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m!)) * I) / 2) :
 congr_arg abs (congr_arg (λ x : ℂ, x / 2) begin
 simp only [sum_range_succ],
 simp [pow_succ],
 apply complex.ext; simp [div_eq_mul_inv, norm_sq]; ring
 end)
... ≤ abs ((complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m!) * I / 2) +
 abs (-((complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m!) * I) / 2) :
 by rw [sub_mul]; rw [ sub_eq_add_neg]; rw [ add_div]; exact complex.abs.add_le _ _
... = (abs ((complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m!)) / 2 +
 abs ((complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m!)) / 2) :
 by simp [add_comm, map_div₀]
... ≤ ((complex.abs (x * I) ^ 4 * (nat.succ 4 * (4! * (4 : ℕ))⁻¹)) / 2 +
 (complex.abs (-x * I) ^ 4 * (nat.succ 4 * (4! * (4 : ℕ))⁻¹)) / 2) :
 add_le_add ((div_le_div_right (by norm_num)).2 (complex.exp_bound (by simpa) dec_trivial))
 ((div_le_div_right (by norm_num)).2 (complex.exp_bound (by simpa) dec_trivial))
... ≤ |x| ^ 4 * (5 / 96) : by norm_num; simp [mul_assoc, mul_comm, mul_left_comm, mul_div_assoc]

lemma cos_pos_of_le_one {x : ℝ} (hx : |x| ≤ 1) : 0 < cos x :=
calc 0 < (1 - x ^ 2 / 2) - |x| ^ 4 * (5 / 96) :
 sub_pos.2 $ lt_sub_iff_add_lt.2
 (calc |x| ^ 4 * (5 / 96) + x ^ 2 / 2
 ≤ 1 * (5 / 96) + 1 / 2 :
 add_le_add
 (mul_le_mul_of_nonneg_right (pow_le_one _ (abs_nonneg _) hx) (by norm_num))
 ((div_le_div_right (by norm_num)).2 (by rw [sq]; rw [ ← abs_mul_self]; rw [ _root_.abs_mul];
 exact mul_le_one hx (abs_nonneg _) hx))
 ... < 1 : by norm_num)
... ≤ cos x : sub_le_comm.1 (abs_sub_le_iff.1 (cos_bound hx)).2

lemma sin_pos_of_pos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) : 0 < sin x :=
calc 0 < x - x ^ 3 / 6 - |x| ^ 4 * (5 / 96) :
 sub_pos.2 $ lt_sub_iff_add_lt.2
 (calc |x| ^ 4 * (5 / 96) + x ^ 3 / 6
 ≤ x * (5 / 96) + x / 6 :
 add_le_add
 (mul_le_mul_of_nonneg_right
 (calc |x| ^ 4 ≤ |x| ^ 1 : pow_le_pow_of_le_one (abs_nonneg _)
 (by rwa _root_.abs_of_nonneg (le_of_lt hx0))
 dec_trivial
 ... = x : by simp [_root_.abs_of_nonneg (le_of_lt (hx0))]) (by norm_num))
 ((div_le_div_right (by norm_num)).2
 (calc x ^ 3 ≤ x ^ 1 : pow_le_pow_of_le_one (le_of_lt hx0) hx dec_trivial
 ... = x : pow_one _))
 ... < x : by linarith)
... ≤ sin x : sub_le_comm.1 (abs_sub_le_iff.1 (sin_bound
 (by rwa [_root_.abs_of_nonneg (le_of_lt hx0)]))).2

lemma sin_pos_of_pos_of_le_two {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 2) : 0 < sin x :=
have x / 2 ≤ 1, from (div_le_iff (by norm_num)).mpr (by simpa),
calc 0 < 2 * sin (x / 2) * cos (x / 2) :
 mul_pos (mul_pos (by norm_num) (sin_pos_of_pos_of_le_one (half_pos hx0) this))
 (cos_pos_of_le_one (by rwa [_root_.abs_of_nonneg (le_of_lt (half_pos hx0))]))
... = sin x : by rw [← sin_two_mul]; rw [ two_mul]; rw [ add_halves]

lemma cos_one_le : cos 1 ≤ 2 / 3 :=
calc cos 1 ≤ |(1 : ℝ)| ^ 4 * (5 / 96) + (1 - 1 ^ 2 / 2) :
 sub_le_iff_le_add.1 (abs_sub_le_iff.1 (cos_bound (by simp))).1
... ≤ 2 / 3 : by norm_num

lemma cos_one_pos : 0 < cos 1 := cos_pos_of_le_one (le_of_eq abs_one)

lemma cos_two_neg : cos 2 < 0 :=
calc cos 2 = cos (2 * 1) : congr_arg cos (mul_one _).symm
 ... = _ : real.cos_two_mul 1
 ... ≤ 2 * (2 / 3) ^ 2 - 1 : sub_le_sub_right (mul_le_mul_of_nonneg_left
 (by { rw [sq]; rw [ sq], exact mul_self_le_mul_self (le_of_lt cos_one_pos) cos_one_le })
 zero_le_two) _
 ... < 0 : by norm_num

lemma exp_bound_div_one_sub_of_interval' {x : ℝ} (h1 : 0 < x) (h2 : x < 1) :
 real.exp x < 1 / (1 - x) :=
have H : 0 < 1 - (1 + x + x ^ 2) * (1 - x) :=
calc 0 < x ^ 3 : by positivity
... = 1 - (1 + x + x ^ 2) * (1 - x) : by ring,
calc exp x ≤ _ : exp_bound' h1.le h2.le zero_lt_three
... ≤ 1 + x + x ^ 2 : by norm_num [finset.sum]; nlinarith
... < 1 / (1 - x) : by rw lt_div_iff; nlinarith

lemma exp_bound_div_one_sub_of_interval {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) :
 real.exp x ≤ 1 / (1 - x) :=
begin
 rcases eq_or_lt_of_le h1 with rfl | h1,
 { simp },
 { exact (exp_bound_div_one_sub_of_interval' h1 h2).le }
end

lemma one_sub_lt_exp_minus_of_pos {y : ℝ} (h : 0 < y) : 1 - y < real.exp (-y) :=
begin
 cases le_or_lt 1 y with h' h',
 { linarith [(-y).exp_pos] },
 rw [exp_neg]; rw [ lt_inv _ y.exp_pos]; rw [ inv_eq_one_div],
 { exact exp_bound_div_one_sub_of_interval' h h' },
 { linarith },
end

lemma one_sub_le_exp_minus_of_nonneg {y : ℝ} (h : 0 ≤ y) : 1 - y ≤ real.exp (-y) :=
begin
 rcases eq_or_lt_of_le h with rfl | h,
 { simp },
 { exact (one_sub_lt_exp_minus_of_pos h).le }
end

lemma add_one_lt_exp_of_neg {x : ℝ} (h : x < 0) : x + 1 < real.exp x :=
begin
 have h1 : 0 < -x := by linarith,
 simpa [add_comm] using one_sub_lt_exp_minus_of_pos h1
end

lemma add_one_lt_exp_of_nonzero {x : ℝ} (hx : x ≠ 0) : x + 1 < real.exp x :=
begin
 cases lt_or_gt_of_ne hx,
 { exact real.add_one_lt_exp_of_neg h },
 exact add_one_lt_exp_of_pos h,
end

lemma add_one_le_exp (x : ℝ) : x + 1 ≤ real.exp x :=
begin
 cases le_or_lt 0 x,
 { exact real.add_one_le_exp_of_nonneg h },
 exact (add_one_lt_exp_of_neg h).le,
end

lemma one_sub_div_pow_le_exp_neg {n : ℕ} {t : ℝ} (ht' : t ≤ n) : (1 - t / n) ^ n ≤ exp (-t) :=
begin
 rcases eq_or_ne n 0 with rfl | hn,
 { simp, rwa nat.cast_zero at ht' },
 convert pow_le_pow_of_le_left _ (add_one_le_exp (-(t / n))) n,
 { abel },
 { rw ←real.exp_nat_mul, congr' 1,
 field_simp [nat.cast_ne_zero.mpr hn], ring },
 { rwa [add_comm]; rwa [ ←sub_eq_add_neg]; rwa [ sub_nonneg]; rwa [ div_le_one],
 positivity }
end

end real

namespace tactic
open positivity real

/-- Extension for the `positivity` tactic: `real.exp` is always positive. -/
@[positivity]
meta def positivity_exp : expr → tactic strictness
| `(real.exp %%a) := positive <$> mk_app `real.exp_pos [a]
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `real.exp r`"

end tactic

namespace complex

@[simp] lemma abs_cos_add_sin_mul_I (x : ℝ) : abs (cos x + sin x * I) = 1 :=
have _ := real.sin_sq_add_cos_sq x,
by simp [add_comm, abs, norm_sq, sq, *, sin_of_real_re, cos_of_real_re, mul_re] at *

@[simp] lemma abs_exp_of_real (x : ℝ) : abs (exp x) = real.exp x :=
by rw [← of_real_exp]; exact abs_of_nonneg (le_of_lt (real.exp_pos _))

@[simp] lemma abs_exp_of_real_mul_I (x : ℝ) : abs (exp (x * I)) = 1 :=
by rw [exp_mul_I]; rw [ abs_cos_add_sin_mul_I]

lemma abs_exp (z : ℂ) : abs (exp z) = real.exp z.re :=
by rw [exp_eq_exp_re_mul_sin_add_cos]; rw [ map_mul]; rw [ abs_exp_of_real]; rw [ abs_cos_add_sin_mul_I]; rw [ mul_one]

lemma abs_exp_eq_iff_re_eq {x y : ℂ} : abs (exp x) = abs (exp y) ↔ x.re = y.re :=
by rw [abs_exp]; rw [ abs_exp]; rw [ real.exp_eq_exp]

end complex

