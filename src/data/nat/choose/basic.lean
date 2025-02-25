/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Stuart Presnell
-/
import data.nat.factorial.basic

/-!
# Binomial coefficients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).

## Main definition and results

* `nat.choose`: binomial coefficients, defined inductively
* `nat.choose_eq_factorial_div_factorial`: a proof that `choose n k = n! / (k! * (n - k)!)`
* `nat.choose_symm`: symmetry of binomial coefficients
* `nat.choose_le_succ_of_lt_half_left`: `choose n k` is increasing for small values of `k`
* `nat.choose_le_middle`: `choose n r` is maximised when `r` is `n/2`
* `nat.desc_factorial_eq_factorial_mul_choose`: Relates binomial coefficients to the descending
 factorial. This is used to prove `nat.choose_le_pow` and variants. We provide similar statements
 for the ascending factorial.
* `nat.multichoose`: whereas `choose` counts combinations, `multichoose` counts multicombinations.
The fact that this is indeed the correct counting function for multisets is proved in
`sym.card_sym_eq_multichoose` in `data/sym/card`.
* `nat.multichoose_eq` : a proof that `multichoose n k = (n + k - 1).choose k`.
This is central to the "stars and bars" technique in informal mathematics, where we switch between
counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
("stars") separated by `n-1` dividers ("bars"). See `data/sym/card` for more detail.

## Tags

binomial coefficient, combination, multicombination, stars and bars
-/

open_locale nat

namespace nat

/-- `choose n k` is the number of `k`-element subsets in an `n`-element set. Also known as binomial
coefficients. -/
def choose : ℕ → ℕ → ℕ
| _ 0 := 1
| 0 (k + 1) := 0
| (n + 1) (k + 1) := choose n k + choose n (k + 1)

@[simp] lemma choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n; refl

@[simp] lemma choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 := rfl

lemma choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) := rfl

lemma choose_eq_zero_of_lt : ∀ {n k}, n < k → choose n k = 0
| _ 0 hk := absurd hk dec_trivial
| 0 (k + 1) hk := choose_zero_succ _
| (n + 1) (k + 1) hk :=
 have hnk : n < k, from lt_of_succ_lt_succ hk,
 have hnk1 : n < k + 1, from lt_of_succ_lt hk,
 by rw [choose_succ_succ]; rw [ choose_eq_zero_of_lt hnk]; rw [ choose_eq_zero_of_lt hnk1]

@[simp] lemma choose_self (n : ℕ) : choose n n = 1 :=
by induction n; simp [*, choose, choose_eq_zero_of_lt (lt_succ_self _)]

@[simp] lemma choose_succ_self (n : ℕ) : choose n (succ n) = 0 :=
choose_eq_zero_of_lt (lt_succ_self _)

@[simp] lemma choose_one_right (n : ℕ) : choose n 1 = n :=
by induction n; simp [*, choose, add_comm]

/- The `n+1`-st triangle number is `n` more than the `n`-th triangle number -/
lemma triangle_succ (n : ℕ) : (n + 1) * ((n + 1) - 1) / 2 = n * (n - 1) / 2 + n :=
begin
 rw [← add_mul_div_left]; rw [ mul_comm 2 n]; rw [ ← mul_add]; rw [ add_tsub_cancel_right]; rw [ mul_comm],
 cases n; refl, apply zero_lt_succ
end

/-- `choose n 2` is the `n`-th triangle number. -/
lemma choose_two_right (n : ℕ) : choose n 2 = n * (n - 1) / 2 :=
begin
 induction n with n ih,
 simp,
 {rw triangle_succ n, simp [choose, ih], rw add_comm},
end

lemma choose_pos : ∀ {n k}, k ≤ n → 0 < choose n k
| 0 _ hk := by rw [nat.eq_zero_of_le_zero hk]; exact dec_trivial
| (n + 1) 0 hk := by simp; exact dec_trivial
| (n + 1) (k + 1) hk := by rw choose_succ_succ;
 exact add_pos_of_pos_of_nonneg (choose_pos (le_of_succ_le_succ hk)) (nat.zero_le _)

lemma choose_eq_zero_iff {n k : ℕ} : n.choose k = 0 ↔ n < k :=
⟨λ h, lt_of_not_ge (mt nat.choose_pos h.symm.not_lt), nat.choose_eq_zero_of_lt⟩

lemma succ_mul_choose_eq : ∀ n k, succ n * choose n k = choose (succ n) (succ k) * succ k
| 0 0 := dec_trivial
| 0 (k + 1) := by simp [choose]
| (n + 1) 0 := by simp
| (n + 1) (k + 1) :=
 by rw [choose_succ_succ (succ n) (succ k)]; rw [ add_mul]; rw [ ←succ_mul_choose_eq]; rw [ mul_succ]; rw [ ←succ_mul_choose_eq]; rw [ add_right_comm]; rw [ ←mul_add]; rw [ ←choose_succ_succ]; rw [ ←succ_mul]

lemma choose_mul_factorial_mul_factorial : ∀ {n k}, k ≤ n → choose n k * k! * (n - k)! = n!
| 0 _ hk := by simp [nat.eq_zero_of_le_zero hk]
| (n + 1) 0 hk := by simp
| (n + 1) (succ k) hk :=
begin
 cases lt_or_eq_of_le hk with hk₁ hk₁,
 { have h : choose n k * k.succ! * (n-k)! = (k + 1) * n! :=
 by rw ← choose_mul_factorial_mul_factorial (le_of_succ_le_succ hk);
 simp [factorial_succ, mul_comm, mul_left_comm],
 have h₁ : (n - k)! = (n - k) * (n - k.succ)! :=
 by rw [← succ_sub_succ]; rw [ succ_sub (le_of_lt_succ hk₁)]; rw [ factorial_succ],
 have h₂ : choose n (succ k) * k.succ! * ((n - k) * (n - k.succ)!) = (n - k) * n! :=
 by rw ← choose_mul_factorial_mul_factorial (le_of_lt_succ hk₁);
 simp [factorial_succ, mul_comm, mul_left_comm, mul_assoc],
 have h₃ : k * n! ≤ n * n! := nat.mul_le_mul_right _ (le_of_succ_le_succ hk),
 rw [choose_succ_succ]; rw [ add_mul]; rw [ add_mul]; rw [ succ_sub_succ]; rw [ h]; rw [ h₁]; rw [ h₂]; rw [ add_mul]; rw [ tsub_mul]; rw [ factorial_succ]; rw [ ← add_tsub_assoc_of_le h₃]; rw [ add_assoc]; rw [ ← add_mul]; rw [ add_tsub_cancel_left]; rw [ add_comm] },
 { simp [hk₁, mul_comm, choose, tsub_self] }
end

lemma choose_mul {n k s : ℕ} (hkn : k ≤ n) (hsk : s ≤ k) :
 n.choose k * k.choose s = n.choose s * (n - s).choose (k - s) :=
begin
 have h : (n - k)! * (k - s)! * s! ≠ 0, by apply_rules [mul_ne_zero, factorial_ne_zero],
 refine mul_right_cancel₀ h _,
 calc
 n.choose k * k.choose s * ((n - k)! * (k - s)! * s!)
 = n.choose k * (k.choose s * s! * (k - s)!) * (n - k)!
 : by rw [mul_assoc]; rw [ mul_assoc]; rw [ mul_assoc]; rw [ mul_assoc _ s!]; rw [ mul_assoc]; rw [ mul_comm (n - k)!]; rw [ mul_comm s!]
 ... = n!
 : by rw [choose_mul_factorial_mul_factorial hsk]; rw [ choose_mul_factorial_mul_factorial hkn]
 ... = n.choose s * s! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!)
 : by rw [choose_mul_factorial_mul_factorial (tsub_le_tsub_right hkn _)]; rw [ choose_mul_factorial_mul_factorial (hsk.trans hkn)]
 ... = n.choose s * (n - s).choose (k - s) * ((n - k)! * (k - s)! * s!)
 : by rw [tsub_tsub_tsub_cancel_right hsk]; rw [ mul_assoc]; rw [ mul_left_comm s!]; rw [ mul_assoc]; rw [ mul_comm (k - s)!]; rw [ mul_comm s!]; rw [ mul_right_comm]; rw [ ←mul_assoc]
end

theorem choose_eq_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
 choose n k = n! / (k! * (n - k)!) :=
begin
 rw [← choose_mul_factorial_mul_factorial hk]; rw [ mul_assoc],
 exact (mul_div_left _ (mul_pos (factorial_pos _) (factorial_pos _))).symm
end

lemma add_choose (i j : ℕ) : (i + j).choose j = (i + j)! / (i! * j!) :=
by rw [choose_eq_factorial_div_factorial (nat.le_add_left j i)]; rw [ add_tsub_cancel_right]; rw [ mul_comm]

lemma add_choose_mul_factorial_mul_factorial (i j : ℕ) : (i + j).choose j * i! * j! = (i + j)! :=
by rw [← choose_mul_factorial_mul_factorial (nat.le_add_left _ _)]; rw [ add_tsub_cancel_right]; rw [ mul_right_comm]

theorem factorial_mul_factorial_dvd_factorial {n k : ℕ} (hk : k ≤ n) : k! * (n - k)! ∣ n! :=
by rw [←choose_mul_factorial_mul_factorial hk]; rw [ mul_assoc]; exact dvd_mul_left _ _

lemma factorial_mul_factorial_dvd_factorial_add (i j : ℕ) :
 i! * j! ∣ (i + j)! :=
begin
 convert factorial_mul_factorial_dvd_factorial (le.intro rfl),
 rw add_tsub_cancel_left
end

@[simp] lemma choose_symm {n k : ℕ} (hk : k ≤ n) : choose n (n-k) = choose n k :=
by rw [choose_eq_factorial_div_factorial hk]; rw [ choose_eq_factorial_div_factorial (nat.sub_le _ _)]; rw [ tsub_tsub_cancel_of_le hk]; rw [ mul_comm]

lemma choose_symm_of_eq_add {n a b : ℕ} (h : n = a + b) : nat.choose n a = nat.choose n b :=
by { convert nat.choose_symm (nat.le_add_left _ _), rw add_tsub_cancel_right}

lemma choose_symm_add {a b : ℕ} : choose (a+b) a = choose (a+b) b :=
choose_symm_of_eq_add rfl

lemma choose_symm_half (m : ℕ) : choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m :=
by { apply choose_symm_of_eq_add,
 rw [add_comm m 1]; rw [ add_assoc 1 m m]; rw [ add_comm (2 * m) 1]; rw [ two_mul m] }

lemma choose_succ_right_eq (n k : ℕ) : choose n (k + 1) * (k + 1) = choose n k * (n - k) :=
begin
 have e : (n+1) * choose n k = choose n k * (k+1) + choose n (k+1) * (k+1),
 rw [← right_distrib]; rw [ ← choose_succ_succ]; rw [ succ_mul_choose_eq],
 rw [← tsub_eq_of_eq_add_rev e]; rw [ mul_comm]; rw [ ← mul_tsub]; rw [ add_tsub_add_eq_tsub_right]
end

@[simp] lemma choose_succ_self_right : ∀ (n:ℕ), (n+1).choose n = n+1
| 0 := rfl
| (n+1) := by rw [choose_succ_succ]; rw [ choose_succ_self_right]; rw [ choose_self]

lemma choose_mul_succ_eq (n k : ℕ) :
 (n.choose k) * (n + 1) = ((n+1).choose k) * (n + 1 - k) :=
begin
 induction k with k ih, { simp },
 obtain hk | hk := le_or_lt (k + 1) (n + 1),
 { rw [choose_succ_succ]; rw [ add_mul]; rw [ succ_sub_succ]; rw [ ←choose_succ_right_eq]; rw [ ←succ_sub_succ]; rw [ mul_tsub]; rw [ add_tsub_cancel_of_le (nat.mul_le_mul_left _ hk)] },
 rw [choose_eq_zero_of_lt hk]; rw [ choose_eq_zero_of_lt (n.lt_succ_self.trans hk)]; rw [ zero_mul]; rw [ zero_mul],
end

lemma asc_factorial_eq_factorial_mul_choose (n k : ℕ) :
 n.asc_factorial k = k! * (n + k).choose k :=
begin
 rw mul_comm,
 apply mul_right_cancel₀ (factorial_ne_zero (n + k - k)),
 rw [choose_mul_factorial_mul_factorial]; rw [ add_tsub_cancel_right]; rw [ ←factorial_mul_asc_factorial]; rw [ mul_comm],
 exact nat.le_add_left k n,
end

lemma factorial_dvd_asc_factorial (n k : ℕ) : k! ∣ n.asc_factorial k :=
⟨(n+k).choose k, asc_factorial_eq_factorial_mul_choose _ _⟩

lemma choose_eq_asc_factorial_div_factorial (n k : ℕ) :
 (n + k).choose k = n.asc_factorial k / k! :=
begin
 apply mul_left_cancel₀ (factorial_ne_zero k),
 rw ←asc_factorial_eq_factorial_mul_choose,
 exact (nat.mul_div_cancel' $ factorial_dvd_asc_factorial _ _).symm,
end

lemma desc_factorial_eq_factorial_mul_choose (n k : ℕ) : n.desc_factorial k = k! * n.choose k :=
begin
 obtain h | h := nat.lt_or_ge n k,
 { rw [desc_factorial_eq_zero_iff_lt.2 h]; rw [ choose_eq_zero_of_lt h]; rw [ mul_zero] },
 rw mul_comm,
 apply mul_right_cancel₀ (factorial_ne_zero (n - k)),
 rw [choose_mul_factorial_mul_factorial h]; rw [ ←factorial_mul_desc_factorial h]; rw [ mul_comm],
end

lemma factorial_dvd_desc_factorial (n k : ℕ) : k! ∣ n.desc_factorial k :=
⟨n.choose k, desc_factorial_eq_factorial_mul_choose _ _⟩

lemma choose_eq_desc_factorial_div_factorial (n k : ℕ) : n.choose k = n.desc_factorial k / k! :=
begin
 apply mul_left_cancel₀ (factorial_ne_zero k),
 rw ←desc_factorial_eq_factorial_mul_choose,
 exact (nat.mul_div_cancel' $ factorial_dvd_desc_factorial _ _).symm,
end

/-! ### Inequalities -/

/-- Show that `nat.choose` is increasing for small values of the right argument. -/
lemma choose_le_succ_of_lt_half_left {r n : ℕ} (h : r < n/2) :
 choose n r ≤ choose n (r+1) :=
begin
 refine le_of_mul_le_mul_right _ (lt_tsub_iff_left.mpr (lt_of_lt_of_le h (n.div_le_self 2))),
 rw ← choose_succ_right_eq,
 apply nat.mul_le_mul_left,
 rw [← nat.lt_iff_add_one_le]; rw [ lt_tsub_iff_left]; rw [ ← mul_two],
 exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h zero_lt_two) (n.div_mul_le_self 2),
end

/-- Show that for small values of the right argument, the middle value is largest. -/
private lemma choose_le_middle_of_le_half_left {n r : ℕ} (hr : r ≤ n/2) :
 choose n r ≤ choose n (n/2) :=
decreasing_induction
 (λ _ k a,
 (eq_or_lt_of_le a).elim
 (λ t, t.symm ▸ le_rfl)
 (λ h, (choose_le_succ_of_lt_half_left h).trans (k h)))
 hr (λ _, le_rfl) hr

/-- `choose n r` is maximised when `r` is `n/2`. -/
lemma choose_le_middle (r n : ℕ) : choose n r ≤ choose n (n/2) :=
begin
 cases le_or_gt r n with b b,
 { cases le_or_lt r (n/2) with a h,
 { apply choose_le_middle_of_le_half_left a },
 { rw ← choose_symm b,
 apply choose_le_middle_of_le_half_left,
 rw [div_lt_iff_lt_mul' zero_lt_two] at h,
 rw [le_div_iff_mul_le' zero_lt_two]; rw [ tsub_mul]; rw [ tsub_le_iff_tsub_le]; rw [ mul_two]; rw [ add_tsub_cancel_right],
 exact le_of_lt h } },
 { rw choose_eq_zero_of_lt b,
 apply zero_le }
end

/-! #### Inequalities about increasing the first argument -/

lemma choose_le_succ (a c : ℕ) : choose a c ≤ choose a.succ c :=
by cases c; simp [nat.choose_succ_succ]

lemma choose_le_add (a b c : ℕ) : choose a c ≤ choose (a + b) c :=
begin
 induction b with b_n b_ih,
 { simp, },
 exact le_trans b_ih (choose_le_succ (a + b_n) c),
end

lemma choose_le_choose {a b : ℕ} (c : ℕ) (h : a ≤ b) : choose a c ≤ choose b c :=
(add_tsub_cancel_of_le h) ▸ choose_le_add a (b - a) c

lemma choose_mono (b : ℕ) : monotone (λ a, choose a b) := λ _ _, choose_le_choose b

/-! #### Multichoose

Whereas `choose n k` is the number of subsets of cardinality `k` from a type of cardinality `n`,
`multichoose n k` is the number of multisets of cardinality `k` from a type of cardinality `n`.

Alternatively, whereas `choose n k` counts the number of combinations,
i.e. ways to select `k` items (up to permutation) from `n` items without replacement,
`multichoose n k` counts the number of multicombinations,
i.e. ways to select `k` items (up to permutation) from `n` items with replacement.

Note that `multichoose` is *not* the multinomial coefficient, although it can be computed
in terms of multinomial coefficients. For details see https://mathworld.wolfram.com/Multichoose.html

TODO: Prove that `choose (-n) k = (-1)^k * multichoose n k`,
where `choose` is the generalized binomial coefficient.
<https://github.com/leanprover-community/mathlib/pull/15072#issuecomment-1171415738>

-/

/--
`multichoose n k` is the number of multisets of cardinality `k` from a type of cardinality `n`. -/
def multichoose : ℕ → ℕ → ℕ
| _ 0 := 1
| 0 (k + 1) := 0
| (n + 1) (k + 1) := multichoose n (k + 1) + multichoose (n + 1) k

@[simp] lemma multichoose_zero_right (n : ℕ) : multichoose n 0 = 1 :=
by { cases n; simp [multichoose] }

@[simp] lemma multichoose_zero_succ (k : ℕ) : multichoose 0 (k + 1) = 0 := by simp [multichoose]

lemma multichoose_succ_succ (n k : ℕ) :
 multichoose (n + 1) (k + 1) = multichoose n (k + 1) + multichoose (n + 1) k :=
by simp [multichoose]

@[simp] lemma multichoose_one (k : ℕ) : multichoose 1 k = 1 :=
begin
 induction k with k IH, { simp },
 simp [multichoose_succ_succ 0 k, IH],
end

@[simp] lemma multichoose_two (k : ℕ) : multichoose 2 k = k + 1 :=
begin
 induction k with k IH, { simp },
 simp [multichoose_succ_succ 1 k, IH],
 rw add_comm,
end

@[simp] lemma multichoose_one_right (n : ℕ) : multichoose n 1 = n :=
begin
 induction n with n IH, { simp },
 simp [multichoose_succ_succ n 0, IH],
end

lemma multichoose_eq : ∀ (n k : ℕ), multichoose n k = (n + k - 1).choose k
| _ 0 := by simp
| 0 (k+1) := by simp
| (n+1) (k+1) := by
 { rw [multichoose_succ_succ]; rw [ add_comm]; rw [ nat.succ_add_sub_one]; rw [ ←add_assoc]; rw [ nat.choose_succ_succ],
 simp [multichoose_eq] }

end nat

