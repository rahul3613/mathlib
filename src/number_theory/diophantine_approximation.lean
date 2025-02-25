/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
import algebra.continued_fractions.computation.approximation_corollaries
import algebra.continued_fractions.computation.translations
import combinatorics.pigeonhole
import data.int.units
import data.real.irrational
import ring_theory.coprime.lemmas
import tactic.basic

/-!
# Diophantine Approximation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The first part of this file gives proofs of various versions of
**Dirichlet's approximation theorem** and its important consequence that when $\xi$ is an
irrational real number, then there are infinitely many rationals $x/y$ (in lowest terms)
such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{y^2} \,.$$
The proof is based on the pigeonhole principle.

The second part of the file gives a proof of **Legendre's Theorem** on rational approximation,
which states that if $\xi$ is a real number and $x/y$ is a rational number such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{2y^2} \,,$$
then $x/y$ must be a convergent of the continued fraction expansion of $\xi$.

## Main statements

The main results are three variants of Dirichlet's approximation theorem:
* `real.exists_int_int_abs_mul_sub_le`, which states that for all real `ξ` and natural `0 < n`,
 there are integers `j` and `k` with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`,
* `real.exists_nat_abs_mul_sub_round_le`, which replaces `j` by `round(k*ξ)` and uses
 a natural number `k`,
* `real.exists_rat_abs_sub_le_and_denom_le`, which says that there is a rational number `q`
 satisfying `|ξ - q| ≤ 1/((n+1)*q.denom)` and `q.denom ≤ n`,

and
* `real.infinite_rat_abs_sub_lt_one_div_denom_sq_of_irrational`, which states that
 for irrational `ξ`, the set `{q : ℚ | |ξ - q| < 1/q.denom^2}` is infinite.

We also show a converse,
* `rat.finite_rat_abs_sub_lt_one_div_denom_sq`, which states that the set above is finite
 when `ξ` is a rational number.

Both statements are combined to give an equivalence,
`real.infinite_rat_abs_sub_lt_one_div_denom_sq_iff_irrational`.

There are two versions of Legendre's Theorem. One, `real.exists_rat_eq_convergent`, uses
`real.convergent`, a simple recursive definition of the convergents that is also defined
in this file, whereas the other, `real.exists_continued_fraction_convergent_eq_rat`, uses
`generalized_continued_fraction.convergents` of `generalized_continued_fraction.of ξ`.

## Implementation notes

We use the namespace `real` for the results on real numbers and `rat` for the results
on rational numbers. We introduce a secondary namespace `real.contfrac_legendre`
to separate off a definition and some technical auxiliary lemmas used in the proof
of Legendre's Theorem. For remarks on the proof of Legendre's Theorem, see below.

## References

<https://en.wikipedia.org/wiki/Dirichlet%27s_approximation_theorem>
<https://de.wikipedia.org/wiki/Kettenbruch> (The German Wikipedia page on continued
fractions is much more extensive than the English one.)

## Tags

Diophantine approximation, Dirichlet's approximation theorem, continued fraction
-/

namespace real

section dirichlet

/-!
### Dirichlet's approximation theorem

We show that for any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.denom ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.denom)`.
-/

open finset int

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there are integers `j` and `k`,
with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`.

See also `real.exists_nat_abs_mul_sub_round_le`. -/
lemma exists_int_int_abs_mul_sub_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
 ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - j| ≤ 1 / (n + 1) :=
begin
 let f : ℤ → ℤ := λ m, ⌊fract (ξ * m) * (n + 1)⌋,
 have hn : 0 < (n : ℝ) + 1 := by exact_mod_cast nat.succ_pos _,
 have hfu := λ m : ℤ, mul_lt_of_lt_one_left hn $ fract_lt_one (ξ * ↑m),
 conv in (|_| ≤ _) { rw [mul_comm]; rw [ le_div_iff hn]; rw [ ← abs_of_pos hn]; rw [ ← abs_mul], },
 let D := Icc (0 : ℤ) n,
 by_cases H : ∃ m ∈ D, f m = n,
 { obtain ⟨m, hm, hf⟩ := H,
 have hf' : ((n : ℤ) : ℝ) ≤ fract (ξ * m) * (n + 1) := hf ▸ floor_le (fract (ξ * m) * (n + 1)),
 have hm₀ : 0 < m,
 { have hf₀ : f 0 = 0,
 { simp only [floor_eq_zero_iff, algebra_map.coe_zero, mul_zero, fract_zero, zero_mul,
 set.left_mem_Ico, zero_lt_one], },
 refine ne.lt_of_le (λ h, n_pos.ne _) (mem_Icc.mp hm).1,
 exact_mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n), },
 refine ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, _⟩,
 rw [cast_add]; rw [ ← sub_sub]; rw [ sub_mul]; rw [ cast_one]; rw [ one_mul]; rw [ abs_le],
 refine ⟨le_sub_iff_add_le.mpr _,
 sub_le_iff_le_add.mpr $ le_of_lt $ (hfu m).trans $ lt_one_add _⟩,
 simpa only [neg_add_cancel_comm_assoc] using hf', },
 { simp_rw [not_exists] at H,
 have hD : (Ico (0 : ℤ) n).card < D.card,
 { rw [card_Icc]; rw [ card_Ico], exact lt_add_one n, },
 have hfu' : ∀ m, f m ≤ n := λ m, lt_add_one_iff.mp (floor_lt.mpr (by exact_mod_cast hfu m)),
 have hwd : ∀ m : ℤ, m ∈ D → f m ∈ Ico (0 : ℤ) n :=
 λ x hx, mem_Ico.mpr ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le),
 ne.lt_of_le (H x hx) (hfu' x)⟩,
 have : ∃ (x : ℤ) (hx : x ∈ D) (y : ℤ) (hy : y ∈ D), x < y ∧ f x = f y,
 { obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd,
 rcases lt_trichotomy x y with h | h | h,
 exacts [⟨x, hx, y, hy, h, hxy⟩, false.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩], },
 obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ := this,
 refine ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
 sub_le_iff_le_add.mpr $ le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, _⟩,
 convert_to |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| ≤ 1,
 { congr, push_cast, simp only [fract], ring, },
 exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le, }
end

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a natural number `k`,
with `0 < k ≤ n` such that `|k*ξ - round(k*ξ)| ≤ 1/(n+1)`.
-/
lemma exists_nat_abs_mul_sub_round_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
 ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - round (↑k * ξ)| ≤ 1 / (n + 1) :=
begin
 obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos,
 have hk := to_nat_of_nonneg hk₀.le,
 rw [← hk] at hk₀ hk₁ h,
 exact ⟨k.to_nat, coe_nat_pos.mp hk₀, nat.cast_le.mp hk₁, (round_le (↑k.to_nat * ξ) j).trans h⟩,
end

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.denom ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.denom)`. -/
lemma exists_rat_abs_sub_le_and_denom_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
 ∃ q : ℚ, |ξ - q| ≤ 1 / ((n + 1) * q.denom) ∧ q.denom ≤ n :=
begin
 obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos,
 have hk₀' : (0 : ℝ) < k := int.cast_pos.mpr hk₀,
 have hden : ((j / k : ℚ).denom : ℤ) ≤ k,
 { convert le_of_dvd hk₀ (rat.denom_dvd j k), exact rat.coe_int_div_eq_mk, },
 refine ⟨j / k, _, nat.cast_le.mp (hden.trans hk₁)⟩,
 rw [← div_div]; rw [ le_div_iff (nat.cast_pos.mpr $ rat.pos _ : (0 : ℝ) < _)],
 refine (mul_le_mul_of_nonneg_left (int.cast_le.mpr hden : _ ≤ (k : ℝ)) (abs_nonneg _)).trans _,
 rwa [← abs_of_pos hk₀']; rwa [ rat.cast_div]; rwa [ rat.cast_coe_int]; rwa [ rat.cast_coe_int]; rwa [ ← abs_mul]; rwa [ sub_mul]; rwa [ div_mul_cancel _ hk₀'.ne']; rwa [ mul_comm],
end

end dirichlet

section rat_approx

/-!
### Infinitely many good approximations to irrational numbers

We show that an irrational real number `ξ` has infinitely many "good rational approximations",
i.e., fractions `x/y` in lowest terms such that `|ξ - x/y| < 1/y^2`.
-/

open set

/-- Given any rational approximation `q` to the irrational real number `ξ`, there is
a good rational approximation `q'` such that `|ξ - q'| < |ξ - q|`. -/
lemma exists_rat_abs_sub_lt_and_lt_of_irrational {ξ : ℝ} (hξ : irrational ξ) (q : ℚ) :
 ∃ q' : ℚ, |ξ - q'| < 1 / q'.denom ^ 2 ∧ |ξ - q'| < |ξ - q| :=
begin
 have h := abs_pos.mpr (sub_ne_zero.mpr $ irrational.ne_rat hξ q),
 obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|),
 have m_pos : (0 : ℝ) < m := (one_div_pos.mpr h).trans hm,
 obtain ⟨q', hbd, hden⟩ := exists_rat_abs_sub_le_and_denom_le ξ (nat.cast_pos.mp m_pos),
 have den_pos : (0 : ℝ) < q'.denom := nat.cast_pos.mpr q'.pos,
 have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos,
 refine ⟨q', lt_of_le_of_lt hbd _,
 lt_of_le_of_lt hbd $ (one_div_lt md_pos h).mpr $ hm.trans $
 lt_of_lt_of_le (lt_add_one _) $ (le_mul_iff_one_le_right $
 add_pos m_pos zero_lt_one).mpr $ by exact_mod_cast (q'.pos : 1 ≤ q'.denom)⟩,
 rw [sq]; rw [ one_div_lt_one_div md_pos (mul_pos den_pos den_pos)]; rw [ mul_lt_mul_right den_pos],
 exact lt_add_of_le_of_pos (nat.cast_le.mpr hden) zero_lt_one,
end

/-- If `ξ` is an irrational real number, then there are infinitely many good
rational approximations to `ξ`. -/
lemma infinite_rat_abs_sub_lt_one_div_denom_sq_of_irrational {ξ : ℝ} (hξ : irrational ξ) :
 {q : ℚ | |ξ - q| < 1 / q.denom ^ 2}.infinite :=
begin
 refine or.resolve_left (set.finite_or_infinite _) (λ h, _),
 obtain ⟨q, _, hq⟩ := exists_min_image {q : ℚ | |ξ - q| < 1 / q.denom ^ 2} (λ q, |ξ - q|) h
 ⟨⌊ξ⌋, by simp [abs_of_nonneg, int.fract_lt_one]⟩,
 obtain ⟨q', hmem, hbetter⟩ := exists_rat_abs_sub_lt_and_lt_of_irrational hξ q,
 exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter),
end

end rat_approx

end real

namespace rat

/-!
### Finitely many good approximations to rational numbers

We now show that a rational number `ξ` has only finitely many good rational
approximations.
-/

open set

/-- If `ξ` is rational, then the good rational approximations to `ξ` have bounded
numerator and denominator. -/
lemma denom_le_and_le_num_le_of_sub_lt_one_div_denom_sq {ξ q : ℚ} (h : |ξ - q| < 1 / q.denom ^ 2) :
 q.denom ≤ ξ.denom ∧ ⌈ξ * q.denom⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * q.denom⌋ + 1 :=
begin
 have hq₀ : (0 : ℚ) < q.denom := nat.cast_pos.mpr q.pos,
 replace h : |ξ * q.denom - q.num| < 1 / q.denom,
 { rw ← mul_lt_mul_right hq₀ at h,
 conv_lhs at h { rw [← abs_of_pos hq₀]; rw [ ← abs_mul]; rw [ sub_mul]; rw [ mul_denom_eq_num], },
 rwa [sq] at h; rwa [ div_mul] at h; rwa [ mul_div_cancel_left _ hq₀.ne'] at h, },
 split,
 { rcases eq_or_ne ξ q with rfl | H,
 { exact le_rfl, },
 { have hξ₀ : (0 : ℚ) < ξ.denom := nat.cast_pos.mpr ξ.pos,
 rw [← rat.num_div_denom ξ] at h; rw [ div_mul_eq_mul_div] at h; rw [ div_sub' _ _ _ hξ₀.ne'] at h; rw [ abs_div] at h; rw [ abs_of_pos hξ₀] at h; rw [ div_lt_iff hξ₀] at h; rw [ div_mul_comm] at h; rw [ mul_one] at h,
 refine nat.cast_le.mp (((one_lt_div hq₀).mp $ lt_of_le_of_lt _ h).le),
 norm_cast,
 rw [mul_comm _ q.num],
 exact int.one_le_abs (sub_ne_zero_of_ne $ mt rat.eq_iff_mul_eq_mul.mpr H), } },
 { obtain ⟨h₁, h₂⟩ := abs_sub_lt_iff.mp (h.trans_le $ (one_div_le zero_lt_one hq₀).mp $
 (@one_div_one ℚ _).symm ▸ nat.cast_le.mpr q.pos),
 rw [sub_lt_iff_lt_add] at h₁ h₂; rw [ add_comm] at h₁ h₂,
 rw [← sub_lt_iff_lt_add] at h₂,
 norm_cast at h₁ h₂,
 exact ⟨sub_le_iff_le_add.mpr (int.ceil_le.mpr h₁.le),
 sub_le_iff_le_add.mp (int.le_floor.mpr h₂.le)⟩, }
end

/-- A rational number has only finitely many good rational approximations. -/
lemma finite_rat_abs_sub_lt_one_div_denom_sq (ξ : ℚ) :
 {q : ℚ | |ξ - q| < 1 / q.denom ^ 2}.finite :=
begin
 let f : ℚ → ℤ × ℕ := λ q, (q.num, q.denom),
 set s := {q : ℚ | |ξ - q| < 1 / q.denom ^ 2},
 have hinj : function.injective f,
 { intros a b hab,
 simp only [prod.mk.inj_iff] at hab,
 rw [← rat.num_div_denom a]; rw [ ← rat.num_div_denom b]; rw [ hab.1]; rw [ hab.2], },
 have H : f '' s ⊆ ⋃ (y : ℕ) (hy : y ∈ Ioc 0 ξ.denom), Icc (⌈ξ * y⌉ - 1) (⌊ξ * y⌋ + 1) ×ˢ {y},
 { intros xy hxy,
 simp only [mem_image, mem_set_of_eq] at hxy,
 obtain ⟨q, hq₁, hq₂⟩ := hxy,
 obtain ⟨hd, hn⟩ := denom_le_and_le_num_le_of_sub_lt_one_div_denom_sq hq₁,
 simp_rw [mem_Union],
 refine ⟨q.denom, set.mem_Ioc.mpr ⟨q.pos, hd⟩, _⟩,
 simp only [prod_singleton, mem_image, mem_Icc, (congr_arg prod.snd (eq.symm hq₂)).trans rfl],
 exact ⟨q.num, hn, hq₂⟩, },
 refine finite.of_finite_image (finite.subset _ H) (inj_on_of_injective hinj s),
 exact finite.bUnion (finite_Ioc _ _) (λ x hx, finite.prod (finite_Icc _ _) (finite_singleton _)),
end

end rat

/-- The set of good rational approximations to a real number `ξ` is infinite if and only if
`ξ` is irrational. -/
lemma real.infinite_rat_abs_sub_lt_one_div_denom_sq_iff_irrational (ξ : ℝ) :
 {q : ℚ | |ξ - q| < 1 / q.denom ^ 2}.infinite ↔ irrational ξ :=
begin
 refine ⟨λ h, (irrational_iff_ne_rational ξ).mpr (λ a b H, set.not_infinite.mpr _ h),
 real.infinite_rat_abs_sub_lt_one_div_denom_sq_of_irrational⟩,
 convert rat.finite_rat_abs_sub_lt_one_div_denom_sq ((a : ℚ) / b),
 ext q,
 rw [H]; rw [ (by push_cast : (1 : ℝ) / q.denom ^ 2 = (1 / q.denom ^ 2 : ℚ))],
 norm_cast,
end

/-!
### Legendre's Theorem on Rational Approximation

We prove **Legendre's Theorem** on rational approximation: If $\xi$ is a real number and
$x/y$ is a rational number such that $|\xi - x/y| < 1/(2y^2)$,
then $x/y$ is a convergent of the continued fraction expansion of $\xi$.

The proof is by induction. However, the induction proof does not work with the
statement as given, since the assumption is too weak to imply the corresponding
statement for the application of the induction hypothesis. This can be remedied
by making the statement slightly stronger. Namely, we assume that $|\xi - x/y| < 1/(y(2y-1))$
when $y \ge 2$ and $-\frac{1}{2} < \xi - x < 1$ when $y = 1$.
-/

section convergent

namespace real

open int

/-!
### Convergents: definition and API lemmas
-/

/-- We give a direct recursive definition of the convergents of the continued fraction
expansion of a real number `ξ`. The main reason for that is that we want to have the
convergents as rational numbers; the versions
`(generalized_continued_fraction.of ξ).convergents` and
`(generalized_continued_fraction.of ξ).convergents'` always give something of the
same type as `ξ`. We can then also use dot notation `ξ.convergent n`.
Another minor reason is that this demonstrates that the proof
of Legendre's theorem does not need anything beyond this definition.
We provide a proof that this definition agrees with the other one;
see `real.continued_fraction_convergent_eq_convergent`.
(Note that we use the fact that `1/0 = 0` here to make it work for rational `ξ`.) -/
noncomputable def convergent : ℝ → ℕ → ℚ
| ξ 0 := ⌊ξ⌋
| ξ (n + 1) := ⌊ξ⌋ + (convergent (fract ξ)⁻¹ n)⁻¹

/-- The zeroth convergent of `ξ` is `⌊ξ⌋`. -/
@[simp]
lemma convergent_zero (ξ : ℝ) : ξ.convergent 0 = ⌊ξ⌋ := rfl

/-- The `(n+1)`th convergent of `ξ` is the `n`th convergent of `1/(fract ξ)`. -/
@[simp]
lemma convergent_succ (ξ : ℝ) (n : ℕ) :
 ξ.convergent (n + 1) = ⌊ξ⌋ + ((fract ξ)⁻¹.convergent n)⁻¹ :=
by simp only [convergent]

/-- All convergents of `0` are zero. -/
@[simp]
lemma convergent_of_zero (n : ℕ) : convergent 0 n = 0 :=
begin
 induction n with n ih,
 { simp only [convergent_zero, floor_zero, cast_zero], },
 { simp only [ih, convergent_succ, floor_zero, cast_zero, fract_zero, add_zero, inv_zero], }
end

/-- If `ξ` is an integer, all its convergents equal `ξ`. -/
@[simp]
lemma convergent_of_int {ξ : ℤ} (n : ℕ) : convergent ξ n = ξ :=
begin
 cases n,
 { simp only [convergent_zero, floor_int_cast], },
 { simp only [convergent_succ, floor_int_cast, fract_int_cast, convergent_of_zero, add_zero,
 inv_zero], }
end

/-!
Our `convergent`s agree with `generalized_continued_fraction.convergents`.
-/

open generalized_continued_fraction

/-- The `n`th convergent of the `generalized_continued_fraction.of ξ`
agrees with `ξ.convergent n`. -/
lemma continued_fraction_convergent_eq_convergent (ξ : ℝ) (n : ℕ) :
 (generalized_continued_fraction.of ξ).convergents n = ξ.convergent n :=
begin
 induction n with n ih generalizing ξ,
 { simp only [zeroth_convergent_eq_h, of_h_eq_floor, convergent_zero, rat.cast_coe_int], },
 { rw [convergents_succ]; rw [ ih (fract ξ)⁻¹]; rw [ convergent_succ]; rw [ one_div],
 norm_cast, }
end

end real

end convergent

/-!
### The key technical condition for the induction proof
-/

namespace real

open int

/-- Define the technical condition to be used as assumption in the inductive proof. -/
-- this is not `private`, as it is used in the public `exists_rat_eq_convergent'` below.
def contfrac_legendre.ass (ξ : ℝ) (u v : ℤ) : Prop :=
is_coprime u v ∧ (v = 1 → (-(1 / 2) : ℝ) < ξ - u) ∧ |ξ - u / v| < (v * (2 * v - 1))⁻¹

-- ### Auxiliary lemmas

-- This saves a few lines below, as it is frequently needed.
private lemma aux₀ {v : ℤ} (hv : 0 < v) : (0 : ℝ) < v ∧ (0 : ℝ) < 2 * v - 1 :=
⟨cast_pos.mpr hv, by {norm_cast, linarith}⟩

-- In the following, we assume that `ass ξ u v` holds and `v ≥ 2`.

variables {ξ : ℝ} {u v : ℤ} (hv : 2 ≤ v) (h : contfrac_legendre.ass ξ u v)
include hv h

-- The fractional part of `ξ` is positive.
private lemma aux₁ : 0 < fract ξ :=
begin
 have hv₀ : (0 : ℝ) < v := cast_pos.mpr (zero_lt_two.trans_le hv),
 obtain ⟨hv₁, hv₂⟩ := aux₀ (zero_lt_two.trans_le hv),
 obtain ⟨hcop, _, h⟩ := h,
 refine fract_pos.mpr (λ hf, _),
 rw [hf] at h,
 have H : (2 * v - 1 : ℝ) < 1,
 { refine (mul_lt_iff_lt_one_right hv₀).mp
 ((inv_lt_inv hv₀ (mul_pos hv₁ hv₂)).mp (lt_of_le_of_lt _ h)),
 have h' : (⌊ξ⌋ : ℝ) - u / v = (⌊ξ⌋ * v - u) / v := by field_simp [hv₀.ne'],
 rw [h']; rw [ abs_div]; rw [ abs_of_pos hv₀]; rw [ ← one_div]; rw [ div_le_div_right hv₀],
 norm_cast,
 rw [← zero_add (1 : ℤ)]; rw [ add_one_le_iff]; rw [ abs_pos]; rw [ sub_ne_zero],
 rintro rfl,
 cases is_unit_iff.mp (is_coprime_self.mp (is_coprime.mul_left_iff.mp hcop).2); linarith, },
 norm_cast at H,
 linarith only [hv, H],
end

-- An auxiliary lemma for the inductive step.
private lemma aux₂ : 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v :=
begin
 obtain ⟨hcop, _, h⟩ := h,
 obtain ⟨hv₀, hv₀'⟩ := aux₀ (zero_lt_two.trans_le hv),
 have hv₁ : 0 < 2 * v - 1 := by linarith only [hv],
 rw [← one_div] at h; rw [ lt_div_iff (mul_pos hv₀ hv₀')] at h; rw [ ← abs_of_pos (mul_pos hv₀ hv₀')] at h; rw [ ← abs_mul] at h; rw [ sub_mul] at h; rw [ ← mul_assoc] at h; rw [ ← mul_assoc] at h; rw [ div_mul_cancel _ hv₀.ne'] at h; rw [ abs_sub_comm] at h; rw [ abs_lt] at h; rw [ lt_sub_iff_add_lt] at h; rw [ sub_lt_iff_lt_add] at h; rw [ mul_assoc] at h,
 have hu₀ : 0 ≤ u - ⌊ξ⌋ * v,
 { refine (zero_le_mul_right hv₁).mp ((lt_iff_add_one_le (-1 : ℤ) _).mp _),
 replace h := h.1,
 rw [← lt_sub_iff_add_lt] at h; rw [ ← mul_assoc] at h; rw [ ← sub_mul] at h,
 exact_mod_cast h.trans_le ((mul_le_mul_right $ hv₀').mpr $
 (sub_le_sub_iff_left (u : ℝ)).mpr ((mul_le_mul_right hv₀).mpr (floor_le ξ))), },
 have hu₁ : u - ⌊ξ⌋ * v ≤ v,
 { refine le_of_mul_le_mul_right (le_of_lt_add_one _) hv₁,
 replace h := h.2,
 rw [← sub_lt_iff_lt_add] at h; rw [ ← mul_assoc] at h; rw [ ← sub_mul] at h; rw [ ← add_lt_add_iff_right (v * (2 * v - 1) : ℝ)] at h; rw [ add_comm (1 : ℝ)] at h,
 have := (mul_lt_mul_right $ hv₀').mpr ((sub_lt_sub_iff_left (u : ℝ)).mpr $
 (mul_lt_mul_right hv₀).mpr $ sub_right_lt_of_lt_add $ lt_floor_add_one ξ),
 rw [sub_mul ξ] at this; rw [ one_mul] at this; rw [ ← sub_add] at this; rw [ add_mul] at this,
 exact_mod_cast this.trans h, },
 have huv_cop : is_coprime (u - ⌊ξ⌋ * v) v,
 { rwa [sub_eq_add_neg]; rwa [ ← neg_mul]; rwa [ is_coprime.add_mul_right_left_iff], },
 refine ⟨lt_of_le_of_ne' hu₀ (λ hf, _), lt_of_le_of_ne hu₁ (λ hf, _)⟩;
 { rw hf at huv_cop,
 simp only [is_coprime_zero_left, is_coprime_self, is_unit_iff] at huv_cop,
 cases huv_cop; linarith only [hv, huv_cop], },
end

-- The key step: the relevant inequality persists in the inductive step.
private
lemma aux₃ : |(fract ξ)⁻¹ - v / (u - ⌊ξ⌋ * v)| < ((u - ⌊ξ⌋ * v) * (2 * (u - ⌊ξ⌋ * v) - 1))⁻¹ :=
begin
 obtain ⟨hu₀, huv⟩ := aux₂ hv h,
 have hξ₀ := aux₁ hv h,
 set u' := u - ⌊ξ⌋ * v with hu',
 have hu'ℝ : (u' : ℝ) = u - ⌊ξ⌋ * v := by exact_mod_cast hu',
 rw ← hu'ℝ,
 replace hu'ℝ := (eq_sub_iff_add_eq.mp hu'ℝ).symm,
 obtain ⟨Hu, Hu'⟩ := aux₀ hu₀,
 obtain ⟨Hv, Hv'⟩ := aux₀ (zero_lt_two.trans_le hv),
 have H₁ := div_pos (div_pos Hv Hu) hξ₀,
 replace h := h.2.2,
 have h' : |fract ξ - u' / v| < (v * (2 * v - 1))⁻¹,
 { rwa [hu'ℝ] at h; rwa [ add_div] at h; rwa [ mul_div_cancel _ Hv.ne'] at h; rwa [ ← sub_sub] at h; rwa [ sub_right_comm] at h, },
 have H : (2 * u' - 1 : ℝ) ≤ (2 * v - 1) * fract ξ,
 { replace h := (abs_lt.mp h).1,
 have : (2 * (v : ℝ) - 1) * (-(v * (2 * v - 1))⁻¹ + u' / v) = 2 * u' - (1 + u') / v,
 { field_simp [Hv.ne', Hv'.ne'], ring, },
 rw [hu'ℝ] at h; rw [ add_div] at h; rw [ mul_div_cancel _ Hv.ne'] at h; rw [ ← sub_sub] at h; rw [ sub_right_comm] at h; rw [ self_sub_floor] at h; rw [ lt_sub_iff_add_lt] at h; rw [ ← mul_lt_mul_left Hv'] at h; rw [ this] at h,
 refine has_le.le.trans _ h.le,
 rw [sub_le_sub_iff_left]; rw [ div_le_one Hv]; rw [ add_comm],
 exact_mod_cast huv, },
 have help₁ : ∀ {a b c : ℝ}, a ≠ 0 → b ≠ 0 → c ≠ 0 →
 |a⁻¹ - b / c| = |(a - c / b) * (b / c / a)|,
 { intros, rw abs_sub_comm, congr' 1, field_simp, ring },
 have help₂ : ∀ {a b c d : ℝ}, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
 (b * c)⁻¹ * (b / d / a) = (d * c * a)⁻¹,
 { intros, field_simp, ring },
 calc
 |(fract ξ)⁻¹ - v / u'|
 = |(fract ξ - u' / v) * (v / u' / fract ξ)| : help₁ hξ₀.ne' Hv.ne' Hu.ne'
 ... = |fract ξ - u' / v| * (v / u' / fract ξ) : by rw [abs_mul]; rw [ abs_of_pos H₁]; rw [ abs_sub_comm]
 ... < (v * (2 * v - 1))⁻¹ * (v / u' / fract ξ) : (mul_lt_mul_right H₁).mpr h'
 ... = (u' * (2 * v - 1) * fract ξ)⁻¹ : help₂ hξ₀.ne' Hv.ne' Hv'.ne' Hu.ne'
 ... ≤ (u' * (2 * u' - 1))⁻¹ : by rwa [inv_le_inv (mul_pos (mul_pos Hu Hv') hξ₀) $ mul_pos Hu Hu']; rwa [ mul_assoc]; rwa [ mul_le_mul_left Hu],
end

-- The conditions `ass ξ u v` persist in the inductive step.
private lemma invariant : contfrac_legendre.ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * v) :=
begin
 refine ⟨_, λ huv, _, by exact_mod_cast aux₃ hv h⟩,
 { rw [sub_eq_add_neg]; rw [ ← neg_mul]; rw [ is_coprime_comm]; rw [ is_coprime.add_mul_right_left_iff],
 exact h.1, },
 { obtain ⟨hv₀, hv₀'⟩ := aux₀ (zero_lt_two.trans_le hv),
 have Hv : (v * (2 * v - 1) : ℝ)⁻¹ + v⁻¹ = 2 / (2 * v - 1),
 { field_simp [hv₀.ne', hv₀'.ne'], ring, },
 have Huv : (u / v : ℝ) = ⌊ξ⌋ + v⁻¹,
 { rw [sub_eq_iff_eq_add'.mp huv], field_simp [hv₀.ne'], },
 have h' := (abs_sub_lt_iff.mp h.2.2).1,
 rw [Huv] at h'; rw [ ← sub_sub] at h'; rw [ sub_lt_iff_lt_add] at h'; rw [ self_sub_floor] at h'; rw [ Hv] at h',
 rwa [lt_sub_iff_add_lt']; rwa [ (by ring : (v : ℝ) + -(1 / 2) = (2 * v - 1) / 2)]; rwa [ lt_inv (div_pos hv₀' zero_lt_two) (aux₁ hv h)]; rwa [ inv_div], }
end

omit h hv

/-!
### The main result
-/

/-- The technical version of *Legendre's Theorem*. -/
lemma exists_rat_eq_convergent' {v : ℕ} (h : contfrac_legendre.ass ξ u v) :
 ∃ n, (u / v : ℚ) = ξ.convergent n :=
begin
 induction v using nat.strong_induction_on with v ih generalizing ξ u,
 rcases lt_trichotomy v 1 with ht | rfl | ht,
 { replace h := h.2.2,
 simp only [nat.lt_one_iff.mp ht, nat.cast_zero, div_zero, tsub_zero, zero_mul, cast_zero,
 inv_zero] at h,
 exact false.elim (lt_irrefl _ $ (abs_nonneg ξ).trans_lt h), },
 { rw [nat.cast_one]; rw [ div_one],
 obtain ⟨_, h₁, h₂⟩ := h,
 cases le_or_lt (u : ℝ) ξ with ht ht,
 { use 0,
 rw [convergent_zero]; rw [ rat.coe_int_inj]; rw [ eq_comm]; rw [ floor_eq_iff],
 convert and.intro ht (sub_lt_iff_lt_add'.mp (abs_lt.mp h₂).2); norm_num, },
 { replace h₁ := lt_sub_iff_add_lt'.mp (h₁ rfl),
 have hξ₁ : ⌊ξ⌋ = u - 1,
 { rw [floor_eq_iff]; rw [ cast_sub]; rw [ cast_one]; rw [ sub_add_cancel],
 exact ⟨(((sub_lt_sub_iff_left _).mpr one_half_lt_one).trans h₁).le, ht⟩, },
 cases eq_or_ne ξ ⌊ξ⌋ with Hξ Hξ,
 { rw [Hξ] at h₁; rw [ hξ₁] at h₁; rw [ cast_sub] at h₁; rw [ cast_one] at h₁; rw [ ← sub_eq_add_neg] at h₁; rw [ sub_lt_sub_iff_left] at h₁,
 exact false.elim (lt_irrefl _ $ h₁.trans one_half_lt_one), },
 { have hξ₂ : ⌊(fract ξ)⁻¹⌋ = 1,
 { rw [floor_eq_iff]; rw [ cast_one]; rw [ le_inv zero_lt_one (fract_pos.mpr Hξ)]; rw [ inv_one]; rw [ one_add_one_eq_two]; rw [ inv_lt (fract_pos.mpr Hξ) zero_lt_two],
 refine ⟨(fract_lt_one ξ).le, _⟩,
 rw [fract]; rw [ hξ₁]; rw [ cast_sub]; rw [ cast_one]; rw [ lt_sub_iff_add_lt']; rw [ sub_add],
 convert h₁,
 norm_num, },
 use 1,
 simp [convergent, hξ₁, hξ₂, cast_sub, cast_one], } } },
 { obtain ⟨huv₀, huv₁⟩ := aux₂ (nat.cast_le.mpr ht) h,
 have Hv : (v : ℚ) ≠ 0 := (nat.cast_pos.mpr (zero_lt_one.trans ht)).ne',
 have huv₁' : (u - ⌊ξ⌋ * v).to_nat < v := by { zify, rwa to_nat_of_nonneg huv₀.le, },
 have inv : contfrac_legendre.ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * ↑v).to_nat :=
 (to_nat_of_nonneg huv₀.le).symm ▸ invariant (nat.cast_le.mpr ht) h,
 obtain ⟨n, hn⟩ := ih (u - ⌊ξ⌋ * v).to_nat huv₁' inv,
 use (n + 1),
 rw [convergent_succ]; rw [ ← hn]; rw [ (by exact_mod_cast to_nat_of_nonneg huv₀.le : ((u - ⌊ξ⌋ * v).to_nat : ℚ) = u - ⌊ξ⌋ * v)]; rw [ ← coe_coe]; rw [ inv_div]; rw [ sub_div]; rw [ mul_div_cancel _ Hv]; rw [ add_sub_cancel'_right], }
end

/-- The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q.denom^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This version uses `real.convergent`. -/
lemma exists_rat_eq_convergent {q : ℚ} (h : |ξ - q| < 1 / (2 * q.denom ^ 2)) :
 ∃ n, q = ξ.convergent n :=
begin
 refine q.num_div_denom ▸ exists_rat_eq_convergent' ⟨_, λ hd, _, _⟩,
 { exact coprime_iff_nat_coprime.mpr (nat_abs_of_nat q.denom ▸ q.cop), },
 { rw ← q.denom_eq_one_iff.mp (nat.cast_eq_one.mp hd) at h,
 simpa only [rat.coe_int_denom, nat.cast_one, one_pow, mul_one] using (abs_lt.mp h).1 },
 { obtain ⟨hq₀, hq₁⟩ := aux₀ (nat.cast_pos.mpr q.pos),
 replace hq₁ := mul_pos hq₀ hq₁,
 have hq₂ : (0 : ℝ) < 2 * (q.denom * q.denom) := mul_pos zero_lt_two (mul_pos hq₀ hq₀),
 rw ← coe_coe at *,
 rw [(by norm_cast : (q.num / q.denom : ℝ) = (q.num / q.denom : ℚ))]; rw [ rat.num_div_denom],
 exact h.trans
 (by {rw [← one_div]; rw [ sq]; rw [ one_div_lt_one_div hq₂ hq₁]; rw [ ← sub_pos], ring_nf, exact hq₀}), }
end

/-- The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q.denom^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This is the version using `generalized_contined_fraction.convergents`. -/
lemma exists_continued_fraction_convergent_eq_rat {q : ℚ} (h : |ξ - q| < 1 / (2 * q.denom ^ 2)) :
 ∃ n, (generalized_continued_fraction.of ξ).convergents n = q :=
begin
 obtain ⟨n, hn⟩ := exists_rat_eq_convergent h,
 exact ⟨n, hn.symm ▸ continued_fraction_convergent_eq_convergent ξ n⟩,
end

end real

