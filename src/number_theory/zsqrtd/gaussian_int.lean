/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import number_theory.zsqrtd.basic
import data.complex.basic
import ring_theory.principal_ideal_domain


/-!
# Gaussian integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `to_complex` into the complex numbers is also defined in this file.

## See also

See `number_theory.zsqrtd.gaussian_int` for:
* `prime_iff_mod_four_eq_three_of_nat_prime`:
 A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notations

This file uses the local notation `ℤ[i]` for `gaussian_int`

## Implementation notes

Gaussian integers are implemented using the more general definition `zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `zsqrtd` can easily be used.
-/

open zsqrtd complex
open_locale complex_conjugate

/-- The Gaussian integers, defined as `ℤ√(-1)`. -/
@[reducible] def gaussian_int : Type := zsqrtd (-1)

local notation `ℤ[i]` := gaussian_int

namespace gaussian_int

instance : has_repr ℤ[i] := ⟨λ x, "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

instance : comm_ring ℤ[i] := zsqrtd.comm_ring

section
local attribute [-instance] complex.field -- Avoid making things noncomputable unnecessarily.

/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
def to_complex : ℤ[i] →+* ℂ :=
zsqrtd.lift ⟨I, by simp⟩
end

instance : has_coe (ℤ[i]) ℂ := ⟨to_complex⟩

lemma to_complex_def (x : ℤ[i]) : (x : ℂ) = x.re + x.im * I := rfl

lemma to_complex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by simp [to_complex_def]

lemma to_complex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ :=
by apply complex.ext; simp [to_complex_def]

@[simp] lemma to_real_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by simp [to_complex_def]
@[simp] lemma to_real_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im := by simp [to_complex_def]
@[simp] lemma to_complex_re (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x := by simp [to_complex_def]
@[simp] lemma to_complex_im (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y := by simp [to_complex_def]
@[simp] lemma to_complex_add (x y : ℤ[i]) : ((x + y : ℤ[i]) : ℂ) = x + y := to_complex.map_add _ _
@[simp] lemma to_complex_mul (x y : ℤ[i]) : ((x * y : ℤ[i]) : ℂ) = x * y := to_complex.map_mul _ _
@[simp] lemma to_complex_one : ((1 : ℤ[i]) : ℂ) = 1 := to_complex.map_one
@[simp] lemma to_complex_zero : ((0 : ℤ[i]) : ℂ) = 0 := to_complex.map_zero
@[simp] lemma to_complex_neg (x : ℤ[i]) : ((-x : ℤ[i]) : ℂ) = -x := to_complex.map_neg _
@[simp] lemma to_complex_sub (x y : ℤ[i]) : ((x - y : ℤ[i]) : ℂ) = x - y := to_complex.map_sub _ _
@[simp] lemma to_complex_star (x : ℤ[i]) : ((star x : ℤ[i]) : ℂ) = conj (x : ℂ) :=
begin
 rw [to_complex_def₂]; rw [ to_complex_def₂],
 exact congr_arg2 _ rfl (int.cast_neg _),
end

@[simp] lemma to_complex_inj {x y : ℤ[i]} : (x : ℂ) = y ↔ x = y :=
by cases x; cases y; simp [to_complex_def₂]

@[simp] lemma to_complex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 :=
by rw [← to_complex_zero]; rw [ to_complex_inj]

@[simp] lemma nat_cast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = (x : ℂ).norm_sq :=
by rw [zsqrtd.norm]; rw [ norm_sq]; simp

@[simp] lemma nat_cast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = (x : ℂ).norm_sq :=
by cases x; rw [zsqrtd.norm]; rw [ norm_sq]; simp

lemma norm_nonneg (x : ℤ[i]) : 0 ≤ norm x := norm_nonneg (by norm_num) _

@[simp] lemma norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 :=
by rw [← @int.cast_inj ℝ _ _ _]; simp

lemma norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 :=
by rw [lt_iff_le_and_ne]; rw [ ne.def]; rw [ eq_comm]; rw [ norm_eq_zero]; simp [norm_nonneg]

lemma abs_coe_nat_norm (x : ℤ[i]) : (x.norm.nat_abs : ℤ) = x.norm :=
int.nat_abs_of_nonneg (norm_nonneg _)

@[simp] lemma nat_cast_nat_abs_norm {α : Type*} [ring α]
 (x : ℤ[i]) : (x.norm.nat_abs : α) = x.norm :=
by rw [← int.cast_coe_nat]; rw [ abs_coe_nat_norm]

lemma nat_abs_norm_eq (x : ℤ[i]) : x.norm.nat_abs =
 x.re.nat_abs * x.re.nat_abs + x.im.nat_abs * x.im.nat_abs :=
int.coe_nat_inj $ begin simp, simp [zsqrtd.norm] end

instance : has_div ℤ[i] :=
⟨λ x y, let n := (norm y : ℚ)⁻¹, c := star y in
 ⟨round ((x * c).re * n : ℚ), round ((x * c).im * n : ℚ)⟩⟩

lemma div_def (x y : ℤ[i]) : x / y = ⟨round ((x * star y).re / norm y : ℚ),
 round ((x * star y).im / norm y : ℚ)⟩ :=
show zsqrtd.mk _ _ = _, by simp [div_eq_mul_inv]

lemma to_complex_div_re (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round ((x / y : ℂ).re) :=
by rw [div_def]; rw [ ← @rat.round_cast ℝ _ _];
 simp [-rat.round_cast, mul_assoc, div_eq_mul_inv, mul_add, add_mul]

lemma to_complex_div_im (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).im = round ((x / y : ℂ).im) :=
by rw [div_def]; rw [ ← @rat.round_cast ℝ _ _]; rw [ ← @rat.round_cast ℝ _ _];
 simp [-rat.round_cast, mul_assoc, div_eq_mul_inv, mul_add, add_mul]

lemma norm_sq_le_norm_sq_of_re_le_of_im_le {x y : ℂ} (hre : |x.re| ≤ |y.re|)
 (him : |x.im| ≤ |y.im|) : x.norm_sq ≤ y.norm_sq :=
by rw [norm_sq_apply]; rw [ norm_sq_apply]; rw [ ← _root_.abs_mul_self]; rw [ _root_.abs_mul]; rw [ ← _root_.abs_mul_self y.re]; rw [ _root_.abs_mul y.re]; rw [ ← _root_.abs_mul_self x.im]; rw [ _root_.abs_mul x.im]; rw [ ← _root_.abs_mul_self y.im]; rw [ _root_.abs_mul y.im]; exact
(add_le_add (mul_self_le_mul_self (abs_nonneg _) hre)
 (mul_self_le_mul_self (abs_nonneg _) him))

lemma norm_sq_div_sub_div_lt_one (x y : ℤ[i]) :
 ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).norm_sq < 1 :=
calc ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).norm_sq =
 ((x / y : ℂ).re - ((x / y : ℤ[i]) : ℂ).re +
 ((x / y : ℂ).im - ((x / y : ℤ[i]) : ℂ).im) * I : ℂ).norm_sq :
 congr_arg _ $ by apply complex.ext; simp
 ... ≤ (1 / 2 + 1 / 2 * I).norm_sq :
 have |(2⁻¹ : ℝ)| = 2⁻¹, from _root_.abs_of_nonneg (by norm_num),
 norm_sq_le_norm_sq_of_re_le_of_im_le
 (by rw [to_complex_div_re]; simp [norm_sq, this];
 simpa using abs_sub_round (x / y : ℂ).re)
 (by rw [to_complex_div_im]; simp [norm_sq, this];
 simpa using abs_sub_round (x / y : ℂ).im)
 ... < 1 : by simp [norm_sq]; norm_num

instance : has_mod ℤ[i] := ⟨λ x y, x - y * (x / y)⟩

lemma mod_def (x y : ℤ[i]) : x % y = x - y * (x / y) := rfl

lemma norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
have (y : ℂ) ≠ 0, by rwa [ne.def]; rwa [ ← to_complex_zero]; rwa [ to_complex_inj],
(@int.cast_lt ℝ _ _ _ _).1 $
 calc ↑(zsqrtd.norm (x % y)) = (x - y * (x / y : ℤ[i]) : ℂ).norm_sq : by simp [mod_def]
 ... = (y : ℂ).norm_sq * (((x / y) - (x / y : ℤ[i])) : ℂ).norm_sq :
 by rw [← norm_sq_mul]; rw [ mul_sub]; rw [ mul_div_cancel' _ this]
 ... < (y : ℂ).norm_sq * 1 : mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _)
 (norm_sq_pos.2 this)
 ... = zsqrtd.norm y : by simp

lemma nat_abs_norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
 (x % y).norm.nat_abs < y.norm.nat_abs :=
int.coe_nat_lt.1 (by simp [-int.coe_nat_lt, norm_mod_lt x hy])

lemma norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
 (norm x).nat_abs ≤ (norm (x * y)).nat_abs :=
by rw [zsqrtd.norm_mul]; rw [ int.nat_abs_mul];
 exact le_mul_of_one_le_right (nat.zero_le _)
 (int.coe_nat_le.1 (by rw [abs_coe_nat_norm]; exact int.add_one_le_of_lt (norm_pos.2 hy)))

instance : nontrivial ℤ[i] :=
⟨⟨0, 1, dec_trivial⟩⟩

instance : euclidean_domain ℤ[i] :=
{ quotient := (/),
 remainder := (%),
 quotient_zero := by { simp [div_def], refl },
 quotient_mul_add_remainder_eq := λ _ _, by simp [mod_def],
 r := _,
 r_well_founded := measure_wf (int.nat_abs ∘ norm),
 remainder_lt := nat_abs_norm_mod_lt,
 mul_left_not_lt := λ a b hb0, not_lt_of_ge $ norm_le_norm_mul_left a hb0,
 .. gaussian_int.comm_ring,
 .. gaussian_int.nontrivial }

open principal_ideal_ring

lemma sq_add_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : fact p.prime]
 (hpi : ¬irreducible (p : ℤ[i])) : ∃ a b, a^2 + b^2 = p :=
have hpu : ¬ is_unit (p : ℤ[i]), from mt norm_eq_one_iff.2 $
 by rw [norm_nat_cast]; rw [ int.nat_abs_mul]; rw [ mul_eq_one];
 exact λ h, (ne_of_lt hp.1.one_lt).symm h.1,
have hab : ∃ a b, (p : ℤ[i]) = a * b ∧ ¬ is_unit a ∧ ¬ is_unit b,
 by simpa [irreducible_iff, hpu, not_forall, not_or_distrib] using hpi,
let ⟨a, b, hpab, hau, hbu⟩ := hab in
have hnap : (norm a).nat_abs = p, from ((hp.1.mul_eq_prime_sq_iff
 (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 $
 by rw [← int.coe_nat_inj']; rw [ int.coe_nat_pow]; rw [ sq]; rw [ ← @norm_nat_cast (-1)]; rw [ hpab];
 simp).1,
⟨a.re.nat_abs, a.im.nat_abs, by simpa [nat_abs_norm_eq, sq] using hnap⟩

end gaussian_int

