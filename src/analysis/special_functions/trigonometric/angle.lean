/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import analysis.special_functions.trigonometric.basic
import analysis.normed.group.add_circle
import algebra.char_zero.quotient
import topology.instances.sign

/-!
# The type of angles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `real.angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/

open_locale real

noncomputable theory

namespace real

/-- The type of angles -/
@[derive [normed_add_comm_group, inhabited, has_coe_t ℝ]]
def angle : Type := add_circle (2 * π)

namespace angle

instance : circular_order real.angle :=
@add_circle.circular_order _ _ _ _ _ ⟨by norm_num [pi_pos]⟩ _

@[continuity] lemma continuous_coe : continuous (coe : ℝ → angle) :=
continuous_quotient_mk

/-- Coercion `ℝ → angle` as an additive homomorphism. -/
def coe_hom : ℝ →+ angle := quotient_add_group.mk' _

@[simp] lemma coe_coe_hom : (coe_hom : ℝ → angle) = coe := rfl

/-- An induction principle to deduce results for `angle` from those for `ℝ`, used with
`induction θ using real.angle.induction_on`. -/
@[elab_as_eliminator]
protected lemma induction_on {p : angle → Prop} (θ : angle) (h : ∀ x : ℝ, p x) : p θ :=
quotient.induction_on' θ h

@[simp] lemma coe_zero : ↑(0 : ℝ) = (0 : angle) := rfl
@[simp] lemma coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : angle) := rfl
@[simp] lemma coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : angle) := rfl
@[simp] lemma coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : angle) := rfl
lemma coe_nsmul (n : ℕ) (x : ℝ) : ↑(n • x : ℝ) = (n • ↑x : angle) := rfl
lemma coe_zsmul (z : ℤ) (x : ℝ) : ↑(z • x : ℝ) = (z • ↑x : angle) := rfl

@[simp, norm_cast] lemma coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) :
 ↑((n : ℝ) * x) = n • (↑x : angle) :=
by simpa only [nsmul_eq_mul] using coe_hom.map_nsmul x n

@[simp, norm_cast] lemma coe_int_mul_eq_zsmul (x : ℝ) (n : ℤ) :
 ↑((n : ℝ) * x : ℝ) = n • (↑x : angle) :=
by simpa only [zsmul_eq_mul] using coe_hom.map_zsmul x n

lemma angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k :=
by simp only [quotient_add_group.eq, add_subgroup.zmultiples_eq_closure,
 add_subgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

@[simp] lemma coe_two_pi : ↑(2 * π : ℝ) = (0 : angle) :=
angle_eq_iff_two_pi_dvd_sub.2 ⟨1, by rw [sub_zero]; rw [ int.cast_one]; rw [ mul_one]⟩

@[simp] lemma neg_coe_pi : -(π : angle) = π :=
begin
 rw [←coe_neg]; rw [ angle_eq_iff_two_pi_dvd_sub],
 use -1,
 simp [two_mul, sub_eq_add_neg]
end

@[simp] lemma two_nsmul_coe_div_two (θ : ℝ) : (2 : ℕ) • (↑(θ / 2) : angle) = θ :=
by rw [←coe_nsmul]; rw [ two_nsmul]; rw [ add_halves]

@[simp] lemma two_zsmul_coe_div_two (θ : ℝ) : (2 : ℤ) • (↑(θ / 2) : angle) = θ :=
by rw [←coe_zsmul]; rw [ two_zsmul]; rw [ add_halves]

@[simp] lemma two_nsmul_neg_pi_div_two : (2 : ℕ) • (↑(-π / 2) : angle) = π :=
by rw [two_nsmul_coe_div_two]; rw [ coe_neg]; rw [ neg_coe_pi]

@[simp] lemma two_zsmul_neg_pi_div_two : (2 : ℤ) • (↑(-π / 2) : angle) = π :=
by rw [two_zsmul]; rw [ ←two_nsmul]; rw [ two_nsmul_neg_pi_div_two]

lemma sub_coe_pi_eq_add_coe_pi (θ : angle) : θ - π = θ + π :=
by rw [sub_eq_add_neg]; rw [ neg_coe_pi]

@[simp] lemma two_nsmul_coe_pi : (2 : ℕ) • (π : angle) = 0 :=
by simp [←coe_nat_mul_eq_nsmul]

@[simp] lemma two_zsmul_coe_pi : (2 : ℤ) • (π : angle) = 0 :=
by simp [←coe_int_mul_eq_zsmul]

@[simp] lemma coe_pi_add_coe_pi : (π : real.angle) + π = 0 :=
by rw [←two_nsmul]; rw [ two_nsmul_coe_pi]

lemma zsmul_eq_iff {ψ θ : angle} {z : ℤ} (hz : z ≠ 0) :
 z • ψ = z • θ ↔ (∃ k : fin z.nat_abs, ψ = θ + (k : ℕ) • (2 * π / z : ℝ)) :=
quotient_add_group.zmultiples_zsmul_eq_zsmul_iff hz

lemma nsmul_eq_iff {ψ θ : angle} {n : ℕ} (hz : n ≠ 0) :
 n • ψ = n • θ ↔ (∃ k : fin n, ψ = θ + (k : ℕ) • (2 * π / n : ℝ)) :=
quotient_add_group.zmultiples_nsmul_eq_nsmul_iff hz

lemma two_zsmul_eq_iff {ψ θ : angle} : (2 : ℤ) • ψ = (2 : ℤ) • θ ↔ (ψ = θ ∨ ψ = θ + π) :=
by rw [zsmul_eq_iff two_ne_zero]; rw [ int.nat_abs_bit0]; rw [ int.nat_abs_one]; rw [ fin.exists_fin_two]; rw [ fin.coe_zero]; rw [ fin.coe_one]; rw [ zero_smul]; rw [ add_zero]; rw [ one_smul]; rw [ int.cast_two]; rw [ mul_div_cancel_left (_ : ℝ) two_ne_zero]

lemma two_nsmul_eq_iff {ψ θ : angle} : (2 : ℕ) • ψ = (2 : ℕ) • θ ↔ (ψ = θ ∨ ψ = θ + π) :=
by simp_rw [←coe_nat_zsmul, int.coe_nat_bit0, int.coe_nat_one, two_zsmul_eq_iff]

lemma two_nsmul_eq_zero_iff {θ : angle} : (2 : ℕ) • θ = 0 ↔ (θ = 0 ∨ θ = π) :=
by convert two_nsmul_eq_iff; simp

lemma two_nsmul_ne_zero_iff {θ : angle} : (2 : ℕ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib]; rw [ ←two_nsmul_eq_zero_iff]

lemma two_zsmul_eq_zero_iff {θ : angle} : (2 : ℤ) • θ = 0 ↔ (θ = 0 ∨ θ = π) :=
by simp_rw [two_zsmul, ←two_nsmul, two_nsmul_eq_zero_iff]

lemma two_zsmul_ne_zero_iff {θ : angle} : (2 : ℤ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib]; rw [ ←two_zsmul_eq_zero_iff]

lemma eq_neg_self_iff {θ : angle} : θ = -θ ↔ θ = 0 ∨ θ = π :=
by rw [←add_eq_zero_iff_eq_neg]; rw [ ←two_nsmul]; rw [ two_nsmul_eq_zero_iff]

lemma ne_neg_self_iff {θ : angle} : θ ≠ -θ ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib]; rw [ ←eq_neg_self_iff.not]

lemma neg_eq_self_iff {θ : angle} : -θ = θ ↔ θ = 0 ∨ θ = π :=
by rw [eq_comm]; rw [ eq_neg_self_iff]

lemma neg_ne_self_iff {θ : angle} : -θ ≠ θ ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib]; rw [ ←neg_eq_self_iff.not]

lemma two_nsmul_eq_pi_iff {θ : angle} : (2 : ℕ) • θ = π ↔ (θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)) :=
begin
 have h : (π : angle) = (2 : ℕ) • (π / 2 : ℝ), { rw [two_nsmul]; rw [ ←coe_add]; rw [ add_halves] },
 nth_rewrite 0 h,
 rw [two_nsmul_eq_iff],
 congr',
 rw [add_comm]; rw [ ←coe_add]; rw [ ←sub_eq_zero]; rw [ ←coe_sub]; rw [ add_sub_assoc]; rw [ neg_div]; rw [ sub_neg_eq_add]; rw [ add_halves]; rw [ ←two_mul]; rw [ coe_two_pi]
end

lemma two_zsmul_eq_pi_iff {θ : angle} : (2 : ℤ) • θ = π ↔ (θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)) :=
by rw [two_zsmul]; rw [ ←two_nsmul]; rw [ two_nsmul_eq_pi_iff]

theorem cos_eq_iff_coe_eq_or_eq_neg {θ ψ : ℝ} :
 cos θ = cos ψ ↔ (θ : angle) = ψ ∨ (θ : angle) = -ψ :=
begin
 split,
 { intro Hcos,
 rw [← sub_eq_zero] at Hcos; rw [ cos_sub_cos] at Hcos; rw [ mul_eq_zero] at Hcos; rw [ mul_eq_zero] at Hcos; rw [ neg_eq_zero] at Hcos; rw [ eq_false_intro (two_ne_zero' ℝ)] at Hcos; rw [ false_or] at Hcos; rw [ sin_eq_zero_iff] at Hcos; rw [ sin_eq_zero_iff] at Hcos,
 rcases Hcos with ⟨n, hn⟩ | ⟨n, hn⟩,
 { right,
 rw [eq_div_iff_mul_eq (two_ne_zero' ℝ)] at hn; rw [ ← sub_eq_iff_eq_add] at hn,
 rw [← hn]; rw [ coe_sub]; rw [ eq_neg_iff_add_eq_zero]; rw [ sub_add_cancel]; rw [ mul_assoc]; rw [ coe_int_mul_eq_zsmul]; rw [ mul_comm]; rw [ coe_two_pi]; rw [ zsmul_zero] },
 { left,
 rw [eq_div_iff_mul_eq (two_ne_zero' ℝ)] at hn; rw [ eq_sub_iff_add_eq] at hn,
 rw [← hn]; rw [ coe_add]; rw [ mul_assoc]; rw [ coe_int_mul_eq_zsmul]; rw [ mul_comm]; rw [ coe_two_pi]; rw [ zsmul_zero]; rw [ zero_add] }, },
 { rw [angle_eq_iff_two_pi_dvd_sub]; rw [ ← coe_neg]; rw [ angle_eq_iff_two_pi_dvd_sub],
 rintro (⟨k, H⟩ | ⟨k, H⟩),
 rw [← sub_eq_zero]; rw [ cos_sub_cos]; rw [ H]; rw [ mul_assoc 2 π k]; rw [ mul_div_cancel_left _ (two_ne_zero' ℝ)]; rw [ mul_comm π _]; rw [ sin_int_mul_pi]; rw [ mul_zero],
 rw [← sub_eq_zero]; rw [ cos_sub_cos]; rw [ ← sub_neg_eq_add]; rw [ H]; rw [ mul_assoc 2 π k]; rw [ mul_div_cancel_left _ (two_ne_zero' ℝ)]; rw [ mul_comm π _]; rw [ sin_int_mul_pi]; rw [ mul_zero]; rw [ zero_mul] }
end

theorem sin_eq_iff_coe_eq_or_add_eq_pi {θ ψ : ℝ} :
 sin θ = sin ψ ↔ (θ : angle) = ψ ∨ (θ : angle) + ψ = π :=
begin
 split,
 { intro Hsin, rw [← cos_pi_div_two_sub] at Hsin; rw [ ← cos_pi_div_two_sub] at Hsin,
 cases cos_eq_iff_coe_eq_or_eq_neg.mp Hsin with h h,
 { left, rw [coe_sub] at h; rw [ coe_sub] at h, exact sub_right_inj.1 h },
 right, rw [coe_sub] at h; rw [ coe_sub] at h; rw [ eq_neg_iff_add_eq_zero] at h; rw [ add_sub] at h; rw [ sub_add_eq_add_sub] at h; rw [ ← coe_add] at h; rw [ add_halves] at h; rw [ sub_sub] at h; rw [ sub_eq_zero] at h,
 exact h.symm },
 { rw [angle_eq_iff_two_pi_dvd_sub]; rw [ ←eq_sub_iff_add_eq]; rw [ ←coe_sub]; rw [ angle_eq_iff_two_pi_dvd_sub],
 rintro (⟨k, H⟩ | ⟨k, H⟩),
 rw [← sub_eq_zero]; rw [ sin_sub_sin]; rw [ H]; rw [ mul_assoc 2 π k]; rw [ mul_div_cancel_left _ (two_ne_zero' ℝ)]; rw [ mul_comm π _]; rw [ sin_int_mul_pi]; rw [ mul_zero]; rw [ zero_mul],
 have H' : θ + ψ = (2 * k) * π + π := by rwa [←sub_add] at H; rwa [ sub_add_eq_add_sub] at H; rwa [ sub_eq_iff_eq_add] at H; rwa [ mul_assoc] at H; rwa [ mul_comm π _] at H; rwa [ ←mul_assoc] at H,
 rw [← sub_eq_zero]; rw [ sin_sub_sin]; rw [ H']; rw [ add_div]; rw [ mul_assoc 2 _ π]; rw [ mul_div_cancel_left _ (two_ne_zero' ℝ)]; rw [ cos_add_pi_div_two]; rw [ sin_int_mul_pi]; rw [ neg_zero]; rw [ mul_zero] }
end

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : angle) = ψ :=
begin
 cases cos_eq_iff_coe_eq_or_eq_neg.mp Hcos with hc hc, { exact hc },
 cases sin_eq_iff_coe_eq_or_add_eq_pi.mp Hsin with hs hs, { exact hs },
 rw [eq_neg_iff_add_eq_zero] at hc; rw [ hs] at hc,
 obtain ⟨n, hn⟩ : ∃ n, n • _ = _ := quotient_add_group.left_rel_apply.mp (quotient.exact' hc),
 rw [← neg_one_mul] at hn; rw [ add_zero] at hn; rw [ ← sub_eq_zero] at hn; rw [ zsmul_eq_mul] at hn; rw [ ← mul_assoc] at hn; rw [ ← sub_mul] at hn; rw [ mul_eq_zero] at hn; rw [ eq_false_intro (ne_of_gt pi_pos)] at hn; rw [ or_false] at hn; rw [ sub_neg_eq_add] at hn; rw [ ← int.cast_zero] at hn; rw [ ← int.cast_one] at hn; rw [ ← int.cast_bit0] at hn; rw [ ← int.cast_mul] at hn; rw [ ← int.cast_add] at hn; rw [ int.cast_inj] at hn,
 have : (n * 2 + 1) % (2:ℤ) = 0 % (2:ℤ) := congr_arg (%(2:ℤ)) hn,
 rw [add_comm] at this; rw [ int.add_mul_mod_self] at this,
 exact absurd this one_ne_zero
end

/-- The sine of a `real.angle`. -/
def sin (θ : angle) : ℝ := sin_periodic.lift θ

@[simp] lemma sin_coe (x : ℝ) : sin (x : angle) = real.sin x :=
rfl

@[continuity] lemma continuous_sin : continuous sin :=
real.continuous_sin.quotient_lift_on' _

/-- The cosine of a `real.angle`. -/
def cos (θ : angle) : ℝ := cos_periodic.lift θ

@[simp] lemma cos_coe (x : ℝ) : cos (x : angle) = real.cos x :=
rfl

@[continuity] lemma continuous_cos : continuous cos :=
real.continuous_cos.quotient_lift_on' _

lemma cos_eq_real_cos_iff_eq_or_eq_neg {θ : angle} {ψ : ℝ} : cos θ = real.cos ψ ↔ θ = ψ ∨ θ = -ψ :=
begin
 induction θ using real.angle.induction_on,
 exact cos_eq_iff_coe_eq_or_eq_neg
end

lemma cos_eq_iff_eq_or_eq_neg {θ ψ : angle} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ :=
begin
 induction ψ using real.angle.induction_on,
 exact cos_eq_real_cos_iff_eq_or_eq_neg
end

lemma sin_eq_real_sin_iff_eq_or_add_eq_pi {θ : angle} {ψ : ℝ} :
 sin θ = real.sin ψ ↔ θ = ψ ∨ θ + ψ = π :=
begin
 induction θ using real.angle.induction_on,
 exact sin_eq_iff_coe_eq_or_add_eq_pi
end

lemma sin_eq_iff_eq_or_add_eq_pi {θ ψ : angle} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π :=
begin
 induction ψ using real.angle.induction_on,
 exact sin_eq_real_sin_iff_eq_or_add_eq_pi
end

@[simp] lemma sin_zero : sin (0 : angle) = 0 :=
by rw [←coe_zero]; rw [ sin_coe]; rw [ real.sin_zero]

@[simp] lemma sin_coe_pi : sin (π : angle) = 0 :=
by rw [sin_coe]; rw [ real.sin_pi]

lemma sin_eq_zero_iff {θ : angle} : sin θ = 0 ↔ θ = 0 ∨ θ = π :=
begin
 nth_rewrite 0 ←sin_zero,
 rw sin_eq_iff_eq_or_add_eq_pi,
 simp
end

lemma sin_ne_zero_iff {θ : angle} : sin θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib]; rw [ ←sin_eq_zero_iff]

@[simp] lemma sin_neg (θ : angle) : sin (-θ) = -sin θ :=
begin
 induction θ using real.angle.induction_on,
 exact real.sin_neg _
end

lemma sin_antiperiodic : function.antiperiodic sin (π : angle) :=
begin
 intro θ,
 induction θ using real.angle.induction_on,
 exact real.sin_antiperiodic θ
end

@[simp] lemma sin_add_pi (θ : angle) : sin (θ + π) = -sin θ :=
sin_antiperiodic θ

@[simp] lemma sin_sub_pi (θ : angle) : sin (θ - π) = -sin θ :=
sin_antiperiodic.sub_eq θ

@[simp] lemma cos_zero : cos (0 : angle) = 1 :=
by rw [←coe_zero]; rw [ cos_coe]; rw [ real.cos_zero]

@[simp] lemma cos_coe_pi : cos (π : angle) = -1 :=
by rw [cos_coe]; rw [ real.cos_pi]

@[simp] lemma cos_neg (θ : angle) : cos (-θ) = cos θ :=
begin
 induction θ using real.angle.induction_on,
 exact real.cos_neg _
end

lemma cos_antiperiodic : function.antiperiodic cos (π : angle) :=
begin
 intro θ,
 induction θ using real.angle.induction_on,
 exact real.cos_antiperiodic θ
end

@[simp] lemma cos_add_pi (θ : angle) : cos (θ + π) = -cos θ :=
cos_antiperiodic θ

@[simp] lemma cos_sub_pi (θ : angle) : cos (θ - π) = -cos θ :=
cos_antiperiodic.sub_eq θ

lemma cos_eq_zero_iff {θ : angle} : cos θ = 0 ↔ (θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)) :=
by rw [← cos_pi_div_two]; rw [ ← cos_coe]; rw [ cos_eq_iff_eq_or_eq_neg]; rw [ ← coe_neg]; rw [ ← neg_div]

lemma sin_add (θ₁ θ₂ : real.angle) : sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * sin θ₂ :=
begin
 induction θ₁ using real.angle.induction_on,
 induction θ₂ using real.angle.induction_on,
 exact real.sin_add θ₁ θ₂
end

lemma cos_add (θ₁ θ₂ : real.angle) : cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂ :=
begin
 induction θ₂ using real.angle.induction_on,
 induction θ₁ using real.angle.induction_on,
 exact real.cos_add θ₁ θ₂,
end

@[simp] lemma cos_sq_add_sin_sq (θ : real.angle) : cos θ ^ 2 + sin θ ^ 2 = 1 :=
begin
 induction θ using real.angle.induction_on,
 exact real.cos_sq_add_sin_sq θ,
end

lemma sin_add_pi_div_two (θ : angle) : sin (θ + ↑(π / 2)) = cos θ :=
begin
 induction θ using real.angle.induction_on,
 exact sin_add_pi_div_two _
end

lemma sin_sub_pi_div_two (θ : angle) : sin (θ - ↑(π / 2)) = -cos θ :=
begin
 induction θ using real.angle.induction_on,
 exact sin_sub_pi_div_two _
end

lemma sin_pi_div_two_sub (θ : angle) : sin (↑(π / 2) - θ) = cos θ :=
begin
 induction θ using real.angle.induction_on,
 exact sin_pi_div_two_sub _
end

lemma cos_add_pi_div_two (θ : angle) : cos (θ + ↑(π / 2)) = -sin θ :=
begin
 induction θ using real.angle.induction_on,
 exact cos_add_pi_div_two _
end

lemma cos_sub_pi_div_two (θ : angle) : cos (θ - ↑(π / 2)) = sin θ :=
begin
 induction θ using real.angle.induction_on,
 exact cos_sub_pi_div_two _
end

lemma cos_pi_div_two_sub (θ : angle) : cos (↑(π / 2) - θ) = sin θ :=
begin
 induction θ using real.angle.induction_on,
 exact cos_pi_div_two_sub _
end

lemma abs_sin_eq_of_two_nsmul_eq {θ ψ : angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
 |sin θ| = |sin ψ| :=
begin
 rw two_nsmul_eq_iff at h,
 rcases h with rfl | rfl,
 { refl },
 { rw [sin_add_pi]; rw [ abs_neg] }
end

lemma abs_sin_eq_of_two_zsmul_eq {θ ψ : angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
 |sin θ| = |sin ψ| :=
begin
 simp_rw [two_zsmul, ←two_nsmul] at h,
 exact abs_sin_eq_of_two_nsmul_eq h
end

lemma abs_cos_eq_of_two_nsmul_eq {θ ψ : angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
 |cos θ| = |cos ψ| :=
begin
 rw two_nsmul_eq_iff at h,
 rcases h with rfl | rfl,
 { refl },
 { rw [cos_add_pi]; rw [ abs_neg] }
end

lemma abs_cos_eq_of_two_zsmul_eq {θ ψ : angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
 |cos θ| = |cos ψ| :=
begin
 simp_rw [two_zsmul, ←two_nsmul] at h,
 exact abs_cos_eq_of_two_nsmul_eq h
end

@[simp] lemma coe_to_Ico_mod (θ ψ : ℝ) : ↑(to_Ico_mod two_pi_pos ψ θ) = (θ : angle) :=
begin
 rw angle_eq_iff_two_pi_dvd_sub,
 refine ⟨-to_Ico_div two_pi_pos ψ θ, _⟩,
 rw [to_Ico_mod_sub_self]; rw [ zsmul_eq_mul]; rw [ mul_comm]
end

@[simp] lemma coe_to_Ioc_mod (θ ψ : ℝ) : ↑(to_Ioc_mod two_pi_pos ψ θ) = (θ : angle) :=
begin
 rw angle_eq_iff_two_pi_dvd_sub,
 refine ⟨-to_Ioc_div two_pi_pos ψ θ, _⟩,
 rw [to_Ioc_mod_sub_self]; rw [ zsmul_eq_mul]; rw [ mul_comm]
end

/-- Convert a `real.angle` to a real number in the interval `Ioc (-π) π`. -/
def to_real (θ : angle) : ℝ :=
(to_Ioc_mod_periodic two_pi_pos (-π)).lift θ

lemma to_real_coe (θ : ℝ) : (θ : angle).to_real = to_Ioc_mod two_pi_pos (-π) θ := rfl

lemma to_real_coe_eq_self_iff {θ : ℝ} : (θ : angle).to_real = θ ↔ -π < θ ∧ θ ≤ π :=
begin
 rw [to_real_coe]; rw [ to_Ioc_mod_eq_self two_pi_pos],
 ring_nf
end

lemma to_real_coe_eq_self_iff_mem_Ioc {θ : ℝ} : (θ : angle).to_real = θ ↔ θ ∈ set.Ioc (-π) π :=
by rw [to_real_coe_eq_self_iff]; rw [ ←set.mem_Ioc]

lemma to_real_injective : function.injective to_real :=
begin
 intros θ ψ h,
 induction θ using real.angle.induction_on,
 induction ψ using real.angle.induction_on,
 simpa [to_real_coe, to_Ioc_mod_eq_to_Ioc_mod, zsmul_eq_mul, mul_comm _ (2 * π),
 ←angle_eq_iff_two_pi_dvd_sub, eq_comm] using h,
end

@[simp] lemma to_real_inj {θ ψ : angle} : θ.to_real = ψ.to_real ↔ θ = ψ :=
to_real_injective.eq_iff

@[simp] lemma coe_to_real (θ : angle): (θ.to_real : angle) = θ :=
begin
 induction θ using real.angle.induction_on,
 exact coe_to_Ioc_mod _ _
end

lemma neg_pi_lt_to_real (θ : angle) : -π < θ.to_real :=
begin
 induction θ using real.angle.induction_on,
 exact left_lt_to_Ioc_mod _ _ _
end

lemma to_real_le_pi (θ : angle) : θ.to_real ≤ π :=
begin
 induction θ using real.angle.induction_on,
 convert to_Ioc_mod_le_right two_pi_pos _ _,
 ring
end

lemma abs_to_real_le_pi (θ : angle) : |θ.to_real| ≤ π :=
abs_le.2 ⟨(neg_pi_lt_to_real _).le, to_real_le_pi _⟩

lemma to_real_mem_Ioc (θ : angle) : θ.to_real ∈ set.Ioc (-π) π :=
⟨neg_pi_lt_to_real _, to_real_le_pi _⟩

@[simp] lemma to_Ioc_mod_to_real (θ : angle): to_Ioc_mod two_pi_pos (-π) θ.to_real = θ.to_real :=
begin
 induction θ using real.angle.induction_on,
 rw to_real_coe,
 exact to_Ioc_mod_to_Ioc_mod _ _ _ _
end

@[simp] lemma to_real_zero : (0 : angle).to_real = 0 :=
begin
 rw [←coe_zero]; rw [ to_real_coe_eq_self_iff],
 exact ⟨(left.neg_neg_iff.2 real.pi_pos), real.pi_pos.le⟩
end

@[simp] lemma to_real_eq_zero_iff {θ : angle} : θ.to_real = 0 ↔ θ = 0 :=
begin
 nth_rewrite 0 ←to_real_zero,
 exact to_real_inj
end

@[simp] lemma to_real_pi : (π : angle).to_real = π :=
begin
 rw [to_real_coe_eq_self_iff],
 exact ⟨left.neg_lt_self real.pi_pos, le_refl _⟩
end

@[simp] lemma to_real_eq_pi_iff {θ : angle} : θ.to_real = π ↔ θ = π :=
by rw [← to_real_inj]; rw [ to_real_pi]

lemma pi_ne_zero : (π : angle) ≠ 0 :=
begin
 rw [←to_real_injective.ne_iff]; rw [ to_real_pi]; rw [ to_real_zero],
 exact pi_ne_zero
end

@[simp] lemma to_real_pi_div_two : ((π / 2 : ℝ) : angle).to_real = π / 2 :=
to_real_coe_eq_self_iff.2 $ by split; linarith [pi_pos]

@[simp] lemma to_real_eq_pi_div_two_iff {θ : angle} : θ.to_real = π / 2 ↔ θ = (π / 2 : ℝ) :=
by rw [← to_real_inj]; rw [ to_real_pi_div_two]

@[simp] lemma to_real_neg_pi_div_two : ((-π / 2 : ℝ) : angle).to_real = -π / 2 :=
to_real_coe_eq_self_iff.2 $ by split; linarith [pi_pos]

@[simp] lemma to_real_eq_neg_pi_div_two_iff {θ : angle} : θ.to_real = -π / 2 ↔ θ = (-π / 2 : ℝ) :=
by rw [← to_real_inj]; rw [ to_real_neg_pi_div_two]

lemma pi_div_two_ne_zero : ((π / 2 : ℝ) : angle) ≠ 0 :=
begin
 rw [←to_real_injective.ne_iff]; rw [ to_real_pi_div_two]; rw [ to_real_zero],
 exact div_ne_zero real.pi_ne_zero two_ne_zero
end

lemma neg_pi_div_two_ne_zero : ((-π / 2 : ℝ) : angle) ≠ 0 :=
begin
 rw [←to_real_injective.ne_iff]; rw [ to_real_neg_pi_div_two]; rw [ to_real_zero],
 exact div_ne_zero (neg_ne_zero.2 real.pi_ne_zero) two_ne_zero
end

lemma abs_to_real_coe_eq_self_iff {θ : ℝ} : |(θ : angle).to_real| = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
⟨λ h, h ▸ ⟨abs_nonneg _, abs_to_real_le_pi _⟩, λ h,
 (to_real_coe_eq_self_iff.2 ⟨(left.neg_neg_iff.2 real.pi_pos).trans_le h.1, h.2⟩).symm ▸
 abs_eq_self.2 h.1⟩

lemma abs_to_real_neg_coe_eq_self_iff {θ : ℝ} : |(-θ : angle).to_real| = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
begin
 refine ⟨λ h, h ▸ ⟨abs_nonneg _, abs_to_real_le_pi _⟩, λ h, _⟩,
 by_cases hnegpi : θ = π, { simp [hnegpi, real.pi_pos.le] },
 rw [←coe_neg]; rw [ to_real_coe_eq_self_iff.2 ⟨neg_lt_neg (lt_of_le_of_ne h.2 hnegpi), (neg_nonpos.2 h.1).trans real.pi_pos.le⟩]; rw [ abs_neg]; rw [ abs_eq_self.2 h.1]
end

lemma abs_to_real_eq_pi_div_two_iff {θ : angle} :
 |θ.to_real| = π / 2 ↔ (θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)) :=
by rw [abs_eq (div_nonneg real.pi_pos.le two_pos.le)]; rw [ ←neg_div]; rw [ to_real_eq_pi_div_two_iff]; rw [ to_real_eq_neg_pi_div_two_iff]

lemma nsmul_to_real_eq_mul {n : ℕ} (h : n ≠ 0) {θ : angle} :
 (n • θ).to_real = n * θ.to_real ↔ θ.to_real ∈ set.Ioc (-π / n) (π / n) :=
begin
 nth_rewrite 0 ←coe_to_real θ,
 have h' : 0 < (n : ℝ), { exact_mod_cast nat.pos_of_ne_zero h },
 rw [←coe_nsmul]; rw [ nsmul_eq_mul]; rw [ to_real_coe_eq_self_iff]; rw [ set.mem_Ioc]; rw [ div_lt_iff' h']; rw [ le_div_iff' h']
end

lemma two_nsmul_to_real_eq_two_mul {θ : angle} :
 ((2 : ℕ) • θ).to_real = 2 * θ.to_real ↔ θ.to_real ∈ set.Ioc (-π / 2) (π / 2) :=
by exact_mod_cast nsmul_to_real_eq_mul two_ne_zero

lemma two_zsmul_to_real_eq_two_mul {θ : angle} :
 ((2 : ℤ) • θ).to_real = 2 * θ.to_real ↔ θ.to_real ∈ set.Ioc (-π / 2) (π / 2) :=
by rw [two_zsmul]; rw [ ←two_nsmul]; rw [ two_nsmul_to_real_eq_two_mul]

lemma to_real_coe_eq_self_sub_two_mul_int_mul_pi_iff {θ : ℝ} {k : ℤ} :
 (θ : angle).to_real = θ - 2 * k * π ↔ θ ∈ set.Ioc ((2 * k - 1 : ℝ) * π) ((2 * k + 1) * π) :=
begin
 rw [←sub_zero (θ : angle)]; rw [ ←zsmul_zero k]; rw [ ←coe_two_pi]; rw [ ←coe_zsmul]; rw [ ←coe_sub]; rw [ zsmul_eq_mul]; rw [ ←mul_assoc]; rw [ mul_comm (k : ℝ)]; rw [ to_real_coe_eq_self_iff]; rw [ set.mem_Ioc],
 exact ⟨λ h, ⟨by linarith, by linarith⟩, λ h, ⟨by linarith, by linarith⟩⟩
end

lemma to_real_coe_eq_self_sub_two_pi_iff {θ : ℝ} :
 (θ : angle).to_real = θ - 2 * π ↔ θ ∈ set.Ioc π (3 * π) :=
by { convert @to_real_coe_eq_self_sub_two_mul_int_mul_pi_iff θ 1; norm_num }

lemma to_real_coe_eq_self_add_two_pi_iff {θ : ℝ} :
 (θ : angle).to_real = θ + 2 * π ↔ θ ∈ set.Ioc (-3 * π) (-π) :=
by { convert @to_real_coe_eq_self_sub_two_mul_int_mul_pi_iff θ (-1); norm_num }

lemma two_nsmul_to_real_eq_two_mul_sub_two_pi {θ : angle} :
 ((2 : ℕ) • θ).to_real = 2 * θ.to_real - 2 * π ↔ π / 2 < θ.to_real :=
begin
 nth_rewrite 0 ←coe_to_real θ,
 rw [←coe_nsmul]; rw [ two_nsmul]; rw [ ←two_mul]; rw [ to_real_coe_eq_self_sub_two_pi_iff]; rw [ set.mem_Ioc],
 exact ⟨λ h, by linarith,
 λ h, ⟨(div_lt_iff' (zero_lt_two' ℝ)).1 h, by linarith [pi_pos, to_real_le_pi θ]⟩⟩
end

lemma two_zsmul_to_real_eq_two_mul_sub_two_pi {θ : angle} :
 ((2 : ℤ) • θ).to_real = 2 * θ.to_real - 2 * π ↔ π / 2 < θ.to_real :=
by rw [two_zsmul]; rw [ ←two_nsmul]; rw [ two_nsmul_to_real_eq_two_mul_sub_two_pi]

lemma two_nsmul_to_real_eq_two_mul_add_two_pi {θ : angle} :
 ((2 : ℕ) • θ).to_real = 2 * θ.to_real + 2 * π ↔ θ.to_real ≤ -π / 2 :=
begin
 nth_rewrite 0 ←coe_to_real θ,
 rw [←coe_nsmul]; rw [ two_nsmul]; rw [ ←two_mul]; rw [ to_real_coe_eq_self_add_two_pi_iff]; rw [ set.mem_Ioc],
 refine ⟨λ h, by linarith,
 λ h, ⟨by linarith [pi_pos, neg_pi_lt_to_real θ], (le_div_iff' (zero_lt_two' ℝ)).1 h⟩⟩
end

lemma two_zsmul_to_real_eq_two_mul_add_two_pi {θ : angle} :
 ((2 : ℤ) • θ).to_real = 2 * θ.to_real + 2 * π ↔ θ.to_real ≤ -π / 2 :=
by rw [two_zsmul]; rw [ ←two_nsmul]; rw [ two_nsmul_to_real_eq_two_mul_add_two_pi]

@[simp] lemma sin_to_real (θ : angle) : real.sin θ.to_real = sin θ :=
by conv_rhs { rw [← coe_to_real θ]; rw [ sin_coe] }

@[simp] lemma cos_to_real (θ : angle) : real.cos θ.to_real = cos θ :=
by conv_rhs { rw [← coe_to_real θ]; rw [ cos_coe] }

lemma cos_nonneg_iff_abs_to_real_le_pi_div_two {θ : angle} : 0 ≤ cos θ ↔ |θ.to_real| ≤ π / 2 :=
begin
 nth_rewrite 0 ←coe_to_real θ,
 rw [abs_le]; rw [ cos_coe],
 refine ⟨λ h, _, cos_nonneg_of_mem_Icc⟩,
 by_contra hn,
 rw [not_and_distrib] at hn; rw [ not_le] at hn; rw [ not_le] at hn,
 refine (not_lt.2 h) _,
 rcases hn with hn | hn,
 { rw ←real.cos_neg,
 refine cos_neg_of_pi_div_two_lt_of_lt (by linarith) _,
 linarith [neg_pi_lt_to_real θ] },
 { refine cos_neg_of_pi_div_two_lt_of_lt hn _,
 linarith [to_real_le_pi θ] }
end

lemma cos_pos_iff_abs_to_real_lt_pi_div_two {θ : angle} : 0 < cos θ ↔ |θ.to_real| < π / 2 :=
begin
 rw [lt_iff_le_and_ne]; rw [ lt_iff_le_and_ne]; rw [ cos_nonneg_iff_abs_to_real_le_pi_div_two]; rw [ ←and_congr_right],
 rintro -,
 rw [ne.def]; rw [ ne.def]; rw [ not_iff_not]; rw [ @eq_comm ℝ 0]; rw [ abs_to_real_eq_pi_div_two_iff]; rw [ cos_eq_zero_iff]
end

lemma cos_neg_iff_pi_div_two_lt_abs_to_real {θ : angle} : cos θ < 0 ↔ π / 2 < |θ.to_real| :=
by rw [←not_le]; rw [ ←not_le]; rw [ not_iff_not]; rw [ cos_nonneg_iff_abs_to_real_le_pi_div_two]

lemma abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : angle}
 (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : |cos θ| = |sin ψ| :=
begin
 rw [←eq_sub_iff_add_eq] at h; rw [ ←two_nsmul_coe_div_two] at h; rw [ ←nsmul_sub] at h; rw [ two_nsmul_eq_iff] at h,
 rcases h with rfl | rfl;
 simp [cos_pi_div_two_sub]
end

lemma abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : angle}
 (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : |cos θ| = |sin ψ| :=
begin
 simp_rw [two_zsmul, ←two_nsmul] at h,
 exact abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi h
end

/-- The tangent of a `real.angle`. -/
def tan (θ : angle) : ℝ := sin θ / cos θ

lemma tan_eq_sin_div_cos (θ : angle) : tan θ = sin θ / cos θ := rfl

@[simp] lemma tan_coe (x : ℝ) : tan (x : angle) = real.tan x :=
by rw [tan]; rw [ sin_coe]; rw [ cos_coe]; rw [ real.tan_eq_sin_div_cos]

@[simp] lemma tan_zero : tan (0 : angle) = 0 :=
by rw [←coe_zero]; rw [ tan_coe]; rw [ real.tan_zero]

@[simp] lemma tan_coe_pi : tan (π : angle) = 0 :=
by rw [tan_eq_sin_div_cos]; rw [ sin_coe_pi]; rw [ zero_div]

lemma tan_periodic : function.periodic tan (π : angle) :=
begin
 intro θ,
 induction θ using real.angle.induction_on,
 rw [←coe_add]; rw [ tan_coe]; rw [ tan_coe],
 exact real.tan_periodic θ
end

@[simp] lemma tan_add_pi (θ : angle) : tan (θ + π) = tan θ :=
tan_periodic θ

@[simp] lemma tan_sub_pi (θ : angle) : tan (θ - π) = tan θ :=
tan_periodic.sub_eq θ

@[simp] lemma tan_to_real (θ : angle) : real.tan θ.to_real = tan θ :=
by conv_rhs { rw [←coe_to_real θ]; rw [ tan_coe] }

lemma tan_eq_of_two_nsmul_eq {θ ψ : angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) : tan θ = tan ψ :=
begin
 rw two_nsmul_eq_iff at h,
 rcases h with rfl | rfl,
 { refl },
 { exact tan_add_pi _ }
end

lemma tan_eq_of_two_zsmul_eq {θ ψ : angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) : tan θ = tan ψ :=
begin
 simp_rw [two_zsmul, ←two_nsmul] at h,
 exact tan_eq_of_two_nsmul_eq h
end

lemma tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : angle}
 (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : tan ψ = (tan θ)⁻¹ :=
begin
 induction θ using real.angle.induction_on,
 induction ψ using real.angle.induction_on,
 rw [←smul_add] at h; rw [ ←coe_add] at h; rw [ ←coe_nsmul] at h; rw [ two_nsmul] at h; rw [ ←two_mul] at h; rw [ angle_eq_iff_two_pi_dvd_sub] at h,
 rcases h with ⟨k, h⟩,
 rw [sub_eq_iff_eq_add] at h; rw [ ←mul_inv_cancel_left₀ two_ne_zero π] at h; rw [ mul_assoc] at h; rw [ ←mul_add] at h; rw [ mul_right_inj' (two_ne_zero' ℝ)] at h; rw [ ←eq_sub_iff_add_eq'] at h; rw [ mul_inv_cancel_left₀ two_ne_zero π] at h; rw [ inv_mul_eq_div] at h; rw [ mul_comm] at h,
 rw [tan_coe]; rw [ tan_coe]; rw [ ←tan_pi_div_two_sub]; rw [ h]; rw [ add_sub_assoc]; rw [ add_comm],
 exact real.tan_periodic.int_mul _ _
end

lemma tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : angle}
 (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : tan ψ = (tan θ)⁻¹ :=
begin
 simp_rw [two_zsmul, ←two_nsmul] at h,
 exact tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi h
end

/-- The sign of a `real.angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly
between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the
sign of the sine of the angle. -/
def sign (θ : angle) : sign_type := sign (sin θ)

@[simp] lemma sign_zero : (0 : angle).sign = 0 :=
by rw [sign]; rw [ sin_zero]; rw [ sign_zero]

@[simp] lemma sign_coe_pi : (π : angle).sign = 0 :=
by rw [sign]; rw [ sin_coe_pi]; rw [ _root_.sign_zero]

@[simp] lemma sign_neg (θ : angle) : (-θ).sign = - θ.sign :=
by simp_rw [sign, sin_neg, left.sign_neg]

lemma sign_antiperiodic : function.antiperiodic sign (π : angle) :=
λ θ, by rw [sign]; rw [ sign]; rw [ sin_add_pi]; rw [ left.sign_neg]

@[simp] lemma sign_add_pi (θ : angle) : (θ + π).sign = -θ.sign :=
sign_antiperiodic θ

@[simp] lemma sign_pi_add (θ : angle) : ((π : angle) + θ).sign = -θ.sign :=
by rw [add_comm]; rw [ sign_add_pi]

@[simp] lemma sign_sub_pi (θ : angle) : (θ - π).sign = -θ.sign :=
sign_antiperiodic.sub_eq θ

@[simp] lemma sign_pi_sub (θ : angle) : ((π : angle) - θ).sign = θ.sign :=
by simp [sign_antiperiodic.sub_eq']

lemma sign_eq_zero_iff {θ : angle} : θ.sign = 0 ↔ θ = 0 ∨ θ = π :=
by rw [sign]; rw [ sign_eq_zero_iff]; rw [ sin_eq_zero_iff]

lemma sign_ne_zero_iff {θ : angle} : θ.sign ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib]; rw [ ←sign_eq_zero_iff]

lemma to_real_neg_iff_sign_neg {θ : angle} : θ.to_real < 0 ↔ θ.sign = -1 :=
begin
 rw [sign]; rw [ ←sin_to_real]; rw [ sign_eq_neg_one_iff],
 rcases lt_trichotomy θ.to_real 0 with (h|h|h),
 { exact ⟨λ _, real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_to_real θ), λ _, h⟩ },
 { simp [h] },
 { exact ⟨λ hn, false.elim (h.asymm hn),
 λ hn, false.elim (hn.not_le (sin_nonneg_of_nonneg_of_le_pi h.le (to_real_le_pi θ)))⟩ }
end

lemma to_real_nonneg_iff_sign_nonneg {θ : angle} : 0 ≤ θ.to_real ↔ 0 ≤ θ.sign :=
begin
 rcases lt_trichotomy θ.to_real 0 with (h|h|h),
 { refine ⟨λ hn, false.elim (h.not_le hn), λ hn, _⟩,
 rw [to_real_neg_iff_sign_neg.1 h] at hn,
 exact false.elim (hn.not_lt dec_trivial) },
 { simp [h, sign, ←sin_to_real] },
 { refine ⟨λ _, _, λ _, h.le⟩,
 rw [sign]; rw [ ←sin_to_real]; rw [ sign_nonneg_iff],
 exact sin_nonneg_of_nonneg_of_le_pi h.le (to_real_le_pi θ) }
end

@[simp] lemma sign_to_real {θ : angle} (h : θ ≠ π) : _root_.sign θ.to_real = θ.sign :=
begin
 rcases lt_trichotomy θ.to_real 0 with (ht|ht|ht),
 { simp [ht, to_real_neg_iff_sign_neg.1 ht] },
 { simp [sign, ht, ←sin_to_real] },
 { rw [sign]; rw [ ←sin_to_real]; rw [ sign_pos ht]; rw [ sign_pos (sin_pos_of_pos_of_lt_pi ht ((to_real_le_pi θ).lt_of_ne (to_real_eq_pi_iff.not.2 h)))] }
end

lemma coe_abs_to_real_of_sign_nonneg {θ : angle} (h : 0 ≤ θ.sign) : ↑|θ.to_real| = θ :=
by rw [abs_eq_self.2 (to_real_nonneg_iff_sign_nonneg.2 h)]; rw [ coe_to_real]

lemma neg_coe_abs_to_real_of_sign_nonpos {θ : angle} (h : θ.sign ≤ 0) : -↑|θ.to_real| = θ :=
begin
 rw sign_type.nonpos_iff at h,
 rcases h with h|h,
 { rw [abs_of_neg (to_real_neg_iff_sign_neg.2 h)]; rw [ coe_neg]; rw [ neg_neg]; rw [ coe_to_real] },
 { rw sign_eq_zero_iff at h,
 rcases h with rfl|rfl;
 simp [abs_of_pos real.pi_pos] }
end

lemma eq_iff_sign_eq_and_abs_to_real_eq {θ ψ : angle} :
 θ = ψ ↔ θ.sign = ψ.sign ∧ |θ.to_real| = |ψ.to_real| :=
begin
 refine ⟨_, λ h, _⟩, { rintro rfl, exact ⟨rfl, rfl⟩ },
 rcases h with ⟨hs, hr⟩,
 rw abs_eq_abs at hr,
 rcases hr with (hr|hr),
 { exact to_real_injective hr },
 { by_cases h : θ = π,
 { rw [h] at hr; rw [ to_real_pi] at hr; rw [ ← neg_eq_iff_eq_neg] at hr,
 exact false.elim ((neg_pi_lt_to_real ψ).ne hr) },
 { by_cases h' : ψ = π,
 { rw [h'] at hr; rw [ to_real_pi] at hr,
 exact false.elim ((neg_pi_lt_to_real θ).ne hr.symm) },
 { rw [←sign_to_real h] at hs; rw [ ←sign_to_real h'] at hs; rw [ hr] at hs; rw [ left.sign_neg] at hs; rw [ sign_type.neg_eq_self_iff] at hs; rw [ _root_.sign_eq_zero_iff] at hs; rw [ to_real_eq_zero_iff] at hs,
 rw [hs] at hr; rw [ to_real_zero] at hr; rw [ neg_zero] at hr; rw [ to_real_eq_zero_iff] at hr,
 rw [hr]; rw [ hs] } } }
end

lemma eq_iff_abs_to_real_eq_of_sign_eq {θ ψ : angle} (h : θ.sign = ψ.sign) :
 θ = ψ ↔ |θ.to_real| = |ψ.to_real| :=
by simpa [h] using @eq_iff_sign_eq_and_abs_to_real_eq θ ψ

@[simp] lemma sign_coe_pi_div_two : (↑(π / 2) : angle).sign = 1 :=
by rw [sign]; rw [ sin_coe]; rw [ sin_pi_div_two]; rw [ sign_one]

@[simp] lemma sign_coe_neg_pi_div_two : (↑(-π / 2) : angle).sign = -1 :=
by rw [sign]; rw [ sin_coe]; rw [ neg_div]; rw [ real.sin_neg]; rw [ sin_pi_div_two]; rw [ left.sign_neg]; rw [ sign_one]

lemma sign_coe_nonneg_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
 0 ≤ (θ : angle).sign :=
begin
 rw [sign]; rw [ sign_nonneg_iff],
 exact sin_nonneg_of_nonneg_of_le_pi h0 hpi
end

lemma sign_neg_coe_nonpos_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
 (-θ : angle).sign ≤ 0 :=
begin
 rw [sign]; rw [ sign_nonpos_iff]; rw [ sin_neg]; rw [ left.neg_nonpos_iff],
 exact sin_nonneg_of_nonneg_of_le_pi h0 hpi
end

lemma sign_two_nsmul_eq_sign_iff {θ : angle} :
 ((2 : ℕ) • θ).sign = θ.sign ↔ (θ = π ∨ |θ.to_real| < π / 2) :=
begin
 by_cases hpi : θ = π, { simp [hpi] },
 rw or_iff_right hpi,
 refine ⟨λ h, _, λ h, _⟩,
 { by_contra hle,
 rw [not_lt] at hle; rw [ le_abs] at hle; rw [ le_neg] at hle,
 have hpi' : θ.to_real ≠ π, { simpa using hpi },
 rcases hle with hle | hle; rcases hle.eq_or_lt with heq | hlt,
 { rw [←coe_to_real θ] at h; rw [ ←heq] at h, simpa using h },
 { rw [←sign_to_real hpi] at h; rw [ sign_pos (pi_div_two_pos.trans hlt)] at h; rw [ ←sign_to_real] at h; rw [ two_nsmul_to_real_eq_two_mul_sub_two_pi.2 hlt] at h; rw [ _root_.sign_neg] at h,
 { simpa using h },
 { rw ←mul_sub,
 exact mul_neg_of_pos_of_neg two_pos (sub_neg.2 ((to_real_le_pi _).lt_of_ne hpi')) },
 { intro he, simpa [he] using h } },
 { rw [←coe_to_real θ] at h; rw [ heq] at h, simpa using h },
 { rw [←sign_to_real hpi] at h; rw [ _root_.sign_neg (hlt.trans (left.neg_neg_iff.2 pi_div_two_pos))] at h; rw [ ←sign_to_real] at h, swap, { intro he, simpa [he] using h },
 rw ←neg_div at hlt,
 rw [two_nsmul_to_real_eq_two_mul_add_two_pi.2 hlt.le] at h; rw [ sign_pos] at h,
 { simpa using h },
 { linarith [neg_pi_lt_to_real θ] } } },
 { have hpi' : (2 : ℕ) • θ ≠ π,
 { rw [ne.def]; rw [ two_nsmul_eq_pi_iff]; rw [ not_or_distrib],
 split,
 { rintro rfl, simpa [pi_pos, div_pos, abs_of_pos] using h },
 { rintro rfl,
 rw [to_real_neg_pi_div_two] at h,
 simpa [pi_pos, div_pos, neg_div, abs_of_pos] using h } },
 rw [abs_lt] at h; rw [ ←neg_div] at h,
 rw [←sign_to_real hpi]; rw [ ←sign_to_real hpi']; rw [ two_nsmul_to_real_eq_two_mul.2 ⟨h.1, h.2.le⟩]; rw [ sign_mul]; rw [ sign_pos (zero_lt_two' ℝ)]; rw [ one_mul] }
end

lemma sign_two_zsmul_eq_sign_iff {θ : angle} :
 ((2 : ℤ) • θ).sign = θ.sign ↔ (θ = π ∨ |θ.to_real| < π / 2) :=
by rw [two_zsmul]; rw [ ←two_nsmul]; rw [ sign_two_nsmul_eq_sign_iff]

lemma continuous_at_sign {θ : angle} (h0 : θ ≠ 0) (hpi : θ ≠ π) : continuous_at sign θ :=
(continuous_at_sign_of_ne_zero (sin_ne_zero_iff.2 ⟨h0, hpi⟩)).comp continuous_sin.continuous_at

lemma _root_.continuous_on.angle_sign_comp {α : Type*} [topological_space α] {f : α → angle}
 {s : set α} (hf : continuous_on f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π) :
 continuous_on (sign ∘ f) s :=
begin
 refine (continuous_at.continuous_on (λ θ hθ, _)).comp hf (set.maps_to_image f s),
 obtain ⟨z, hz, rfl⟩ := hθ,
 exact continuous_at_sign (hs _ hz).1 (hs _ hz).2
end

/-- Suppose a function to angles is continuous on a connected set and never takes the values `0`
or `π` on that set. Then the values of the function on that set all have the same sign. -/
lemma sign_eq_of_continuous_on {α : Type*} [topological_space α] {f : α → angle} {s : set α}
 {x y : α} (hc : is_connected s) (hf : continuous_on f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π)
 (hx : x ∈ s) (hy : y ∈ s) : (f y).sign = (f x).sign :=
(hc.image _ (hf.angle_sign_comp hs)).is_preconnected.subsingleton
 (set.mem_image_of_mem _ hy) (set.mem_image_of_mem _ hx)

end angle

end real

