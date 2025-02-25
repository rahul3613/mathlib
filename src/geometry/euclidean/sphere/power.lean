/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson
-/
import geometry.euclidean.angle.unoriented.affine
import geometry.euclidean.sphere.basic

/-!
# Power of a point (intersecting chords and secants)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic geometrical results about power of a point (intersecting chords and
secants) in spheres in real inner product spaces and Euclidean affine spaces.

## Main theorems

* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`: Intersecting Chords Theorem (Freek No. 55).
* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`: Intersecting Secants Theorem.
-/

open real
open_locale euclidean_geometry real_inner_product_space real

variables {V : Type*} [normed_add_comm_group V] [inner_product_space ℝ V]

namespace inner_product_geometry

/-!
### Geometrical results on spheres in real inner product spaces

This section develops some results on spheres in real inner product spaces,
which are used to deduce corresponding results for Euclidean affine spaces.
-/

lemma mul_norm_eq_abs_sub_sq_norm {x y z : V}
 (h₁ : ∃ k : ℝ, k ≠ 1 ∧ x + y = k • (x - y)) (h₂ : ‖z - y‖ = ‖z + y‖) :
 ‖x - y‖ * ‖x + y‖ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| :=
begin
 obtain ⟨k, hk_ne_one, hk⟩ := h₁,
 let r := (k - 1)⁻¹ * (k + 1),

 have hxy : x = r • y,
 { rw [← smul_smul]; rw [ eq_inv_smul_iff₀ (sub_ne_zero.mpr hk_ne_one)]; rw [ ← sub_eq_zero],
 calc (k - 1) • x - (k + 1) • y
 = (k • x - x) - (k • y + y) : by simp_rw [sub_smul, add_smul, one_smul]
 ... = (k • x - k • y) - (x + y) : by simp_rw [← sub_sub, sub_right_comm]
 ... = k • (x - y) - (x + y) : by rw ← smul_sub k x y
 ... = 0 : sub_eq_zero.mpr hk.symm },

 have hzy : ⟪z, y⟫ = 0,
 by rwa [inner_eq_zero_iff_angle_eq_pi_div_two]; rwa [ ← norm_add_eq_norm_sub_iff_angle_eq_pi_div_two]; rwa [ eq_comm],

 have hzx : ⟪z, x⟫ = 0 := by rw [hxy]; rw [ inner_smul_right]; rw [ hzy]; rw [ mul_zero],

 calc ‖x - y‖ * ‖x + y‖
 = ‖(r - 1) • y‖ * ‖(r + 1) • y‖ : by simp [sub_smul, add_smul, hxy]
 ... = ‖r - 1‖ * ‖y‖ * (‖r + 1‖ * ‖y‖) : by simp_rw [norm_smul]
 ... = ‖r - 1‖ * ‖r + 1‖ * ‖y‖ ^ 2 : by ring
 ... = |(r - 1) * (r + 1) * ‖y‖ ^ 2| : by simp [abs_mul]
 ... = |r ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2| : by ring_nf
 ... = |‖x‖ ^ 2 - ‖y‖ ^ 2| : by simp [hxy, norm_smul, mul_pow, sq_abs]
 ... = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| : by simp [norm_add_sq_real, norm_sub_sq_real,
 hzy, hzx, abs_sub_comm],
end

end inner_product_geometry

namespace euclidean_geometry

/-!
### Geometrical results on spheres in Euclidean affine spaces

This section develops some results on spheres in Euclidean affine spaces.
-/

open inner_product_geometry

variables {P : Type*} [metric_space P] [normed_add_torsor V P]
include V

/-- If `P` is a point on the line `AB` and `Q` is equidistant from `A` and `B`, then
`AP * BP = abs (BQ ^ 2 - PQ ^ 2)`. -/
lemma mul_dist_eq_abs_sub_sq_dist {a b p q : P}
 (hp : ∃ k : ℝ, k ≠ 1 ∧ b -ᵥ p = k • (a -ᵥ p)) (hq : dist a q = dist b q) :
 dist a p * dist b p = |dist b q ^ 2 - dist p q ^ 2| :=
begin
 let m : P := midpoint ℝ a b,
 obtain ⟨v, h1, h2, h3⟩ := ⟨vsub_sub_vsub_cancel_left, v a p m, v p q m, v a q m⟩,
 have h : ∀ r, b -ᵥ r = (m -ᵥ r) + (m -ᵥ a) :=
 λ r, by rw [midpoint_vsub_left]; rw [ ← right_vsub_midpoint]; rw [ add_comm]; rw [ vsub_add_vsub_cancel],
 iterate 4 { rw dist_eq_norm_vsub V },
 rw [← h1]; rw [ ← h2]; rw [ h]; rw [ h],
 rw [← h1] at hp; rw [ h] at hp,
 rw [dist_eq_norm_vsub V a q] at hq; rw [ dist_eq_norm_vsub V b q] at hq; rw [ ← h3] at hq; rw [ h] at hq,
 exact mul_norm_eq_abs_sub_sq_norm hp hq,
end

/-- If `A`, `B`, `C`, `D` are cospherical and `P` is on both lines `AB` and `CD`, then
`AP * BP = CP * DP`. -/
lemma mul_dist_eq_mul_dist_of_cospherical {a b c d p : P}
 (h : cospherical ({a, b, c, d} : set P))
 (hapb : ∃ k₁ : ℝ, k₁ ≠ 1 ∧ b -ᵥ p = k₁ • (a -ᵥ p))
 (hcpd : ∃ k₂ : ℝ, k₂ ≠ 1 ∧ d -ᵥ p = k₂ • (c -ᵥ p)) :
 dist a p * dist b p = dist c p * dist d p :=
begin
 obtain ⟨q, r, h'⟩ := (cospherical_def {a, b, c, d}).mp h,
 obtain ⟨ha, hb, hc, hd⟩ := ⟨h' a _, h' b _, h' c _, h' d _⟩,
 { rw ← hd at hc,
 rw ← hb at ha,
 rw [mul_dist_eq_abs_sub_sq_dist hapb ha]; rw [ hb]; rw [ mul_dist_eq_abs_sub_sq_dist hcpd hc]; rw [ hd] },
 all_goals { simp },
end

/-- **Intersecting Chords Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P}
 (h : cospherical ({a, b, c, d} : set P))
 (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
 dist a p * dist b p = dist c p * dist d p :=
begin
 obtain ⟨-, k₁, _, hab⟩ := angle_eq_pi_iff.mp hapb,
 obtain ⟨-, k₂, _, hcd⟩ := angle_eq_pi_iff.mp hcpd,
 exact mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, (by linarith), hab⟩ ⟨k₂, (by linarith), hcd⟩,
end

/-- **Intersecting Secants Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P}
 (h : cospherical ({a, b, c, d} : set P))
 (hab : a ≠ b) (hcd : c ≠ d) (hapb : ∠ a p b = 0) (hcpd : ∠ c p d = 0) :
 dist a p * dist b p = dist c p * dist d p :=
begin
 obtain ⟨-, k₁, -, hab₁⟩ := angle_eq_zero_iff.mp hapb,
 obtain ⟨-, k₂, -, hcd₁⟩ := angle_eq_zero_iff.mp hcpd,
 refine mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, _, hab₁⟩ ⟨k₂, _, hcd₁⟩;
 by_contra hnot;
 simp only [not_not, *, one_smul] at *,
 exacts [hab (vsub_left_cancel hab₁).symm, hcd (vsub_left_cancel hcd₁).symm],
end

end euclidean_geometry

