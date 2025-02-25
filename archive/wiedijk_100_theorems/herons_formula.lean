/-
Copyright (c) 2021 Matt Kempster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Kempster
-/
import geometry.euclidean.triangle

/-!
# Freek № 57: Heron's Formula

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves Theorem 57 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/),
also known as Heron's formula, which gives the area of a triangle based only on its three sides'
lengths.

## References

* https://en.wikipedia.org/wiki/Herons_formula

-/

open real euclidean_geometry
open_locale real euclidean_geometry

namespace theorems_100

local notation `√` := real.sqrt

variables {V : Type*} {P : Type*}
 [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]

include V

/-- **Heron's formula**: The area of a triangle with side lengths `a`, `b`, and `c` is
 `√(s * (s - a) * (s - b) * (s - c))` where `s = (a + b + c) / 2` is the semiperimeter.
 We show this by equating this formula to `a * b * sin γ`, where `γ` is the angle opposite
 the side `c`.
 -/
theorem heron {p1 p2 p3 : P} (h1 : p1 ≠ p2) (h2 : p3 ≠ p2) :
 let a := dist p1 p2, b := dist p3 p2, c := dist p1 p3, s := (a + b + c) / 2 in
 1/2 * a * b * sin (∠ p1 p2 p3) = √(s * (s - a) * (s - b) * (s - c)) :=
begin
 intros a b c s,
 let γ := ∠ p1 p2 p3,
 obtain := ⟨(dist_pos.mpr h1).ne', (dist_pos.mpr h2).ne'⟩,
 have cos_rule : cos γ = (a * a + b * b - c * c) / (2 * a * b) := by field_simp [mul_comm, a,
 dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p1 p2 p3],
 let numerator := (2*a*b)^2 - (a*a + b*b - c*c)^2,
 let denominator := (2*a*b)^2,
 have split_to_frac : 1 - cos γ ^ 2 = numerator / denominator := by field_simp [cos_rule],
 have numerator_nonneg : 0 ≤ numerator,
 { have frac_nonneg: 0 ≤ numerator / denominator := by linarith [split_to_frac, cos_sq_le_one γ],
 cases div_nonneg_iff.mp frac_nonneg,
 { exact h.left },
 { simpa [h1, h2] using le_antisymm h.right (sq_nonneg _) } },
 have ab2_nonneg : 0 ≤ (2 * a * b) := by norm_num [mul_nonneg, dist_nonneg],
 calc 1/2 * a * b * sin γ
 = 1/2 * a * b * (√numerator / √denominator) : by rw [sin_eq_sqrt_one_sub_cos_sq]; rw [ split_to_frac]; rw [ sqrt_div numerator_nonneg];
 simp [angle_nonneg, angle_le_pi]
 ... = 1/4 * √((2*a*b)^2 - (a*a + b*b - c*c)^2) : by { field_simp [ab2_nonneg], ring }
 ... = 1/4 * √(s * (s-a) * (s-b) * (s-c) * 4^2) : by { simp only [s], ring_nf }
 ... = √(s * (s-a) * (s-b) * (s-c)) : by rw [sqrt_mul']; rw [ sqrt_sq]; rw [ div_mul_eq_mul_div]; rw [ one_mul]; rw [ mul_div_cancel];
 norm_num,
end

end theorems_100

