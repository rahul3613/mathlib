/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import analysis.convex.between
import geometry.euclidean.angle.unoriented.basic

/-!
# Angles between points

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines unoriented angles in Euclidean affine spaces.

## Main definitions

* `euclidean_geometry.angle`, with notation `∠`, is the undirected angle determined by three
 points.

-/

noncomputable theory
open_locale big_operators
open_locale real
open_locale real_inner_product_space

namespace euclidean_geometry

open inner_product_geometry

variables {V : Type*} {P : Type*}
 [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
include V

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. Use
`open_locale euclidean_geometry` to access the `∠ p1 p2 p3`
notation. -/
def angle (p1 p2 p3 : P) : ℝ := angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2)

localized "notation (name := angle) `∠` := euclidean_geometry.angle" in euclidean_geometry

lemma continuous_at_angle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
 continuous_at (λ y : P × P × P, ∠ y.1 y.2.1 y.2.2) x :=
begin
 let f : P × P × P → V × V := λ y, (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1),
 have hf1 : (f x).1 ≠ 0, by simp [hx12],
 have hf2 : (f x).2 ≠ 0, by simp [hx32],
 exact (inner_product_geometry.continuous_at_angle hf1 hf2).comp
 ((continuous_fst.vsub continuous_snd.fst).prod_mk
 (continuous_snd.snd.vsub continuous_snd.fst)).continuous_at
end

@[simp] lemma _root_.affine_isometry.angle_map {V₂ P₂ : Type*}
 [normed_add_comm_group V₂] [inner_product_space ℝ V₂]
 [metric_space P₂] [normed_add_torsor V₂ P₂] (f : P →ᵃⁱ[ℝ] P₂) (p₁ p₂ p₃ : P) :
 ∠ (f p₁) (f p₂) (f p₃) = ∠ p₁ p₂ p₃ :=
by simp_rw [angle, ←affine_isometry.map_vsub, linear_isometry.angle_map]

@[simp, norm_cast] lemma _root_.affine_subspace.angle_coe {s : affine_subspace ℝ P}
 (p₁ p₂ p₃ : s) :
 by haveI : nonempty s := ⟨p₁⟩; exact ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
by haveI : nonempty s := ⟨p₁⟩; exact s.subtypeₐᵢ.angle_map p₁ p₂ p₃

/-- Angles are translation invariant -/
@[simp] lemma angle_const_vadd (v : V) (p₁ p₂ p₃ : P) :
 ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃ :=
(affine_isometry_equiv.const_vadd ℝ P v).to_affine_isometry.angle_map _ _ _

/-- Angles are translation invariant -/
@[simp] lemma angle_vadd_const (v₁ v₂ v₃ : V) (p : P) :
 ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃ :=
(affine_isometry_equiv.vadd_const ℝ p).to_affine_isometry.angle_map _ _ _

/-- Angles are translation invariant -/
@[simp] lemma angle_const_vsub (p p₁ p₂ p₃ : P) : ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃ :=
(affine_isometry_equiv.const_vsub ℝ p).to_affine_isometry.angle_map _ _ _

/-- Angles are translation invariant -/
@[simp] lemma angle_vsub_const (p₁ p₂ p₃ p : P) : ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃ :=
(affine_isometry_equiv.vadd_const ℝ p).symm.to_affine_isometry.angle_map _ _ _

/-- Angles in a vector space are translation invariant -/
@[simp] lemma angle_add_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ v₁ v₂ v₃ :=
angle_vadd_const _ _ _ _

/-- Angles in a vector space are translation invariant -/
@[simp] lemma angle_const_add (v : V) (v₁ v₂ v₃ : V) : ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ v₁ v₂ v₃ :=
angle_const_vadd _ _ _ _

/-- Angles in a vector space are translation invariant -/
@[simp] lemma angle_sub_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ v₁ v₂ v₃ :=
by simpa only [vsub_eq_sub] using angle_vsub_const v₁ v₂ v₃ v

/-- Angles in a vector space are invariant to inversion -/
@[simp] lemma angle_const_sub (v : V) (v₁ v₂ v₃ : V) : ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃ :=
by simpa only [vsub_eq_sub] using angle_const_vsub _ _ _ _

/-- Angles in a vector space are invariant to inversion -/
@[simp] lemma angle_neg (v₁ v₂ v₃ : V) : ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃ :=
by simpa only [zero_sub] using angle_const_sub 0 v₁ v₂ v₃

/-- The angle at a point does not depend on the order of the other two
points. -/
lemma angle_comm (p1 p2 p3 : P) : ∠ p1 p2 p3 = ∠ p3 p2 p1 :=
angle_comm _ _

/-- The angle at a point is nonnegative. -/
lemma angle_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ p1 p2 p3 :=
angle_nonneg _ _

/-- The angle at a point is at most π. -/
lemma angle_le_pi (p1 p2 p3 : P) : ∠ p1 p2 p3 ≤ π :=
angle_le_pi _ _

/-- The angle ∠AAB at a point. -/
lemma angle_eq_left (p1 p2 : P) : ∠ p1 p1 p2 = π / 2 :=
begin
 unfold angle,
 rw vsub_self,
 exact angle_zero_left _
end

/-- The angle ∠ABB at a point. -/
lemma angle_eq_right (p1 p2 : P) : ∠ p1 p2 p2 = π / 2 :=
by rw [angle_comm]; rw [ angle_eq_left]

/-- The angle ∠ABA at a point. -/
lemma angle_eq_of_ne {p1 p2 : P} (h : p1 ≠ p2) : ∠ p1 p2 p1 = 0 :=
angle_self (λ he, h (vsub_eq_zero_iff_eq.1 he))

/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_left {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
 ∠ p2 p1 p3 = 0 :=
begin
 unfold angle at h,
 rw angle_eq_pi_iff at h,
 rcases h with ⟨hp1p2, ⟨r, ⟨hr, hpr⟩⟩⟩,
 unfold angle,
 rw angle_eq_zero_iff,
 rw [←neg_vsub_eq_vsub_rev] at hp1p2; rw [ neg_ne_zero] at hp1p2,
 use [hp1p2, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one],
 rw [add_smul]; rw [ ←neg_vsub_eq_vsub_rev p1 p2]; rw [ smul_neg],
 simp [←hpr]
end

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_right {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
 ∠ p2 p3 p1 = 0 :=
begin
 rw angle_comm at h,
 exact angle_eq_zero_of_angle_eq_pi_left h
end

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
lemma angle_eq_angle_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
 ∠ p1 p2 p3 = ∠ p1 p2 p4 :=
begin
 unfold angle at *,
 rcases angle_eq_pi_iff.1 h with ⟨hp2p3, ⟨r, ⟨hr, hpr⟩⟩⟩,
 rw [eq_comm],
 convert angle_smul_right_of_pos (p1 -ᵥ p2) (p3 -ᵥ p2) (add_pos (neg_pos_of_neg hr) zero_lt_one),
 rw [add_smul]; rw [ ← neg_vsub_eq_vsub_rev p2 p3]; rw [ smul_neg]; rw [ neg_smul]; rw [ ← hpr],
 simp
end

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
lemma angle_add_angle_eq_pi_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
 ∠ p1 p3 p2 + ∠ p1 p3 p4 = π :=
begin
 unfold angle at h,
 rw [angle_comm p1 p3 p2]; rw [ angle_comm p1 p3 p4],
 unfold angle,
 exact angle_add_angle_eq_pi_of_angle_eq_pi _ h
end

/-- Vertical Angles Theorem: angles opposite each other, formed by two intersecting straight
lines, are equal. -/
lemma angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p1 p2 p3 p4 p5 : P}
 (hapc : ∠ p1 p5 p3 = π) (hbpd : ∠ p2 p5 p4 = π) : ∠ p1 p5 p2 = ∠ p3 p5 p4 :=
by linarith [angle_add_angle_eq_pi_of_angle_eq_pi p1 hbpd, angle_comm p4 p5 p1,
 angle_add_angle_eq_pi_of_angle_eq_pi p4 hapc, angle_comm p4 p5 p3]

/-- If ∠ABC = π then dist A B ≠ 0. -/
lemma left_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p1 p2 ≠ 0 :=
begin
 by_contra heq,
 rw [dist_eq_zero] at heq,
 rw [heq] at h; rw [ angle_eq_left] at h,
 exact real.pi_ne_zero (by linarith),
end

/-- If ∠ABC = π then dist C B ≠ 0. -/
lemma right_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p3 p2 ≠ 0 :=
left_dist_ne_zero_of_angle_eq_pi $ (angle_comm _ _ _).trans h

/-- If ∠ABC = π, then (dist A C) = (dist A B) + (dist B C). -/
lemma dist_eq_add_dist_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
 dist p1 p3 = dist p1 p2 + dist p3 p2 :=
begin
 rw [dist_eq_norm_vsub V]; rw [ dist_eq_norm_vsub V]; rw [ dist_eq_norm_vsub V]; rw [ ← vsub_sub_vsub_cancel_right],
 exact norm_sub_eq_add_norm_of_angle_eq_pi h,
end

/-- If A ≠ B and C ≠ B then ∠ABC = π if and only if (dist A C) = (dist A B) + (dist B C). -/
lemma dist_eq_add_dist_iff_angle_eq_pi {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
 dist p1 p3 = dist p1 p2 + dist p3 p2 ↔ ∠ p1 p2 p3 = π :=
begin
 rw [dist_eq_norm_vsub V]; rw [ dist_eq_norm_vsub V]; rw [ dist_eq_norm_vsub V]; rw [ ← vsub_sub_vsub_cancel_right],
 exact norm_sub_eq_add_norm_iff_angle_eq_pi
 ((λ he, hp1p2 (vsub_eq_zero_iff_eq.1 he))) (λ he, hp3p2 (vsub_eq_zero_iff_eq.1 he)),
end

/-- If ∠ABC = 0, then (dist A C) = abs ((dist A B) - (dist B C)). -/
lemma dist_eq_abs_sub_dist_of_angle_eq_zero {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = 0) :
 (dist p1 p3) = |(dist p1 p2) - (dist p3 p2)| :=
begin
 rw [dist_eq_norm_vsub V]; rw [ dist_eq_norm_vsub V]; rw [ dist_eq_norm_vsub V]; rw [ ← vsub_sub_vsub_cancel_right],
 exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h,
end

/-- If A ≠ B and C ≠ B then ∠ABC = 0 if and only if (dist A C) = abs ((dist A B) - (dist B C)). -/
lemma dist_eq_abs_sub_dist_iff_angle_eq_zero {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
 (dist p1 p3) = |(dist p1 p2) - (dist p3 p2)| ↔ ∠ p1 p2 p3 = 0 :=
begin
 rw [dist_eq_norm_vsub V]; rw [ dist_eq_norm_vsub V]; rw [ dist_eq_norm_vsub V]; rw [ ← vsub_sub_vsub_cancel_right],
 exact norm_sub_eq_abs_sub_norm_iff_angle_eq_zero
 ((λ he, hp1p2 (vsub_eq_zero_iff_eq.1 he))) (λ he, hp3p2 (vsub_eq_zero_iff_eq.1 he)),
end

/-- If M is the midpoint of the segment AB, then ∠AMB = π. -/
lemma angle_midpoint_eq_pi (p1 p2 : P) (hp1p2 : p1 ≠ p2) : ∠ p1 (midpoint ℝ p1 p2) p2 = π :=
have p2 -ᵥ midpoint ℝ p1 p2 = -(p1 -ᵥ midpoint ℝ p1 p2), by { rw neg_vsub_eq_vsub_rev, simp },
by simp [angle, this, hp1p2, -zero_lt_one]

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMA = π / 2. -/
lemma angle_left_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
 ∠ p3 (midpoint ℝ p1 p2) p1 = π / 2 :=
begin
 let m : P := midpoint ℝ p1 p2,
 have h1 : p3 -ᵥ p1 = (p3 -ᵥ m) - (p1 -ᵥ m) := (vsub_sub_vsub_cancel_right p3 p1 m).symm,
 have h2 : p3 -ᵥ p2 = (p3 -ᵥ m) + (p1 -ᵥ m),
 { rw [left_vsub_midpoint]; rw [ ← midpoint_vsub_right]; rw [ vsub_add_vsub_cancel] },
 rw [dist_eq_norm_vsub V p3 p1] at h; rw [ dist_eq_norm_vsub V p3 p2] at h; rw [ h1] at h; rw [ h2] at h,
 exact (norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (p3 -ᵥ m) (p1 -ᵥ m)).mp h.symm,
end

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMB = π / 2. -/
lemma angle_right_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
 ∠ p3 (midpoint ℝ p1 p2) p2 = π / 2 :=
by rw [midpoint_comm p1 p2]; rw [ angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]

/-- If the second of three points is strictly between the other two, the angle at that point
is π. -/
lemma _root_.sbtw.angle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₂ p₃ = π :=
begin
 rw [angle]; rw [ angle_eq_pi_iff],
 rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩,
 refine ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r, _⟩,
 have hr0' : r ≠ 0,
 { rintro rfl,
 rw ←hp₂ at hp₂p₁,
 simpa using hp₂p₁ },
 have hr1' : r ≠ 1,
 { rintro rfl,
 rw ←hp₂ at hp₂p₃,
 simpa using hp₂p₃ },
 replace hr0 := hr0.lt_of_ne hr0'.symm,
 replace hr1 := hr1.lt_of_ne hr1',
 refine ⟨div_neg_of_neg_of_pos (left.neg_neg_iff.2 (sub_pos.2 hr1)) hr0, _⟩,
 rw [←hp₂]; rw [ affine_map.line_map_apply]; rw [ vsub_vadd_eq_vsub_sub]; rw [ vsub_vadd_eq_vsub_sub]; rw [ vsub_self]; rw [ zero_sub]; rw [ smul_neg]; rw [ smul_smul]; rw [ div_mul_cancel _ hr0']; rw [ neg_smul]; rw [ neg_neg]; rw [ sub_eq_iff_eq_add]; rw [ ←add_smul]; rw [ sub_add_cancel]; rw [ one_smul]
end

/-- If the second of three points is strictly between the other two, the angle at that point
(reversed) is π. -/
lemma _root_.sbtw.angle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₂ p₁ = π :=
by rw [←h.angle₁₂₃_eq_pi]; rw [ angle_comm]

/-- The angle between three points is π if and only if the second point is strictly between the
other two. -/
lemma angle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = π ↔ sbtw ℝ p₁ p₂ p₃ :=
begin
 refine ⟨_, λ h, h.angle₁₂₃_eq_pi⟩,
 rw [angle]; rw [ angle_eq_pi_iff],
 rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩,
 refine ⟨⟨1 / (1 - r),
 ⟨div_nonneg zero_le_one (sub_nonneg.2 (hr.le.trans zero_le_one)),
 (div_le_one (sub_pos.2 (hr.trans zero_lt_one))).2 ((le_sub_self_iff 1).2 hr.le)⟩, _⟩,
 (vsub_ne_zero.1 hp₁p₂).symm, _⟩,
 { rw ←eq_vadd_iff_vsub_eq at hp₃p₂,
 rw [affine_map.line_map_apply]; rw [ hp₃p₂]; rw [ vadd_vsub_assoc]; rw [ ←neg_vsub_eq_vsub_rev p₂ p₁]; rw [ smul_neg]; rw [ ←neg_smul]; rw [ smul_add]; rw [ smul_smul]; rw [ ←add_smul]; rw [ eq_comm]; rw [ eq_vadd_iff_vsub_eq],
 convert (one_smul ℝ (p₂ -ᵥ p₁)).symm,
 field_simp [(sub_pos.2 (hr.trans zero_lt_one)).ne.symm],
 abel },
 { rw [ne_comm]; rw [ ←@vsub_ne_zero V]; rw [ hp₃p₂]; rw [ smul_ne_zero_iff],
 exact ⟨hr.ne, hp₁p₂⟩ }
end

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point is zero. -/
lemma _root_.wbtw.angle₂₁₃_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
 ∠ p₂ p₁ p₃ = 0 :=
begin
 rw [angle]; rw [ angle_eq_zero_iff],
 rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩,
 have hr0' : r ≠ 0, { rintro rfl, simpa using hp₂p₁ },
 replace hr0 := hr0.lt_of_ne hr0'.symm,
 refine ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, _⟩,
 rw [affine_map.line_map_apply]; rw [ vadd_vsub_assoc]; rw [ vsub_self]; rw [ add_zero]; rw [ smul_smul]; rw [ inv_mul_cancel hr0']; rw [ one_smul]
end

/-- If the second of three points is strictly between the other two, the angle at the first point
is zero. -/
lemma _root_.sbtw.angle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₁ p₃ = 0 :=
h.wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point (reversed) is zero. -/
lemma _root_.wbtw.angle₃₁₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
 ∠ p₃ p₁ p₂ = 0 :=
by rw [←h.angle₂₁₃_eq_zero_of_ne hp₂p₁]; rw [ angle_comm]

/-- If the second of three points is strictly between the other two, the angle at the first point
(reversed) is zero. -/
lemma _root_.sbtw.angle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₁ p₂ = 0 :=
h.wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point is zero. -/
lemma _root_.wbtw.angle₂₃₁_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
 ∠ p₂ p₃ p₁ = 0 :=
h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃

/-- If the second of three points is strictly between the other two, the angle at the third point
is zero. -/
lemma _root_.sbtw.angle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₃ p₁ = 0 :=
h.wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point (reversed) is zero. -/
lemma _root_.wbtw.angle₁₃₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
 ∠ p₁ p₃ p₂ = 0 :=
h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃

/-- If the second of three points is strictly between the other two, the angle at the third point
(reversed) is zero. -/
lemma _root_.sbtw.angle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₃ p₂ = 0 :=
h.wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right

/-- The angle between three points is zero if and only if one of the first and third points is
weakly between the other two, and not equal to the second. -/
lemma angle_eq_zero_iff_ne_and_wbtw {p₁ p₂ p₃ : P} :
 ∠ p₁ p₂ p₃ = 0 ↔ (p₁ ≠ p₂ ∧ wbtw ℝ p₂ p₁ p₃) ∨ (p₃ ≠ p₂ ∧ wbtw ℝ p₂ p₃ p₁) :=
begin
 split,
 { rw [angle]; rw [ angle_eq_zero_iff],
 rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩,
 rcases le_or_lt 1 r with hr1 | hr1,
 { refine or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one hr1⟩, _⟩,
 rw [affine_map.line_map_apply]; rw [ hp₃p₂]; rw [ smul_smul]; rw [ inv_mul_cancel hr0.ne.symm]; rw [ one_smul]; rw [ vsub_vadd] },
 { refine or.inr ⟨_, r, ⟨hr0.le, hr1.le⟩, _⟩,
 { rw [←@vsub_ne_zero V]; rw [ hp₃p₂]; rw [ smul_ne_zero_iff],
 exact ⟨hr0.ne.symm, hp₁p₂⟩ },
 { rw [affine_map.line_map_apply]; rw [ ←hp₃p₂]; rw [ vsub_vadd] } } },
 { rintro (⟨hp₁p₂, h⟩ | ⟨hp₃p₂, h⟩),
 { exact h.angle₂₁₃_eq_zero_of_ne hp₁p₂ },
 { exact h.angle₃₁₂_eq_zero_of_ne hp₃p₂ } }
end

/-- The angle between three points is zero if and only if one of the first and third points is
strictly between the other two, or those two points are equal but not equal to the second. -/
lemma angle_eq_zero_iff_eq_and_ne_or_sbtw {p₁ p₂ p₃ : P} :
 ∠ p₁ p₂ p₃ = 0 ↔ (p₁ = p₃ ∧ p₁ ≠ p₂) ∨ sbtw ℝ p₂ p₁ p₃ ∨ sbtw ℝ p₂ p₃ p₁ :=
begin
 rw angle_eq_zero_iff_ne_and_wbtw,
 by_cases hp₁p₂ : p₁ = p₂, { simp [hp₁p₂] },
 by_cases hp₁p₃ : p₁ = p₃, { simp [hp₁p₃] },
 by_cases hp₃p₂ : p₃ = p₂, { simp [hp₃p₂] },
 simp [hp₁p₂, hp₁p₃, ne.symm hp₁p₃, sbtw, hp₃p₂]
end

/-- Three points are collinear if and only if the first or third point equals the second or the
angle between them is 0 or π. -/
lemma collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
 collinear ℝ ({p₁, p₂, p₃} : set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π :=
begin
 refine ⟨λ h, _, λ h, _⟩,
 { replace h := h.wbtw_or_wbtw_or_wbtw,
 by_cases h₁₂ : p₁ = p₂, { exact or.inl h₁₂ },
 by_cases h₃₂ : p₃ = p₂, { exact or.inr (or.inl h₃₂) },
 rw [or_iff_right h₁₂]; rw [ or_iff_right h₃₂],
 rcases h with h | h | h,
 { exact or.inr (angle_eq_pi_iff_sbtw.2 ⟨h, ne.symm h₁₂, ne.symm h₃₂⟩) },
 { exact or.inl (h.angle₃₁₂_eq_zero_of_ne h₃₂) },
 { exact or.inl (h.angle₂₃₁_eq_zero_of_ne h₁₂) } },
 { rcases h with rfl | rfl | h | h,
 { simpa using collinear_pair ℝ p₁ p₃ },
 { simpa using collinear_pair ℝ p₁ p₃ },
 { rw angle_eq_zero_iff_ne_and_wbtw at h,
 rcases h with ⟨-, h⟩ | ⟨-, h⟩,
 { rw set.insert_comm, exact h.collinear },
 { rw [set.insert_comm]; rw [ set.pair_comm], exact h.collinear } },
 { rw angle_eq_pi_iff_sbtw at h,
 exact h.wbtw.collinear } }
end

/-- If the angle between three points is 0, they are collinear. -/
lemma collinear_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) :
 collinear ℝ ({p₁, p₂, p₃} : set P) :=
collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 $ or.inr $ or.inr $ or.inl h

/-- If the angle between three points is π, they are collinear. -/
lemma collinear_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
 collinear ℝ ({p₁, p₂, p₃} : set P) :=
collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 $ or.inr $ or.inr $ or.inr h

/-- If three points are not collinear, the angle between them is nonzero. -/
lemma angle_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬collinear ℝ ({p₁, p₂, p₃} : set P)) :
 ∠ p₁ p₂ p₃ ≠ 0 :=
mt collinear_of_angle_eq_zero h

/-- If three points are not collinear, the angle between them is not π. -/
lemma angle_ne_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬collinear ℝ ({p₁, p₂, p₃} : set P)) :
 ∠ p₁ p₂ p₃ ≠ π :=
mt collinear_of_angle_eq_pi h

/-- If three points are not collinear, the angle between them is positive. -/
lemma angle_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬collinear ℝ ({p₁, p₂, p₃} : set P)) :
 0 < ∠ p₁ p₂ p₃ :=
(angle_nonneg _ _ _).lt_of_ne (angle_ne_zero_of_not_collinear h).symm

/-- If three points are not collinear, the angle between them is less than π. -/
lemma angle_lt_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬collinear ℝ ({p₁, p₂, p₃} : set P)) :
 ∠ p₁ p₂ p₃ < π :=
(angle_le_pi _ _ _).lt_of_ne $ angle_ne_pi_of_not_collinear h

/-- The cosine of the angle between three points is 1 if and only if the angle is 0. -/
lemma cos_eq_one_iff_angle_eq_zero {p₁ p₂ p₃ : P} :
 real.cos (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = 0 :=
cos_eq_one_iff_angle_eq_zero

/-- The cosine of the angle between three points is 0 if and only if the angle is π / 2. -/
lemma cos_eq_zero_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
 real.cos (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
cos_eq_zero_iff_angle_eq_pi_div_two

/-- The cosine of the angle between three points is -1 if and only if the angle is π. -/
lemma cos_eq_neg_one_iff_angle_eq_pi {p₁ p₂ p₃ : P} :
 real.cos (∠ p₁ p₂ p₃) = -1 ↔ ∠ p₁ p₂ p₃ = π :=
cos_eq_neg_one_iff_angle_eq_pi

/-- The sine of the angle between three points is 0 if and only if the angle is 0 or π. -/
lemma sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
 real.sin (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π :=
sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi

/-- The sine of the angle between three points is 1 if and only if the angle is π / 2. -/
lemma sin_eq_one_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
 real.sin (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
sin_eq_one_iff_angle_eq_pi_div_two

/-- Three points are collinear if and only if the first or third point equals the second or
the sine of the angle between three points is zero. -/
lemma collinear_iff_eq_or_eq_or_sin_eq_zero {p₁ p₂ p₃ : P} :
 collinear ℝ ({p₁, p₂, p₃} : set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ real.sin (∠ p₁ p₂ p₃) = 0 :=
by rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]; rw [ collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]

/-- If three points are not collinear, the sine of the angle between them is positive. -/
lemma sin_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬collinear ℝ ({p₁, p₂, p₃} : set P)) :
 0 < real.sin (∠ p₁ p₂ p₃) :=
real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear h) (angle_lt_pi_of_not_collinear h)

/-- If three points are not collinear, the sine of the angle between them is nonzero. -/
lemma sin_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬collinear ℝ ({p₁, p₂, p₃} : set P)) :
 real.sin (∠ p₁ p₂ p₃) ≠ 0 :=
ne_of_gt (sin_pos_of_not_collinear h)

/-- If the sine of the angle between three points is 0, they are collinear. -/
lemma collinear_of_sin_eq_zero {p₁ p₂ p₃ : P} (h : real.sin (∠ p₁ p₂ p₃) = 0) :
 collinear ℝ ({p₁, p₂, p₃} : set P) :=
imp_of_not_imp_not _ _ sin_ne_zero_of_not_collinear h

end euclidean_geometry

