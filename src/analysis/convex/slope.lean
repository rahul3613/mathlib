/-
Copyright (c) 2021 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Malo Jaffré
-/
import analysis.convex.function
import tactic.field_simp
import tactic.linarith

/-!
# Slopes of convex functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file relates convexity/concavity of functions in a linearly ordered field and the monotonicity
of their slopes.

The main use is to show convexity/concavity from monotonicity of the derivative.
-/

variables {𝕜 : Type*} [linear_ordered_field 𝕜] {s : set 𝕜} {f : 𝕜 → 𝕜}

/-- If `f : 𝕜 → 𝕜` is convex, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
lemma convex_on.slope_mono_adjacent (hf : convex_on 𝕜 s f)
 {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
begin
 have hxz := hxy.trans hyz,
 rw ←sub_pos at hxy hxz hyz,
 suffices : f y / (y - x) + f y / (z - y) ≤ f x / (y - x) + f z / (z - y),
 { ring_nf at this ⊢, linarith },
 set a := (z - y) / (z - x),
 set b := (y - x) / (z - x),
 have hy : a • x + b • z = y, by { field_simp, rw div_eq_iff; [ring, linarith] },
 have key, from
 hf.2 hx hz
 (show 0 ≤ a, by apply div_nonneg; linarith)
 (show 0 ≤ b, by apply div_nonneg; linarith)
 (show a + b = 1, by { field_simp, rw div_eq_iff; [ring, linarith] }),
 rw hy at key,
 replace key := mul_le_mul_of_nonneg_left key hxz.le,
 field_simp [hxy.ne', hyz.ne', hxz.ne', mul_comm (z - x) _] at key ⊢,
 rw div_le_div_right,
 { linarith },
 { nlinarith }
end

/-- If `f : 𝕜 → 𝕜` is concave, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on.slope_anti_adjacent (hf : concave_on 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
 (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
begin
 rw [←neg_le_neg_iff]; rw [ ←neg_sub_neg (f x)]; rw [ ←neg_sub_neg (f y)],
 simp_rw [←pi.neg_apply, ←neg_div, neg_sub],
 exact convex_on.slope_mono_adjacent hf.neg hx hz hxy hyz,
end

/-- If `f : 𝕜 → 𝕜` is strictly convex, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
lemma strict_convex_on.slope_strict_mono_adjacent (hf : strict_convex_on 𝕜 s f)
 {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (f y - f x) / (y - x) < (f z - f y) / (z - y) :=
begin
 have hxz := hxy.trans hyz,
 have hxz' := hxz.ne,
 rw ←sub_pos at hxy hxz hyz,
 suffices : f y / (y - x) + f y / (z - y) < f x / (y - x) + f z / (z - y),
 { ring_nf at this ⊢, linarith },
 set a := (z - y) / (z - x),
 set b := (y - x) / (z - x),
 have hy : a • x + b • z = y, by { field_simp, rw div_eq_iff; [ring, linarith] },
 have key, from
 hf.2 hx hz hxz' (div_pos hyz hxz) (div_pos hxy hxz)
 (show a + b = 1, by { field_simp, rw div_eq_iff; [ring, linarith] }),
 rw hy at key,
 replace key := mul_lt_mul_of_pos_left key hxz,
 field_simp [hxy.ne', hyz.ne', hxz.ne', mul_comm (z - x) _] at key ⊢,
 rw div_lt_div_right,
 { linarith },
 { nlinarith }
end

/-- If `f : 𝕜 → 𝕜` is strictly concave, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
lemma strict_concave_on.slope_anti_adjacent (hf : strict_concave_on 𝕜 s f)
 {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
begin
 rw [←neg_lt_neg_iff]; rw [ ←neg_sub_neg (f x)]; rw [ ←neg_sub_neg (f y)],
 simp_rw [←pi.neg_apply, ←neg_div, neg_sub],
 exact strict_convex_on.slope_strict_mono_adjacent hf.neg hx hz hxy hyz,
end

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
less than the slope of the secant line of `f` on `[x, z]`, then `f` is convex. -/
lemma convex_on_of_slope_mono_adjacent (hs : convex 𝕜 s)
 (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
 (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
 convex_on 𝕜 s f :=
linear_order.convex_on_of_lt hs $ λ x hx z hz hxz a b ha hb hab,
begin
 let y := a * x + b * z,
 have hxy : x < y,
 { rw [← one_mul x]; rw [ ← hab]; rw [ add_mul],
 exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _ },
 have hyz : y < z,
 { rw [← one_mul z]; rw [ ← hab]; rw [ add_mul],
 exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _ },
 have : (f y - f x) * (z - y) ≤ (f z - f y) * (y - x),
 from (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz),
 have hxz : 0 < z - x, from sub_pos.2 (hxy.trans hyz),
 have ha : (z - y) / (z - x) = a,
 { rw [eq_comm] at hab; rw [ ← sub_eq_iff_eq_add'] at hab,
 simp_rw [div_eq_iff hxz.ne', y, ←hab], ring },
 have hb : (y - x) / (z - x) = b,
 { rw [eq_comm] at hab; rw [ ← sub_eq_iff_eq_add] at hab,
 simp_rw [div_eq_iff hxz.ne', y, ←hab], ring },
 rwa [sub_mul] at this; rwa [ sub_mul] at this; rwa [ sub_le_iff_le_add'] at this; rwa [ ← add_sub_assoc] at this; rwa [ le_sub_iff_add_le] at this; rwa [ ← mul_add] at this; rwa [ sub_add_sub_cancel] at this; rwa [ ← le_div_iff hxz] at this; rwa [ add_div] at this; rwa [ mul_div_assoc] at this; rwa [ mul_div_assoc] at this; rwa [ mul_comm (f x)] at this; rwa [ mul_comm (f z)] at this; rwa [ ha] at this; rwa [ hb] at this,
end

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
greater than the slope of the secant line of `f` on `[x, z]`, then `f` is concave. -/
lemma concave_on_of_slope_anti_adjacent (hs : convex 𝕜 s)
 (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
 (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) : concave_on 𝕜 s f :=
begin
 rw ←neg_convex_on_iff,
 refine convex_on_of_slope_mono_adjacent hs (λ x y z hx hz hxy hyz, _),
 rw ←neg_le_neg_iff,
 simp_rw [←neg_div, neg_sub, pi.neg_apply, neg_sub_neg],
 exact hf hx hz hxy hyz,
end

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly less than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly convex. -/
lemma strict_convex_on_of_slope_strict_mono_adjacent (hs : convex 𝕜 s)
 (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
 (f y - f x) / (y - x) < (f z - f y) / (z - y)) :
 strict_convex_on 𝕜 s f :=
linear_order.strict_convex_on_of_lt hs $ λ x hx z hz hxz a b ha hb hab,
begin
 let y := a * x + b * z,
 have hxy : x < y,
 { rw [← one_mul x]; rw [ ← hab]; rw [ add_mul],
 exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _ },
 have hyz : y < z,
 { rw [← one_mul z]; rw [ ← hab]; rw [ add_mul],
 exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _ },
 have : (f y - f x) * (z - y) < (f z - f y) * (y - x),
 from (div_lt_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz),
 have hxz : 0 < z - x, from sub_pos.2 (hxy.trans hyz),
 have ha : (z - y) / (z - x) = a,
 { rw [eq_comm] at hab; rw [ ← sub_eq_iff_eq_add'] at hab,
 simp_rw [div_eq_iff hxz.ne', y, ←hab], ring },
 have hb : (y - x) / (z - x) = b,
 { rw [eq_comm] at hab; rw [ ← sub_eq_iff_eq_add] at hab,
 simp_rw [div_eq_iff hxz.ne', y, ←hab], ring },
 rwa [sub_mul] at this; rwa [ sub_mul] at this; rwa [ sub_lt_iff_lt_add'] at this; rwa [ ← add_sub_assoc] at this; rwa [ lt_sub_iff_add_lt] at this; rwa [ ← mul_add] at this; rwa [ sub_add_sub_cancel] at this; rwa [ ← lt_div_iff hxz] at this; rwa [ add_div] at this; rwa [ mul_div_assoc] at this; rwa [ mul_div_assoc] at this; rwa [ mul_comm (f x)] at this; rwa [ mul_comm (f z)] at this; rwa [ ha] at this; rwa [ hb] at this,
end

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly greater than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly concave.
-/
lemma strict_concave_on_of_slope_strict_anti_adjacent (hs : convex 𝕜 s)
 (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
 (f z - f y) / (z - y) < (f y - f x) / (y - x)) : strict_concave_on 𝕜 s f :=
begin
 rw ←neg_strict_convex_on_iff,
 refine strict_convex_on_of_slope_strict_mono_adjacent hs (λ x y z hx hz hxy hyz, _),
 rw ←neg_lt_neg_iff,
 simp_rw [←neg_div, neg_sub, pi.neg_apply, neg_sub_neg],
 exact hf hx hz hxy hyz,
end

/-- A function `f : 𝕜 → 𝕜` is convex iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
lemma convex_on_iff_slope_mono_adjacent :
 convex_on 𝕜 s f ↔ convex 𝕜 s ∧
 ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z →
 (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
⟨λ h, ⟨h.1, λ x y z, h.slope_mono_adjacent⟩, λ h, convex_on_of_slope_mono_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is concave iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on_iff_slope_anti_adjacent :
 concave_on 𝕜 s f ↔ convex 𝕜 s ∧
 ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z →
 (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
⟨λ h, ⟨h.1, λ x y z, h.slope_anti_adjacent⟩, λ h, concave_on_of_slope_anti_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is strictly convex iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
lemma strict_convex_on_iff_slope_strict_mono_adjacent :
 strict_convex_on 𝕜 s f ↔ convex 𝕜 s ∧
 ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z →
 (f y - f x) / (y - x) < (f z - f y) / (z - y) :=
⟨λ h, ⟨h.1, λ x y z, h.slope_strict_mono_adjacent⟩,
 λ h, strict_convex_on_of_slope_strict_mono_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is strictly concave iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
lemma strict_concave_on_iff_slope_strict_anti_adjacent :
 strict_concave_on 𝕜 s f ↔ convex 𝕜 s ∧
 ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z →
 (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
⟨λ h, ⟨h.1, λ x y z, h.slope_anti_adjacent⟩,
 λ h, strict_concave_on_of_slope_strict_anti_adjacent h.1 h.2⟩

lemma convex_on.secant_mono_aux1 (hf : convex_on 𝕜 s f)
 {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (z - x) * f y ≤ (z - y) * f x + (y - x) * f z :=
begin
 have hxy' : 0 < y - x := by linarith,
 have hyz' : 0 < z - y := by linarith,
 have hxz' : 0 < z - x := by linarith,
 rw ← le_div_iff' hxz',
 have ha : 0 ≤ (z - y) / (z - x) := by positivity,
 have hb : 0 ≤ (y - x) / (z - x) := by positivity,
 calc f y = f ((z - y) / (z - x) * x + (y - x) / (z - x) * z) : _
 ... ≤ (z - y) / (z - x) * f x + (y - x) / (z - x) * f z : hf.2 hx hz ha hb _
 ... = ((z - y) * f x + (y - x) * f z) / (z - x) : _,
 { congr' 1,
 field_simp [hxy'.ne', hyz'.ne', hxz'.ne'],
 ring },
 { field_simp [hxy'.ne', hyz'.ne', hxz'.ne'] },
 { field_simp [hxy'.ne', hyz'.ne', hxz'.ne'] }
end

lemma convex_on.secant_mono_aux2 (hf : convex_on 𝕜 s f)
 {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (f y - f x) / (y - x) ≤ (f z - f x) / (z - x) :=
begin
 have hxy' : 0 < y - x := by linarith,
 have hxz' : 0 < z - x := by linarith,
 rw div_le_div_iff hxy' hxz',
 linarith only [hf.secant_mono_aux1 hx hz hxy hyz],
end

lemma convex_on.secant_mono_aux3 (hf : convex_on 𝕜 s f)
 {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (f z - f x) / (z - x) ≤ (f z - f y) / (z - y) :=
begin
 have hyz' : 0 < z - y := by linarith,
 have hxz' : 0 < z - x := by linarith,
 rw div_le_div_iff hxz' hyz',
 linarith only [hf.secant_mono_aux1 hx hz hxy hyz],
end

lemma convex_on.secant_mono (hf : convex_on 𝕜 s f)
 {a x y : 𝕜} (ha : a ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x ≤ y) :
 (f x - f a) / (x - a) ≤ (f y - f a) / (y - a) :=
begin
 rcases eq_or_lt_of_le hxy with rfl | hxy,
 { simp },
 cases lt_or_gt_of_ne hxa with hxa hxa,
 { cases lt_or_gt_of_ne hya with hya hya,
 { convert hf.secant_mono_aux3 hx ha hxy hya using 1;
 rw ← neg_div_neg_eq;
 field_simp, },
 { convert hf.slope_mono_adjacent hx hy hxa hya using 1,
 rw ← neg_div_neg_eq;
 field_simp, } },
 { exact hf.secant_mono_aux2 ha hy hxa hxy, },
end

lemma strict_convex_on.secant_strict_mono_aux1 (hf : strict_convex_on 𝕜 s f)
 {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (z - x) * f y < (z - y) * f x + (y - x) * f z :=
begin
 have hxy' : 0 < y - x := by linarith,
 have hyz' : 0 < z - y := by linarith,
 have hxz' : 0 < z - x := by linarith,
 rw ← lt_div_iff' hxz',
 have ha : 0 < (z - y) / (z - x) := by positivity,
 have hb : 0 < (y - x) / (z - x) := by positivity,
 calc f y = f ((z - y) / (z - x) * x + (y - x) / (z - x) * z) : _
 ... < (z - y) / (z - x) * f x + (y - x) / (z - x) * f z : hf.2 hx hz (by linarith) ha hb _
 ... = ((z - y) * f x + (y - x) * f z) / (z - x) : _,
 { congr' 1,
 field_simp [hxy'.ne', hyz'.ne', hxz'.ne'],
 ring },
 { field_simp [hxy'.ne', hyz'.ne', hxz'.ne'] },
 { field_simp [hxy'.ne', hyz'.ne', hxz'.ne'] }
end

lemma strict_convex_on.secant_strict_mono_aux2 (hf : strict_convex_on 𝕜 s f)
 {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (f y - f x) / (y - x) < (f z - f x) / (z - x) :=
begin
 have hxy' : 0 < y - x := by linarith,
 have hxz' : 0 < z - x := by linarith,
 rw div_lt_div_iff hxy' hxz',
 linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz],
end

lemma strict_convex_on.secant_strict_mono_aux3 (hf : strict_convex_on 𝕜 s f)
 {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
 (f z - f x) / (z - x) < (f z - f y) / (z - y) :=
begin
 have hyz' : 0 < z - y := by linarith,
 have hxz' : 0 < z - x := by linarith,
 rw div_lt_div_iff hxz' hyz',
 linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz],
end

lemma strict_convex_on.secant_strict_mono (hf : strict_convex_on 𝕜 s f)
 {a x y : 𝕜} (ha : a ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x < y) :
 (f x - f a) / (x - a) < (f y - f a) / (y - a) :=
begin
 cases lt_or_gt_of_ne hxa with hxa hxa,
 { cases lt_or_gt_of_ne hya with hya hya,
 { convert hf.secant_strict_mono_aux3 hx ha hxy hya using 1;
 rw ← neg_div_neg_eq;
 field_simp, },
 { convert hf.slope_strict_mono_adjacent hx hy hxa hya using 1,
 rw ← neg_div_neg_eq;
 field_simp, } },
 { exact hf.secant_strict_mono_aux2 ha hy hxa hxy, },
end

lemma strict_concave_on.secant_strict_mono (hf : strict_concave_on 𝕜 s f)
 {a x y : 𝕜} (ha : a ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x < y) :
 (f y - f a) / (y - a) < (f x - f a) / (x - a) :=
begin
 have key := hf.neg.secant_strict_mono ha hx hy hxa hya hxy,
 simp only [pi.neg_apply] at key,
 rw ← neg_lt_neg_iff,
 convert key using 1; field_simp,
end

/-- If `f` is convex on a set `s` in a linearly ordered field, and `f x < f y` for two points
`x < y` in `s`, then `f` is strictly monotone on `s ∩ [y, ∞)`. -/
lemma convex_on.strict_mono_of_lt (hf : convex_on 𝕜 s f)
 {x y : 𝕜} (hx : x ∈ s) (hxy : x < y) (hxy' : f x < f y) :
 strict_mono_on f (s ∩ set.Ici y) :=
begin
 intros u hu v hv huv,
 have step1 : ∀ {z : 𝕜}, z ∈ s ∩ set.Ioi y → f y < f z,
 { refine λ z hz, hf.lt_right_of_left_lt hx hz.1 _ hxy',
 rw open_segment_eq_Ioo (hxy.trans hz.2),
 exact ⟨hxy, hz.2⟩ },
 rcases eq_or_lt_of_le hu.2 with rfl | hu2,
 { exact step1 ⟨hv.1, huv⟩ },
 { refine hf.lt_right_of_left_lt _ hv.1 _ (step1 ⟨hu.1, hu2⟩),
 { apply hf.1.segment_subset hx hu.1,
 rw segment_eq_Icc (hxy.le.trans hu.2),
 exact ⟨hxy.le, hu.2⟩ },
 { rw open_segment_eq_Ioo (hu2.trans huv),
 exact ⟨hu2, huv⟩ } },
end

