/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import topology.order.lattice
import analysis.normed.group.basic
import algebra.order.lattice_group

/-!
# Normed lattice ordered groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Motivated by the theory of Banach Lattices, we then define `normed_lattice_add_comm_group` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/

/-!
### Normed lattice ordered groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/

local notation (name := abs) `|`a`|` := abs a

section solid_norm

/-- Let `α` be an `add_comm_group` with a `lattice` structure. A norm on `α` is *solid* if, for `a`
and `b` in `α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `‖a‖ ≤ ‖b‖`.
-/
class has_solid_norm (α : Type*) [normed_add_comm_group α] [lattice α] : Prop :=
(solid : ∀ ⦃x y : α⦄, |x| ≤ |y| → ‖x‖ ≤ ‖y‖)

variables {α : Type*} [normed_add_comm_group α] [lattice α] [has_solid_norm α]

lemma norm_le_norm_of_abs_le_abs  {a b : α} (h : |a| ≤ |b|) : ‖a‖ ≤ ‖b‖ := has_solid_norm.solid h

/-- If `α` has a solid norm, then the balls centered at the origin of `α` are solid sets. -/
lemma lattice_ordered_add_comm_group.is_solid_ball (r : ℝ) :
  lattice_ordered_add_comm_group.is_solid (metric.ball (0 : α) r) :=
λ _ hx _ hxy, mem_ball_zero_iff.mpr ((has_solid_norm.solid hxy).trans_lt (mem_ball_zero_iff.mp hx))

instance : has_solid_norm ℝ := ⟨λ _ _, id⟩

instance : has_solid_norm ℚ := ⟨λ _ _ _, by simpa only [norm, ← rat.cast_abs, rat.cast_le]⟩

end solid_norm

/--
Let `α` be a normed commutative group equipped with a partial order covariant with addition, with
respect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in
`α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `‖a‖ ≤ ‖b‖`. Then `α` is
said to be a normed lattice ordered group.
-/
class normed_lattice_add_comm_group (α : Type*)
  extends normed_add_comm_group α, lattice α, has_solid_norm α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

instance : normed_lattice_add_comm_group ℝ :=
{ add_le_add_left := λ _ _ h _, add_le_add le_rfl h,}

/--
A normed lattice ordered group is an ordered additive commutative group
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_to_ordered_add_comm_group {α : Type*}
  [h : normed_lattice_add_comm_group α] : ordered_add_comm_group α := { ..h }

variables {α : Type*} [normed_lattice_add_comm_group α]
open lattice_ordered_comm_group has_solid_norm

lemma dual_solid (a b : α) (h: b⊓-b ≤ a⊓-a) : ‖a‖ ≤ ‖b‖ :=
begin
  apply solid,
  rw abs_eq_sup_neg,
  nth_rewrite 0 ← neg_neg a,
  rw ← neg_inf_eq_sup_neg,
  rw abs_eq_sup_neg,
  nth_rewrite 0 ← neg_neg b,
  rwa [← neg_inf_eq_sup_neg, neg_le_neg_iff, @inf_comm _ _ _ b, @inf_comm _ _ _ a],
end

/--
Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
@[priority 100] -- see Note [lower instance priority]
instance : normed_lattice_add_comm_group αᵒᵈ :=
{ solid := dual_solid,
  ..order_dual.ordered_add_comm_group, ..order_dual.normed_add_comm_group }

lemma norm_abs_eq_norm (a : α) : ‖|a|‖ = ‖a‖ :=
(solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)

lemma norm_inf_sub_inf_le_add_norm (a b c d : α) : ‖a ⊓ b - c ⊓ d‖ ≤ ‖a - c‖ + ‖b - d‖ :=
begin
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)],
  refine le_trans (solid _) (norm_add_le (|a - c|) (|b - d|)),
  rw abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d))),
  calc |a ⊓ b - c ⊓ d| =
    |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| : by rw sub_add_sub_cancel
  ... ≤ |a ⊓ b - c ⊓ b| + |c ⊓ b - c ⊓ d| : abs_add_le _ _
  ... ≤ |a -c| + |b - d| : by
    { apply add_le_add,
      { exact abs_inf_sub_inf_le_abs _ _ _, },
      { rw [@inf_comm _ _ c, @inf_comm _ _ c],
        exact abs_inf_sub_inf_le_abs _ _ _, } },
end

lemma norm_sup_sub_sup_le_add_norm (a b c d : α) : ‖a ⊔ b - (c ⊔ d)‖ ≤ ‖a - c‖ + ‖b - d‖ :=
begin
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)],
  refine le_trans (solid _) (norm_add_le (|a - c|) (|b - d|)),
  rw abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d))),
  calc |a ⊔ b - (c ⊔ d)| =
    |a ⊔ b - (c ⊔ b) + (c ⊔ b - (c ⊔ d))| : by rw sub_add_sub_cancel
  ... ≤ |a ⊔ b - (c ⊔ b)| + |c ⊔ b - (c ⊔ d)| : abs_add_le _ _
  ... ≤ |a -c| + |b - d| : by
    { apply add_le_add,
      { exact abs_sup_sub_sup_le_abs _ _ _, },
      { rw [@sup_comm _ _ c, @sup_comm _ _ c],
        exact abs_sup_sub_sup_le_abs _ _ _, } },
end

lemma norm_inf_le_add (x y : α) : ‖x ⊓ y‖ ≤ ‖x‖ + ‖y‖ :=
begin
  have h : ‖x ⊓ y - 0 ⊓ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_inf_sub_inf_le_add_norm x y 0 0,
  simpa only [inf_idem, sub_zero] using h,
end

lemma norm_sup_le_add (x y : α) : ‖x ⊔ y‖ ≤ ‖x‖ + ‖y‖ :=
begin
  have h : ‖x ⊔ y - 0 ⊔ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_sup_sub_sup_le_add_norm x y 0 0,
  simpa only [sup_idem, sub_zero] using h,
end

/--
Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_has_continuous_inf : has_continuous_inf α :=
begin
  refine ⟨continuous_iff_continuous_at.2 $ λ q, tendsto_iff_norm_tendsto_zero.2 $ _⟩,
  have : ∀ p : α × α, ‖p.1 ⊓ p.2 - q.1 ⊓ q.2‖ ≤ ‖p.1 - q.1‖ + ‖p.2 - q.2‖,
    from λ _, norm_inf_sub_inf_le_add_norm _ _ _ _,
  refine squeeze_zero (λ e, norm_nonneg _) this _,
  convert (((continuous_fst.tendsto q).sub tendsto_const_nhds).norm).add
        (((continuous_snd.tendsto q).sub tendsto_const_nhds).norm),
  simp,
end

@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_has_continuous_sup {α : Type*}
  [normed_lattice_add_comm_group α] :
  has_continuous_sup α :=
order_dual.has_continuous_sup αᵒᵈ

/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_topological_lattice : topological_lattice α :=
topological_lattice.mk

lemma norm_abs_sub_abs (a b : α) :
  ‖ |a| - |b| ‖ ≤ ‖a-b‖ :=
solid (lattice_ordered_comm_group.abs_abs_sub_abs_le _ _)

lemma norm_sup_sub_sup_le_norm (x y z : α) : ‖x ⊔ z - (y ⊔ z)‖ ≤ ‖x - y‖ :=
solid (abs_sup_sub_sup_le_abs x y z)

lemma norm_inf_sub_inf_le_norm (x y z : α) : ‖x ⊓ z - (y ⊓ z)‖ ≤ ‖x - y‖ :=
solid (abs_inf_sub_inf_le_abs x y z)

lemma lipschitz_with_sup_right (z : α) : lipschitz_with 1 (λ x, x ⊔ z) :=
lipschitz_with.of_dist_le_mul $ λ x y, by
{ rw [nonneg.coe_one, one_mul, dist_eq_norm, dist_eq_norm], exact norm_sup_sub_sup_le_norm x y z, }

lemma lipschitz_with_pos : lipschitz_with 1 (has_pos_part.pos : α → α) :=
lipschitz_with_sup_right 0

lemma continuous_pos : continuous (has_pos_part.pos : α → α) :=
lipschitz_with.continuous lipschitz_with_pos

lemma continuous_neg' : continuous (has_neg_part.neg : α → α) :=
continuous_pos.comp continuous_neg

lemma is_closed_nonneg {E} [normed_lattice_add_comm_group E] : is_closed {x : E | 0 ≤ x} :=
begin
  suffices : {x : E | 0 ≤ x} = has_neg_part.neg ⁻¹' {(0 : E)},
  by { rw this, exact is_closed.preimage continuous_neg' is_closed_singleton, },
  ext1 x,
  simp only [set.mem_preimage, set.mem_singleton_iff, set.mem_set_of_eq, neg_eq_zero_iff],
end

lemma is_closed_le_of_is_closed_nonneg {G} [ordered_add_comm_group G] [topological_space G]
  [has_continuous_sub G] (h : is_closed {x : G | 0 ≤ x}) :
  is_closed {p : G × G | p.fst ≤ p.snd} :=
begin
  have : {p : G × G | p.fst ≤ p.snd} = (λ p : G × G, p.snd - p.fst) ⁻¹' {x : G | 0 ≤ x},
    by { ext1 p, simp only [sub_nonneg, set.preimage_set_of_eq], },
  rw this,
  exact is_closed.preimage (continuous_snd.sub continuous_fst) h,
end

@[priority 100]  -- See note [lower instance priority]
instance normed_lattice_add_comm_group.order_closed_topology {E} [normed_lattice_add_comm_group E] :
  order_closed_topology E :=
⟨is_closed_le_of_is_closed_nonneg is_closed_nonneg⟩
