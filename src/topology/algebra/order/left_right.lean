/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.continuous_on

/-!
# Left and right continuity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove a few lemmas about left and right continuous functions:

* `continuous_within_at_Ioi_iff_Ici`: two definitions of right continuity
 (with `(a, ∞)` and with `[a, ∞)`) are equivalent;
* `continuous_within_at_Iio_iff_Iic`: two definitions of left continuity
 (with `(-∞, a)` and with `(-∞, a]`) are equivalent;
* `continuous_at_iff_continuous_left_right`, `continuous_at_iff_continuous_left'_right'` :
 a function is continuous at `a` if and only if it is left and right continuous at `a`.

## Tags

left continuous, right continuous
-/

open set filter
open_locale topology

section partial_order

variables {α β : Type*} [topological_space α] [partial_order α] [topological_space β]

lemma continuous_within_at_Ioi_iff_Ici {a : α} {f : α → β} :
 continuous_within_at f (Ioi a) a ↔ continuous_within_at f (Ici a) a :=
by simp only [← Ici_diff_left, continuous_within_at_diff_self]

lemma continuous_within_at_Iio_iff_Iic {a : α} {f : α → β} :
 continuous_within_at f (Iio a) a ↔ continuous_within_at f (Iic a) a :=
@continuous_within_at_Ioi_iff_Ici αᵒᵈ _ ‹topological_space α› _ _ _ f

lemma nhds_left'_le_nhds_ne (a : α) :
 𝓝[<] a ≤ 𝓝[≠] a :=
nhds_within_mono a (λ y hy, ne_of_lt hy)

lemma nhds_right'_le_nhds_ne (a : α) :
 𝓝[>] a ≤ 𝓝[≠] a :=
nhds_within_mono a (λ y hy, ne_of_gt hy)

end partial_order

section topological_space

variables {α β : Type*} [topological_space α] [linear_order α] [topological_space β]

lemma nhds_left_sup_nhds_right (a : α) :
 𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a :=
by rw [← nhds_within_union]; rw [ Iic_union_Ici]; rw [ nhds_within_univ]

lemma nhds_left'_sup_nhds_right (a : α) :
 𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a :=
by rw [← nhds_within_union]; rw [ Iio_union_Ici]; rw [ nhds_within_univ]

lemma nhds_left_sup_nhds_right' (a : α) :
 𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a :=
by rw [← nhds_within_union]; rw [ Iic_union_Ioi]; rw [ nhds_within_univ]

lemma nhds_left'_sup_nhds_right' (a : α) :
 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a :=
by rw [← nhds_within_union]; rw [ Iio_union_Ioi]

lemma continuous_at_iff_continuous_left_right {a : α} {f : α → β} :
 continuous_at f a ↔ continuous_within_at f (Iic a) a ∧ continuous_within_at f (Ici a) a :=
by simp only [continuous_within_at, continuous_at, ← tendsto_sup, nhds_left_sup_nhds_right]

lemma continuous_at_iff_continuous_left'_right' {a : α} {f : α → β} :
 continuous_at f a ↔ continuous_within_at f (Iio a) a ∧ continuous_within_at f (Ioi a) a :=
by rw [continuous_within_at_Ioi_iff_Ici]; rw [ continuous_within_at_Iio_iff_Iic]; rw [ continuous_at_iff_continuous_left_right]

end topological_space

