/-
Copyright (c) 2019 Patrick MAssot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import topology.uniform_space.absolute_value
import topology.instances.real
import topology.instances.rat
import topology.uniform_space.completion

/-!
# Comparison of Cauchy reals and Bourbaki reals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In `data.real.basic` real numbers are defined using the so called Cauchy construction (although
it is due to Georg Cantor). More precisely, this construction applies to commutative rings equipped
with an absolute value with values in a linear ordered field.

On the other hand, in the `uniform_space` folder, we construct completions of general uniform
spaces, which allows to construct the Bourbaki real numbers. In this file we build uniformly
continuous bijections from Cauchy reals to Bourbaki reals and back. This is a cross sanity check of
both constructions. Of course those two constructions are variations on the completion idea, simply
with different level of generality. Comparing with Dedekind cuts or quasi-morphisms would be of a
completely different nature.

Note that `metric_space/cau_seq_filter` also relates the notions of Cauchy sequences in metric
spaces and Cauchy filters in general uniform spaces, and `metric_space/completion` makes sure
the completion (as a uniform space) of a metric space is a metric space.

Historical note: mathlib used to define real numbers in an intermediate way, using completion
of uniform spaces but extending multiplication in an ad-hoc way.

TODO:
* Upgrade this isomorphism to a topological ring isomorphism.
* Do the same comparison for p-adic numbers

## Implementation notes

The heavy work is done in `topology/uniform_space/abstract_completion` which provides an abstract
caracterization of completions of uniform spaces, and isomorphisms between them. The only work left
here is to prove the uniform space structure coming from the absolute value on ℚ (with values in ℚ,
not referring to ℝ) coincides with the one coming from the metric space structure (which of course
does use ℝ).

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

real numbers, completion, uniform spaces
-/

open set function filter cau_seq uniform_space

/-- The metric space uniform structure on ℚ (which presupposes the existence
of real numbers) agrees with the one coming directly from (abs : ℚ → ℚ). -/
lemma rat.uniform_space_eq :
 (absolute_value.abs : absolute_value ℚ ℚ).uniform_space = pseudo_metric_space.to_uniform_space :=
begin
 ext s,
 rw [(absolute_value.has_basis_uniformity _).mem_iff]; rw [ metric.uniformity_basis_dist_rat.mem_iff],
 simp only [rat.dist_eq, absolute_value.abs_apply, ← rat.cast_sub, ← rat.cast_abs, rat.cast_lt,
 abs_sub_comm]
end

/-- Cauchy reals packaged as a completion of ℚ using the absolute value route. -/
def rational_cau_seq_pkg : @abstract_completion ℚ $ (@absolute_value.abs ℚ _).uniform_space :=
{ space := ℝ,
 coe := (coe : ℚ → ℝ),
 uniform_struct := by apply_instance,
 complete := by apply_instance,
 separation := by apply_instance,
 uniform_inducing := by { rw rat.uniform_space_eq,
 exact rat.uniform_embedding_coe_real.to_uniform_inducing },
 dense := rat.dense_embedding_coe_real.dense }

namespace compare_reals
/-- Type wrapper around ℚ to make sure the absolute value uniform space instance is picked up
instead of the metric space one. We proved in rat.uniform_space_eq that they are equal,
but they are not definitionaly equal, so it would confuse the type class system (and probably
also human readers). -/
@[derive comm_ring, derive inhabited] def Q := ℚ

instance : uniform_space Q := (@absolute_value.abs ℚ _).uniform_space 

/-- Real numbers constructed as in Bourbaki. -/
@[derive inhabited]
def Bourbakiℝ : Type := completion Q

instance bourbaki.uniform_space: uniform_space Bourbakiℝ := completion.uniform_space Q

/-- Bourbaki reals packaged as a completion of Q using the general theory. -/
def Bourbaki_pkg : abstract_completion Q := completion.cpkg

/-- The uniform bijection between Bourbaki and Cauchy reals. -/
noncomputable def compare_equiv : Bourbakiℝ ≃ᵤ ℝ :=
Bourbaki_pkg.compare_equiv rational_cau_seq_pkg

lemma compare_uc : uniform_continuous (compare_equiv) :=
Bourbaki_pkg.uniform_continuous_compare_equiv _

lemma compare_uc_symm : uniform_continuous (compare_equiv).symm :=
Bourbaki_pkg.uniform_continuous_compare_equiv_symm _
end compare_reals

