/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.algebra.monoid

/-!
# Lie groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A Lie group is a group that is also a smooth manifold, in which the group operations of
multiplication and inversion are smooth maps. Smoothness of the group multiplication means that
multiplication is a smooth mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff a Lie group here is not
guaranteed to be second-countable (even though it can be proved it is Hausdorff). Note also that Lie
groups here are not necessarily finite dimensional.

## Main definitions and statements

* `lie_add_group I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `lie_group I G` : a Lie multiplicative group where `G` is a manifold on the model with
 corners `I`.
* `normed_space_lie_add_group` : a normed vector space over a nontrivially normed field
 is an additive Lie group.

## Implementation notes

A priori, a Lie group here is a manifold with corners.

The definition of Lie group cannot require `I : model_with_corners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, beause in the product situation,
the model space is `model_prod E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : model_with_corners 𝕜 E H`.
-/

noncomputable theory

open_locale manifold

/-- A Lie (additive) group is a group and a smooth manifold at the same time in which
the addition and negation operations are smooth. -/
-- See note [Design choices about smooth algebraic structures]
@[ancestor has_smooth_add]
class lie_add_group {𝕜 : Type*} [nontrivially_normed_field 𝕜]
 {H : Type*} [topological_space H]
 {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
 (G : Type*) [add_group G] [topological_space G] [charted_space H G]
 extends has_smooth_add I G : Prop :=
(smooth_neg : smooth I I (λ a:G, -a))

/-- A Lie group is a group and a smooth manifold at the same time in which
the multiplication and inverse operations are smooth. -/
-- See note [Design choices about smooth algebraic structures]
@[ancestor has_smooth_mul, to_additive]
class lie_group {𝕜 : Type*} [nontrivially_normed_field 𝕜]
 {H : Type*} [topological_space H]
 {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
 (G : Type*) [group G] [topological_space G] [charted_space H G]
 extends has_smooth_mul I G : Prop :=
(smooth_inv : smooth I I (λ a:G, a⁻¹))

section lie_group

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F] {J : model_with_corners 𝕜 F F}
{G : Type*} [topological_space G] [charted_space H G] [group G] [lie_group I G]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H' M]
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M' : Type*} [topological_space M'] [charted_space H'' M'] {n : ℕ∞}

section

variable (I)

@[to_additive]
lemma smooth_inv : smooth I I (λ x : G, x⁻¹) :=
lie_group.smooth_inv

/-- A Lie group is a topological group. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
@[to_additive
"An additive Lie group is an additive topological group. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]."]
lemma topological_group_of_lie_group : topological_group G :=
{ continuous_inv := (smooth_inv I).continuous,
 .. has_continuous_mul_of_smooth I }

end

@[to_additive]
lemma cont_mdiff_within_at.inv {f : M → G} {s : set M} {x₀ : M}
 (hf : cont_mdiff_within_at I' I n f s x₀) : cont_mdiff_within_at I' I n (λx, (f x)⁻¹) s x₀ :=
((smooth_inv I).of_le le_top).cont_mdiff_at.cont_mdiff_within_at.comp x₀ hf $ set.maps_to_univ _ _

@[to_additive]
lemma cont_mdiff_at.inv {f : M → G} {x₀ : M}
 (hf : cont_mdiff_at I' I n f x₀) : cont_mdiff_at I' I n (λx, (f x)⁻¹) x₀ :=
((smooth_inv I).of_le le_top).cont_mdiff_at.comp x₀ hf

@[to_additive]
lemma cont_mdiff_on.inv {f : M → G} {s : set M}
 (hf : cont_mdiff_on I' I n f s) : cont_mdiff_on I' I n (λx, (f x)⁻¹) s :=
λ x hx, (hf x hx).inv

@[to_additive]
lemma cont_mdiff.inv {f : M → G}
 (hf : cont_mdiff I' I n f) : cont_mdiff I' I n (λx, (f x)⁻¹) :=
λ x, (hf x).inv

@[to_additive]
lemma smooth_within_at.inv {f : M → G} {s : set M} {x₀ : M}
 (hf : smooth_within_at I' I f s x₀) : smooth_within_at I' I (λx, (f x)⁻¹) s x₀ :=
hf.inv

@[to_additive]
lemma smooth_at.inv {f : M → G} {x₀ : M}
 (hf : smooth_at I' I f x₀) : smooth_at I' I (λx, (f x)⁻¹) x₀ :=
hf.inv

@[to_additive]
lemma smooth_on.inv {f : M → G} {s : set M}
 (hf : smooth_on I' I f s) : smooth_on I' I (λx, (f x)⁻¹) s :=
hf.inv

@[to_additive]
lemma smooth.inv {f : M → G}
 (hf : smooth I' I f) : smooth I' I (λx, (f x)⁻¹) :=
hf.inv

@[to_additive]
lemma cont_mdiff_within_at.div {f g : M → G} {s : set M} {x₀ : M}
 (hf : cont_mdiff_within_at I' I n f s x₀) (hg : cont_mdiff_within_at I' I n g s x₀) :
 cont_mdiff_within_at I' I n (λ x, f x / g x) s x₀ :=
by { simp_rw div_eq_mul_inv, exact hf.mul hg.inv }

@[to_additive]
lemma cont_mdiff_at.div {f g : M → G} {x₀ : M}
 (hf : cont_mdiff_at I' I n f x₀) (hg : cont_mdiff_at I' I n g x₀) :
 cont_mdiff_at I' I n (λ x, f x / g x) x₀ :=
by { simp_rw div_eq_mul_inv, exact hf.mul hg.inv }

@[to_additive]
lemma cont_mdiff_on.div {f g : M → G} {s : set M}
 (hf : cont_mdiff_on I' I n f s) (hg : cont_mdiff_on I' I n g s) :
 cont_mdiff_on I' I n (λ x, f x / g x) s :=
by { simp_rw div_eq_mul_inv, exact hf.mul hg.inv }

@[to_additive]
lemma cont_mdiff.div {f g : M → G}
 (hf : cont_mdiff I' I n f) (hg : cont_mdiff I' I n g) :
 cont_mdiff I' I n (λ x, f x / g x) :=
by { simp_rw div_eq_mul_inv, exact hf.mul hg.inv }

@[to_additive]
lemma smooth_within_at.div {f g : M → G} {s : set M} {x₀ : M}
 (hf : smooth_within_at I' I f s x₀) (hg : smooth_within_at I' I g s x₀) :
 smooth_within_at I' I (λ x, f x / g x) s x₀ :=
hf.div hg

@[to_additive]
lemma smooth_at.div {f g : M → G} {x₀ : M}
 (hf : smooth_at I' I f x₀) (hg : smooth_at I' I g x₀) :
 smooth_at I' I (λ x, f x / g x) x₀ :=
hf.div hg

@[to_additive]
lemma smooth_on.div {f g : M → G} {s : set M}
 (hf : smooth_on I' I f s) (hg : smooth_on I' I g s) : smooth_on I' I (f / g) s :=
hf.div hg

@[to_additive]
lemma smooth.div {f g : M → G}
 (hf : smooth I' I f) (hg : smooth I' I g) : smooth I' I (f / g) :=
hf.div hg

end lie_group

section prod_lie_group

/- Instance of product group -/
@[to_additive]
instance {𝕜 : Type*} [nontrivially_normed_field 𝕜] {H : Type*} [topological_space H]
 {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
 {G : Type*} [topological_space G] [charted_space H G] [group G] [lie_group I G]
 {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
 {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
 {G' : Type*} [topological_space G'] [charted_space H' G']
 [group G'] [lie_group I' G'] :
 lie_group (I.prod I') (G×G') :=
{ smooth_inv := smooth_fst.inv.prod_mk smooth_snd.inv,
 ..has_smooth_mul.prod _ _ _ _ }

end prod_lie_group

/-! ### Normed spaces are Lie groups -/

instance normed_space_lie_add_group {𝕜 : Type*} [nontrivially_normed_field 𝕜]
 {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] :
 lie_add_group (𝓘(𝕜, E)) E :=
{ smooth_add := smooth_iff.2 ⟨continuous_add, λ x y, cont_diff_add.cont_diff_on⟩,
 smooth_neg := smooth_iff.2 ⟨continuous_neg, λ x y, cont_diff_neg.cont_diff_on⟩,
 .. model_space_smooth }

