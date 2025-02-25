/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.algebra.structures

/-!
# Algebraic structures over smooth functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define instances of algebraic structures over smooth functions.
-/

noncomputable theory

open_locale manifold
open topological_space

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{N : Type*} [topological_space N] [charted_space H N]
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{N' : Type*} [topological_space N'] [charted_space H'' N']

namespace smooth_map

@[to_additive]
instance has_mul {G : Type*} [has_mul G] [topological_space G] [charted_space H' G]
 [has_smooth_mul I' G] :
 has_mul C^∞⟮I, N; I', G⟯ :=
⟨λ f g, ⟨f * g, f.smooth.mul g.smooth⟩⟩

@[simp, to_additive]
lemma coe_mul {G : Type*} [has_mul G] [topological_space G] [charted_space H' G]
 [has_smooth_mul I' G] (f g : C^∞⟮I, N; I', G⟯) :
 ⇑(f * g) = f * g := rfl

@[simp, to_additive] lemma mul_comp {G : Type*} [has_mul G] [topological_space G]
 [charted_space H' G] [has_smooth_mul I' G] (f g : C^∞⟮I'', N'; I', G⟯) (h : C^∞⟮I, N; I'', N'⟯) :
(f * g).comp h = (f.comp h) * (g.comp h) :=
by ext; simp only [cont_mdiff_map.comp_apply, coe_mul, pi.mul_apply]

@[to_additive]
instance has_one {G : Type*} [monoid G] [topological_space G] [charted_space H' G] :
 has_one C^∞⟮I, N; I', G⟯ :=
⟨cont_mdiff_map.const (1 : G)⟩

@[simp, to_additive]
lemma coe_one {G : Type*} [monoid G] [topological_space G] [charted_space H' G] :
 ⇑(1 : C^∞⟮I, N; I', G⟯) = 1 := rfl

section group_structure

/-!
### Group structure

In this section we show that smooth functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/

@[to_additive]
instance semigroup {G : Type*} [semigroup G] [topological_space G]
 [charted_space H' G] [has_smooth_mul I' G] :
 semigroup C^∞⟮I, N; I', G⟯ :=
{ mul_assoc := λ a b c, by ext; exact mul_assoc _ _ _,
 ..smooth_map.has_mul}

@[to_additive]
instance monoid {G : Type*} [monoid G] [topological_space G]
 [charted_space H' G] [has_smooth_mul I' G] :
 monoid C^∞⟮I, N; I', G⟯ :=
{ one_mul := λ a, by ext; exact one_mul _,
 mul_one := λ a, by ext; exact mul_one _,
 ..smooth_map.semigroup,
 ..smooth_map.has_one }

/-- Coercion to a function as an `monoid_hom`. Similar to `monoid_hom.coe_fn`. -/
@[to_additive "Coercion to a function as an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn`.",
 simps]
def coe_fn_monoid_hom {G : Type*} [monoid G] [topological_space G]
 [charted_space H' G] [has_smooth_mul I' G] : C^∞⟮I, N; I', G⟯ →* (N → G) :=
{ to_fun := coe_fn, map_one' := coe_one, map_mul' := coe_mul }

variables (I N)

/-- For a manifold `N` and a smooth homomorphism `φ` between Lie groups `G'`, `G''`, the
'left-composition-by-`φ`' group homomorphism from `C^∞⟮I, N; I', G'⟯` to `C^∞⟮I, N; I'', G''⟯`. -/
@[to_additive "For a manifold `N` and a smooth homomorphism `φ` between additive Lie groups `G'`,
`G''`, the 'left-composition-by-`φ`' group homomorphism from `C^∞⟮I, N; I', G'⟯` to
`C^∞⟮I, N; I'', G''⟯`."]
def comp_left_monoid_hom
 {G' : Type*} [monoid G'] [topological_space G'] [charted_space H' G'] [has_smooth_mul I' G']
 {G'' : Type*} [monoid G''] [topological_space G''] [charted_space H'' G'']
 [has_smooth_mul I'' G''] (φ : G' →* G'') (hφ : smooth I' I'' φ) :
 C^∞⟮I, N; I', G'⟯ →* C^∞⟮I, N; I'', G''⟯ :=
{ to_fun := λ f, ⟨φ ∘ f, λ x, (hφ.smooth _).comp x (f.cont_mdiff x)⟩,
 map_one' := by ext x; show φ 1 = 1; simp,
 map_mul' := λ f g, by ext x; show φ (f x * g x) = φ (f x) * φ (g x); simp }

variables (I') {N}

/-- For a Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction' group homomorphism from
`C^∞⟮I, V; I', G⟯` to `C^∞⟮I, U; I', G⟯`. -/
@[to_additive "For an additive Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction' group
homomorphism from `C^∞⟮I, V; I', G⟯` to `C^∞⟮I, U; I', G⟯`."]
def restrict_monoid_hom
 (G : Type*) [monoid G] [topological_space G] [charted_space H' G] [has_smooth_mul I' G]
 {U V : opens N} (h : U ≤ V) :
 C^∞⟮I, V; I', G⟯ →* C^∞⟮I, U; I', G⟯ :=
{ to_fun := λ f, ⟨f ∘ set.inclusion h, f.smooth.comp (smooth_inclusion h)⟩,
 map_one' := rfl,
 map_mul' := λ f g, rfl }

variables {I N I' N'}

@[to_additive]
instance comm_monoid {G : Type*} [comm_monoid G] [topological_space G]
 [charted_space H' G] [has_smooth_mul I' G] :
 comm_monoid C^∞⟮I, N; I', G⟯ :=
{ mul_comm := λ a b, by ext; exact mul_comm _ _,
 ..smooth_map.monoid,
 ..smooth_map.has_one }

@[to_additive]
instance group {G : Type*} [group G] [topological_space G]
 [charted_space H' G] [lie_group I' G] :
 group C^∞⟮I, N; I', G⟯ :=
{ inv := λ f, ⟨λ x, (f x)⁻¹, f.smooth.inv⟩,
 mul_left_inv := λ a, by ext; exact mul_left_inv _,
 div := λ f g, ⟨f / g, f.smooth.div g.smooth⟩,
 div_eq_mul_inv := λ f g, by ext; exact div_eq_mul_inv _ _,
 .. smooth_map.monoid }

@[simp, to_additive]
lemma coe_inv {G : Type*} [group G] [topological_space G]
 [charted_space H' G] [lie_group I' G] (f : C^∞⟮I, N; I', G⟯) :
 ⇑f⁻¹ = f⁻¹ := rfl

@[simp, to_additive]
lemma coe_div {G : Type*} [group G] [topological_space G]
 [charted_space H' G] [lie_group I' G] (f g : C^∞⟮I, N; I', G⟯) :
 ⇑(f / g) = f / g :=
rfl

@[to_additive]
instance comm_group {G : Type*} [comm_group G] [topological_space G]
 [charted_space H' G] [lie_group I' G] :
 comm_group C^∞⟮I, N; I', G⟯ :=
{ ..smooth_map.group,
 ..smooth_map.comm_monoid }

end group_structure

section ring_structure

/-!
### Ring stucture

In this section we show that smooth functions valued in a smooth ring `R` inherit a ring structure
under pointwise multiplication.
-/

instance semiring {R : Type*} [semiring R] [topological_space R]
 [charted_space H' R] [smooth_ring I' R] :
 semiring C^∞⟮I, N; I', R⟯ :=
{ left_distrib := λ a b c, by ext; exact left_distrib _ _ _,
 right_distrib := λ a b c, by ext; exact right_distrib _ _ _,
 zero_mul := λ a, by ext; exact zero_mul _,
 mul_zero := λ a, by ext; exact mul_zero _,
 ..smooth_map.add_comm_monoid,
 ..smooth_map.monoid }

instance ring {R : Type*} [ring R] [topological_space R]
 [charted_space H' R] [smooth_ring I' R] :
 ring C^∞⟮I, N; I', R⟯ :=
{ ..smooth_map.semiring,
 ..smooth_map.add_comm_group, }

instance comm_ring {R : Type*} [comm_ring R] [topological_space R]
 [charted_space H' R] [smooth_ring I' R] :
 comm_ring C^∞⟮I, N; I', R⟯ :=
{ ..smooth_map.semiring,
 ..smooth_map.add_comm_group,
 ..smooth_map.comm_monoid,}

variables (I N)

/-- For a manifold `N` and a smooth homomorphism `φ` between smooth rings `R'`, `R''`, the
'left-composition-by-`φ`' ring homomorphism from `C^∞⟮I, N; I', R'⟯` to `C^∞⟮I, N; I'', R''⟯`. -/
def comp_left_ring_hom
 {R' : Type*} [ring R'] [topological_space R'] [charted_space H' R'] [smooth_ring I' R']
 {R'' : Type*} [ring R''] [topological_space R''] [charted_space H'' R''] [smooth_ring I'' R'']
 (φ : R' →+* R'') (hφ : smooth I' I'' φ) :
 C^∞⟮I, N; I', R'⟯ →+* C^∞⟮I, N; I'', R''⟯ :=
{ to_fun := λ f, ⟨φ ∘ f, λ x, (hφ.smooth _).comp x (f.cont_mdiff x)⟩,
 .. smooth_map.comp_left_monoid_hom I N φ.to_monoid_hom hφ,
 .. smooth_map.comp_left_add_monoid_hom I N φ.to_add_monoid_hom hφ }

variables (I') {N}

/-- For a "smooth ring" `R` and open sets `U ⊆ V` in `N`, the "restriction" ring homomorphism from
`C^∞⟮I, V; I', R⟯` to `C^∞⟮I, U; I', R⟯`. -/
def restrict_ring_hom
 (R : Type*) [ring R] [topological_space R] [charted_space H' R] [smooth_ring I' R]
 {U V : opens N} (h : U ≤ V) :
 C^∞⟮I, V; I', R⟯ →+* C^∞⟮I, U; I', R⟯ :=
{ to_fun := λ f, ⟨f ∘ set.inclusion h, f.smooth.comp (smooth_inclusion h)⟩,
 .. smooth_map.restrict_monoid_hom I I' R h,
 .. smooth_map.restrict_add_monoid_hom I I' R h }

variables {I N I' N'}

/-- Coercion to a function as a `ring_hom`. -/
@[simps]
def coe_fn_ring_hom {R : Type*} [comm_ring R] [topological_space R]
 [charted_space H' R] [smooth_ring I' R] : C^∞⟮I, N; I', R⟯ →+* (N → R) :=
{ to_fun := coe_fn,
 ..(coe_fn_monoid_hom : C^∞⟮I, N; I', R⟯ →* _),
 ..(coe_fn_add_monoid_hom : C^∞⟮I, N; I', R⟯ →+ _) }

/-- `function.eval` as a `ring_hom` on the ring of smooth functions. -/
def eval_ring_hom {R : Type*} [comm_ring R] [topological_space R]
 [charted_space H' R] [smooth_ring I' R] (n : N) : C^∞⟮I, N; I', R⟯ →+* R :=
(pi.eval_ring_hom _ n : (N → R) →+* R).comp smooth_map.coe_fn_ring_hom

end ring_structure

section module_structure

/-!
### Semiodule stucture

In this section we show that smooth functions valued in a vector space `M` over a normed
field `𝕜` inherit a vector space structure.
-/

instance has_smul {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V] :
 has_smul 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
⟨λ r f, ⟨r • f, smooth_const.smul f.smooth⟩⟩

@[simp]
lemma coe_smul {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V]
 (r : 𝕜) (f : C^∞⟮I, N; 𝓘(𝕜, V), V⟯) :
 ⇑(r • f) = r • f := rfl

@[simp] lemma smul_comp {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V]
 (r : 𝕜) (g : C^∞⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^∞⟮I, N; I'', N'⟯) :
(r • g).comp h = r • (g.comp h) := rfl

instance module {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V] :
 module 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
function.injective.module 𝕜 coe_fn_add_monoid_hom cont_mdiff_map.coe_inj coe_smul

/-- Coercion to a function as a `linear_map`. -/
@[simps]
def coe_fn_linear_map {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V] :
C^∞⟮I, N; 𝓘(𝕜, V), V⟯ →ₗ[𝕜] (N → V) :=
{ to_fun := coe_fn,
 map_smul' := coe_smul,
 ..(coe_fn_add_monoid_hom : C^∞⟮I, N; 𝓘(𝕜, V), V⟯ →+ _) }

end module_structure

section algebra_structure

/-!
### Algebra structure

In this section we show that smooth functions valued in a normed algebra `A` over a normed field `𝕜`
inherit an algebra structure.
-/

variables {A : Type*} [normed_ring A] [normed_algebra 𝕜 A] [smooth_ring 𝓘(𝕜, A) A]

/-- Smooth constant functions as a `ring_hom`. -/
def C : 𝕜 →+* C^∞⟮I, N; 𝓘(𝕜, A), A⟯ :=
{ to_fun := λ c : 𝕜, ⟨λ x, ((algebra_map 𝕜 A) c), smooth_const⟩,
 map_one' := by ext x; exact (algebra_map 𝕜 A).map_one,
 map_mul' := λ c₁ c₂, by ext x; exact (algebra_map 𝕜 A).map_mul _ _,
 map_zero' := by ext x; exact (algebra_map 𝕜 A).map_zero,
 map_add' := λ c₁ c₂, by ext x; exact (algebra_map 𝕜 A).map_add _ _ }

instance algebra : algebra 𝕜 C^∞⟮I, N; 𝓘(𝕜, A), A⟯ :=
{ smul := λ r f,
 ⟨r • f, smooth_const.smul f.smooth⟩,
 to_ring_hom := smooth_map.C,
 commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
 smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _,
 ..smooth_map.semiring }

/-- Coercion to a function as an `alg_hom`. -/
@[simps]
def coe_fn_alg_hom : C^∞⟮I, N; 𝓘(𝕜, A), A⟯ →ₐ[𝕜] (N → A) :=
{ to_fun := coe_fn,
 commutes' := λ r, rfl,
 -- `..(smooth_map.coe_fn_ring_hom : C^∞⟮I, N; 𝓘(𝕜, A), A⟯ →+* _)` times out for some reason
 map_zero' := smooth_map.coe_zero,
 map_one' := smooth_map.coe_one,
 map_add' := smooth_map.coe_add,
 map_mul' := smooth_map.coe_mul }

end algebra_structure

section module_over_continuous_functions

/-!
### Structure as module over scalar functions

If `V` is a module over `𝕜`, then we show that the space of smooth functions from `N` to `V`
is naturally a vector space over the ring of smooth functions from `N` to `𝕜`. -/

instance has_smul' {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V] :
 has_smul C^∞⟮I, N; 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
⟨λ f g, ⟨λ x, (f x) • (g x), (smooth.smul f.2 g.2)⟩⟩

@[simp] lemma smul_comp' {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V]
 (f : C^∞⟮I'', N'; 𝕜⟯) (g : C^∞⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^∞⟮I, N; I'', N'⟯) :
(f • g).comp h = (f.comp h) • (g.comp h) := rfl

instance module' {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V] :
 module C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
{ smul := (•),
 smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
 add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
 mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
 one_smul := λ f, by ext x; exact one_smul 𝕜 (f x),
 zero_smul := λ f, by ext x; exact zero_smul _ _,
 smul_zero := λ r, by ext x; exact smul_zero _, }

end module_over_continuous_functions

end smooth_map

