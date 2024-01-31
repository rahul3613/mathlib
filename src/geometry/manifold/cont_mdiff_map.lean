/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.cont_mdiff
import topology.continuous_function.basic

/-!
# Smooth bundled map

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the type `cont_mdiff_map` of `n` times continuously differentiable
bundled maps.
-/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(M : Type*) [topological_space M] [charted_space H M]
(M' : Type*) [topological_space M'] [charted_space H' M']
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H'']
{I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']
-- declare a manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N]
(n : ℕ∞)

/-- Bundled `n` times continuously differentiable maps. -/
def cont_mdiff_map := {f : M → M' // cont_mdiff I I' n f}

/-- Bundled smooth maps. -/
@[reducible] def smooth_map := cont_mdiff_map I I' M M' ⊤

localized "notation (name := cont_mdiff_map) `C^` n `⟮` I `, ` M `; ` I' `, ` M' `⟯` :=
  cont_mdiff_map I I' M M' n" in manifold
localized "notation (name := cont_mdiff_map.self) `C^` n `⟮` I `, ` M `; ` k `⟯` :=
  cont_mdiff_map I (model_with_corners_self k k) M k n" in manifold

open_locale manifold

namespace cont_mdiff_map

variables {I} {I'} {M} {M'} {n}

instance fun_like : fun_like C^n⟮I, M; I', M'⟯ M (λ _, M') :=
{ coe := subtype.val,
  coe_injective' := subtype.coe_injective }

protected lemma cont_mdiff (f : C^n⟮I, M; I', M'⟯) :
  cont_mdiff I I' n f := f.prop

protected lemma smooth (f : C^∞⟮I, M; I', M'⟯) :
  smooth I I' f := f.prop

instance : has_coe C^n⟮I, M; I', M'⟯ C(M, M') :=
⟨λ f, ⟨f, f.cont_mdiff.continuous⟩⟩

attribute [to_additive_ignore_args 21] cont_mdiff_map
  cont_mdiff_map.fun_like cont_mdiff_map.continuous_map.has_coe
variables {f g : C^n⟮I, M; I', M'⟯}

@[simp] lemma coe_fn_mk (f : M → M') (hf : cont_mdiff I I' n f) :
  ((by exact subtype.mk f hf : C^n⟮I, M; I', M'⟯) : M → M') = f :=
rfl

lemma coe_inj ⦃f g : C^n⟮I, M; I', M'⟯⦄ (h : (f : M → M') = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext] theorem ext (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext h

instance : continuous_map_class C^n⟮I, M; I', M'⟯ M M' :=
{ coe := (λ f, ⇑f),
  coe_injective' := coe_inj,
  map_continuous := λ f, f.cont_mdiff.continuous }

/-- The identity as a smooth map. -/
def id : C^n⟮I, M; I, M⟯ := ⟨id, cont_mdiff_id⟩

/-- The composition of smooth maps, as a smooth map. -/
def comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', M''⟯ :=
{ val := λ a, f (g a),
  property := f.cont_mdiff.comp g.cont_mdiff, }

@[simp] lemma comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M) :
  f.comp g x = f (g x) := rfl

instance [inhabited M'] : inhabited C^n⟮I, M; I', M'⟯ :=
⟨⟨λ _, default, cont_mdiff_const⟩⟩

/-- Constant map as a smooth map -/
def const (y : M') : C^n⟮I, M; I', M'⟯ := ⟨λ x, y, cont_mdiff_const⟩

/-- The first projection of a product, as a smooth map. -/
def fst : C^n⟮I.prod I', M × M'; I, M⟯ := ⟨prod.fst, cont_mdiff_fst⟩

/-- The second projection of a product, as a smooth map. -/
def snd : C^n⟮I.prod I', M × M'; I', M'⟯ := ⟨prod.snd, cont_mdiff_snd⟩

/-- Given two smooth maps `f` and `g`, this is the smooth map `x ↦ (f x, g x)`. -/
def prod_mk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.prod I', M × M'⟯ :=
⟨λ x, (f x, g x), f.2.prod_mk g.2⟩

end cont_mdiff_map

instance continuous_linear_map.has_coe_to_cont_mdiff_map :
  has_coe (E →L[𝕜] E') C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, E'), E'⟯ :=
⟨λ f, ⟨f.to_fun, f.cont_mdiff⟩⟩
