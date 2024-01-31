/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.category.basic
import category_theory.functor.basic
import category_theory.groupoid
import tactic.nth_rewrite
import category_theory.path_category
import category_theory.quotient
import combinatorics.quiver.symmetric

/-!
# Free groupoid on a quiver

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the free groupoid on a quiver, the lifting of a prefunctor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given the type `V` and a quiver instance on `V`:

- `free_groupoid V`: a type synonym for `V`.
- `free_groupoid_groupoid`: the `groupoid` instance on `free_groupoid V`.
- `lift`: the lifting of a prefunctor from `V` to `V'` where `V'` is a groupoid, to a functor.
 `free_groupoid V ⥤ V'`.
- `lift_spec` and `lift_unique`: the proofs that, respectively, `lift` indeed is a lifting
 and is the unique one.

## Implementation notes

The free groupoid is first defined by symmetrifying the quiver, taking the induced path category
and finally quotienting by the reducibility relation.

-/

open set classical function
local attribute [instance] prop_decidable

namespace category_theory
namespace groupoid
namespace free

universes u v u' v' u'' v''

variables {V : Type u} [quiver.{v+1} V]

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths $ symmetrify V` -/
abbreviation quiver.hom.to_pos_path {X Y : V} (f : X ⟶ Y) :
 ((category_theory.paths.category_paths $ quiver.symmetrify V).hom X Y) := f.to_pos.to_path

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths $ symmetrify V` -/
abbreviation quiver.hom.to_neg_path {X Y : V} (f : X ⟶ Y) :
 ((category_theory.paths.category_paths $ quiver.symmetrify V).hom Y X) := f.to_neg.to_path

/-- The "reduction" relation -/
inductive red_step : hom_rel (paths (quiver.symmetrify V))
| step (X Z : quiver.symmetrify V) (f : X ⟶ Z) :
 red_step (𝟙 X) (f.to_path ≫ (quiver.reverse f).to_path)

/-- The underlying vertices of the free groupoid -/
def _root_.category_theory.free_groupoid (V) [Q : quiver V] := quotient (@red_step V Q)

instance {V} [Q : quiver V] [h : nonempty V] : nonempty (free_groupoid V) := ⟨⟨h.some⟩⟩

lemma congr_reverse {X Y : paths $ quiver.symmetrify V} (p q : X ⟶ Y) :
 quotient.comp_closure red_step p q →
 quotient.comp_closure red_step (p.reverse) (q.reverse) :=
begin
 rintro ⟨XW, pp, qq, WY, _, Z, f⟩,
 have : quotient.comp_closure red_step (WY.reverse ≫ 𝟙 _ ≫ XW.reverse)
 (WY.reverse ≫ (f.to_path ≫ (quiver.reverse f).to_path) ≫ XW.reverse),
 { apply quotient.comp_closure.intro,
 apply red_step.step, },
 simpa only [category_struct.comp, category_struct.id, quiver.path.reverse, quiver.path.nil_comp,
 quiver.path.reverse_comp, quiver.reverse_reverse, quiver.path.reverse_to_path,
 quiver.path.comp_assoc] using this,
end

lemma congr_comp_reverse {X Y : paths $ quiver.symmetrify V} (p : X ⟶ Y) :
 quot.mk (@quotient.comp_closure _ _ red_step _ _) (p ≫ p.reverse) =
 quot.mk (@quotient.comp_closure _ _ red_step _ _) (𝟙 X) :=
begin
 apply quot.eqv_gen_sound,
 induction p with _ _ q f ih,
 { apply eqv_gen.refl, },
 { simp only [quiver.path.reverse],
 fapply eqv_gen.trans,
 { exact q ≫ q.reverse, },
 { apply eqv_gen.symm, apply eqv_gen.rel,
 have : quotient.comp_closure
 red_step (q ≫ (𝟙 _) ≫ q.reverse)
 (q ≫ (f.to_path ≫ (quiver.reverse f).to_path) ≫ q.reverse), by
 { apply quotient.comp_closure.intro, apply red_step.step, },
 have that : q.cons f = q.comp f.to_path, by refl, rw that,
 simp only [category.assoc, category.id_comp] at this ⊢,
 simp only [category_struct.comp, quiver.path.comp_assoc] at this ⊢,
 exact this, },
 { exact ih }, },
end

lemma congr_reverse_comp {X Y : paths $ quiver.symmetrify V} (p : X ⟶ Y) :
 quot.mk (@quotient.comp_closure _ _ red_step _ _) (p.reverse ≫ p) =
 quot.mk (@quotient.comp_closure _ _ red_step _ _) (𝟙 Y) :=
begin
 nth_rewrite 1 ←quiver.path.reverse_reverse p,
 apply congr_comp_reverse,
end

instance : category (free_groupoid V) := quotient.category red_step

/-- The inverse of an arrow in the free groupoid -/
def quot_inv {X Y : free_groupoid V} (f : X ⟶ Y) : Y ⟶ X :=
quot.lift_on f
 (λ pp, quot.mk _ $ pp.reverse)
 (λ pp qq con, quot.sound $ congr_reverse pp qq con)

instance : groupoid (free_groupoid V) :=
{ inv := λ X Y f, quot_inv f,
 inv_comp' := λ X Y p, quot.induction_on p $ λ pp, congr_reverse_comp pp,
 comp_inv' := λ X Y p, quot.induction_on p $ λ pp, congr_comp_reverse pp }

/-- The inclusion of the quiver on `V` to the underlying quiver on `free_groupoid V`-/
def of (V) [quiver V] : V ⥤q (free_groupoid V) :=
{ obj := λ X, ⟨X⟩,
 map := λ X Y f, quot.mk _ f.to_pos_path }

lemma of_eq : of V =
 (quiver.symmetrify.of ⋙q paths.of).comp (quotient.functor $ @red_step V _).to_prefunctor :=
begin
 apply prefunctor.ext, rotate,
 { rintro X, refl, },
 { rintro X Y f, refl, }
end

section universal_property

variables {V' : Type u'} [groupoid V'] (φ : V ⥤q V')

/-- The lift of a prefunctor to a groupoid, to a functor from `free_groupoid V` -/
def lift (φ : V ⥤q V') : free_groupoid V ⥤ V' :=
quotient.lift _
 (paths.lift $ quiver.symmetrify.lift φ)
 (by
 { rintros _ _ _ _ ⟨X,Y,f⟩,
 simp only [quiver.symmetrify.lift_reverse, paths.lift_nil, quiver.path.comp_nil,
 paths.lift_cons, paths.lift_to_path],
 symmetry,
 apply groupoid.comp_inv, })

lemma lift_spec (φ : V ⥤q V') : of V ⋙q (lift φ).to_prefunctor = φ :=
begin
 rw [of_eq]; rw [ prefunctor.comp_assoc]; rw [ prefunctor.comp_assoc]; rw [ functor.to_prefunctor_comp],
 dsimp [lift],
 rw [quotient.lift_spec]; rw [ paths.lift_spec]; rw [ quiver.symmetrify.lift_spec],
end

lemma lift_unique (φ : V ⥤q V') (Φ : free_groupoid V ⥤ V')
 (hΦ : of V ⋙q Φ.to_prefunctor = φ) : Φ = lift φ :=
begin
 apply quotient.lift_unique,
 apply paths.lift_unique,
 fapply @quiver.symmetrify.lift_unique _ _ _ _ _ _ _ _ _,
 { rw ←functor.to_prefunctor_comp, exact hΦ, },
 { constructor, rintros X Y f,
 simp only [←functor.to_prefunctor_comp,prefunctor.comp_map, paths.of_map, inv_eq_inv],
 change Φ.map (inv ((quotient.functor red_step).to_prefunctor.map f.to_path)) =
 inv (Φ.map ((quotient.functor red_step).to_prefunctor.map f.to_path)),
 have := functor.map_inv Φ ((quotient.functor red_step).to_prefunctor.map f.to_path),
 convert this; simp only [inv_eq_inv], },
end

end universal_property

section functoriality

variables {V' : Type u'} [quiver.{v'+1} V'] {V'' : Type u''} [quiver.{v''+1} V'']

/-- The functor of free groupoid induced by a prefunctor of quivers -/
def _root_.category_theory.free_groupoid_functor (φ : V ⥤q V') :
 free_groupoid V ⥤ free_groupoid V' := lift (φ ⋙q of V')

lemma free_groupoid_functor_id :
 free_groupoid_functor (prefunctor.id V) = functor.id (free_groupoid V) :=
begin
 dsimp only [free_groupoid_functor], symmetry,
 apply lift_unique, refl,
end

lemma free_groupoid_functor_comp
 (φ : V ⥤q V') (φ' : V' ⥤q V'') :
 free_groupoid_functor (φ ⋙q φ') = free_groupoid_functor φ ⋙ free_groupoid_functor φ' :=
begin
 dsimp only [free_groupoid_functor], symmetry,
 apply lift_unique, refl,
end

end functoriality

end free
end groupoid
end category_theory

