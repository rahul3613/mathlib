/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import category_theory.opposites

/-!
# Morphisms from equations between objects.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

When working categorically, sometimes one encounters an equation `h : X = Y` between objects.

Your initial aversion to this is natural and appropriate:
you're in for some trouble, and if there is another way to approach the problem that won't
rely on this equality, it may be worth pursuing.

You have two options:
1. Use the equality `h` as one normally would in Lean (e.g. using `rw` and `subst`).
   This may immediately cause difficulties, because in category theory everything is dependently
   typed, and equations between objects quickly lead to nasty goals with `eq.rec`.
2. Promote `h` to a morphism using `eq_to_hom h : X ⟶ Y`, or `eq_to_iso h : X ≅ Y`.

This file introduces various `simp` lemmas which in favourable circumstances
result in the various `eq_to_hom` morphisms to drop out at the appropriate moment!
-/

universes v₁ v₂ v₃ u₁ u₂ u₃
-- morphism levels before object levels. See note [category_theory universes].

namespace category_theory
open opposite

variables {C : Type u₁} [category.{v₁} C]

/--
An equality `X = Y` gives us a morphism `X ⟶ Y`.

It is typically better to use this, rather than rewriting by the equality then using `𝟙 _`
which usually leads to dependent type theory hell.
-/
def eq_to_hom {X Y : C} (p : X = Y) : X ⟶ Y := by rw p; exact 𝟙 _

@[simp] lemma eq_to_hom_refl (X : C) (p : X = X) : eq_to_hom p = 𝟙 X := rfl
@[simp, reassoc] lemma eq_to_hom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
  eq_to_hom p ≫ eq_to_hom q = eq_to_hom (p.trans q) :=
by { cases p, cases q, simp, }

lemma comp_eq_to_hom_iff {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y') :
  f ≫ eq_to_hom p = g ↔ f = g ≫ eq_to_hom p.symm :=
{ mp := λ h, h ▸ by simp,
  mpr := λ h, by simp [eq_whisker h (eq_to_hom p)] }

lemma eq_to_hom_comp_iff {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y) :
  eq_to_hom p ≫ g = f ↔ g = eq_to_hom p.symm ≫ f :=
{ mp := λ h, h ▸ by simp,
  mpr := λ h, h ▸ by simp [whisker_eq _ h] }

/--
If we (perhaps unintentionally) perform equational rewriting on
the source object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eq_to_hom`.

It may be advisable to introduce any necessary `eq_to_hom` morphisms manually,
rather than relying on this lemma firing.
-/
@[simp]
lemma congr_arg_mpr_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
  (congr_arg (λ W : C, W ⟶ Z) p).mpr q = eq_to_hom p ≫ q :=
by { cases p, simp, }

/--
If we (perhaps unintentionally) perform equational rewriting on
the target object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eq_to_hom`.

It may be advisable to introduce any necessary `eq_to_hom` morphisms manually,
rather than relying on this lemma firing.
-/
@[simp]
lemma congr_arg_mpr_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
  (congr_arg (λ W : C, X ⟶ W) q).mpr p = p ≫ eq_to_hom q.symm :=
by { cases q, simp, }

/--
An equality `X = Y` gives us an isomorphism `X ≅ Y`.

It is typically better to use this, rather than rewriting by the equality then using `iso.refl _`
which usually leads to dependent type theory hell.
-/
def eq_to_iso {X Y : C} (p : X = Y) : X ≅ Y :=
⟨eq_to_hom p, eq_to_hom p.symm, by simp, by simp⟩

@[simp] lemma eq_to_iso.hom {X Y : C} (p : X = Y) : (eq_to_iso p).hom = eq_to_hom p :=
rfl
@[simp] lemma eq_to_iso.inv {X Y : C} (p : X = Y) : (eq_to_iso p).inv = eq_to_hom p.symm :=
rfl

@[simp] lemma eq_to_iso_refl {X : C} (p : X = X) : eq_to_iso p = iso.refl X := rfl
@[simp] lemma eq_to_iso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
  eq_to_iso p ≪≫ eq_to_iso q = eq_to_iso (p.trans q) :=
by ext; simp

@[simp] lemma eq_to_hom_op {X Y : C} (h : X = Y) :
  (eq_to_hom h).op = eq_to_hom (congr_arg op h.symm) :=
by { cases h, refl, }

@[simp] lemma eq_to_hom_unop {X Y : Cᵒᵖ} (h : X = Y) :
  (eq_to_hom h).unop = eq_to_hom (congr_arg unop h.symm) :=
by { cases h, refl, }

instance {X Y : C} (h : X = Y) : is_iso (eq_to_hom h) := is_iso.of_iso (eq_to_iso h)

@[simp] lemma inv_eq_to_hom {X Y : C} (h : X = Y) : inv (eq_to_hom h) = eq_to_hom h.symm :=
by { ext, simp, }

variables {D : Type u₂} [category.{v₂} D]

namespace functor

/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
lemma ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ X Y f, F.map f = eq_to_hom (h_obj X) ≫ G.map f ≫ eq_to_hom (h_obj Y).symm) :
  F = G :=
begin
  cases F with F_obj _ _ _, cases G with G_obj _ _ _,
  obtain rfl : F_obj = G_obj, by { ext X, apply h_obj },
  congr,
  funext X Y f,
  simpa using h_map X Y f
end

/-- Two morphisms are conjugate via eq_to_hom if and only if they are heterogeneously equal. -/
lemma conj_eq_to_hom_iff_heq {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) :
  f = eq_to_hom h ≫ g ≫ eq_to_hom h'.symm ↔ f == g :=
by { cases h, cases h', simp }

/-- Proving equality between functors using heterogeneous equality. -/
lemma hext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ X Y (f : X ⟶ Y), F.map f == G.map f) : F = G :=
functor.ext h_obj (λ _ _ f,
  (conj_eq_to_hom_iff_heq _ _ (h_obj _) (h_obj _)).2 $ h_map _ _ f)

-- Using equalities between functors.

lemma congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X :=
by subst h

lemma congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
  F.map f = eq_to_hom (congr_obj h X) ≫ G.map f ≫ eq_to_hom (congr_obj h Y).symm :=
by subst h; simp

lemma congr_inv_of_congr_hom (F G : C ⥤ D) {X Y : C} (e : X ≅ Y)
  (hX : F.obj X = G.obj X) (hY : F.obj Y = G.obj Y)
  (h₂ : F.map e.hom = eq_to_hom (by rw hX) ≫ G.map e.hom ≫ eq_to_hom (by rw hY)) :
F.map e.inv = eq_to_hom (by rw hY) ≫ G.map e.inv ≫ eq_to_hom (by rw hX) :=
by simp only [← is_iso.iso.inv_hom e, functor.map_inv, h₂, is_iso.inv_comp,
  inv_eq_to_hom, category.assoc]

lemma congr_map (F : C ⥤ D) {X Y : C} {f g : X ⟶ Y} (h : f = g) :
  F.map f = F.map g := by rw h

section heq

/- Composition of functors and maps w.r.t. heq -/

variables {E : Type u₃} [category.{v₃} E] {F G : C ⥤ D} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

lemma map_comp_heq (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj Z = G.obj Z)
  (hf : F.map f == G.map f) (hg : F.map g == G.map g) : F.map (f ≫ g) == G.map (f ≫ g) :=
by { rw [F.map_comp, G.map_comp], congr' }

lemma map_comp_heq' (hobj : ∀ X : C, F.obj X = G.obj X)
  (hmap : ∀ {X Y} (f : X ⟶ Y), F.map f == G.map f) :
  F.map (f ≫ g) == G.map (f ≫ g) :=
by rw functor.hext hobj (λ _ _, hmap)

lemma precomp_map_heq (H : E ⥤ C)
  (hmap : ∀ {X Y} (f : X ⟶ Y), F.map f == G.map f) {X Y : E} (f : X ⟶ Y) :
  (H ⋙ F).map f == (H ⋙ G).map f := hmap _

lemma postcomp_map_heq (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y)
  (hmap : F.map f == G.map f) : (F ⋙ H).map f == (G ⋙ H).map f :=
by { dsimp, congr' }

lemma postcomp_map_heq' (H : D ⥤ E) (hobj : ∀ X : C, F.obj X = G.obj X)
  (hmap : ∀ {X Y} (f : X ⟶ Y), F.map f == G.map f) :
  (F ⋙ H).map f == (G ⋙ H).map f :=
by rw functor.hext hobj (λ _ _, hmap)

lemma hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) : F.map f == G.map f :=
by subst h

end heq

end functor

/--
This is not always a good idea as a `@[simp]` lemma,
as we lose the ability to use results that interact with `F`,
e.g. the naturality of a natural transformation.

In some files it may be appropriate to use `local attribute [simp] eq_to_hom_map`, however.
-/
lemma eq_to_hom_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
  F.map (eq_to_hom p) = eq_to_hom (congr_arg F.obj p) :=
by cases p; simp

/--
See the note on `eq_to_hom_map` regarding using this as a `simp` lemma.
-/
lemma eq_to_iso_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
  F.map_iso (eq_to_iso p) = eq_to_iso (congr_arg F.obj p) :=
by ext; cases p; simp

@[simp] lemma eq_to_hom_app {F G : C ⥤ D} (h : F = G) (X : C) :
  (eq_to_hom h : F ⟶ G).app X = eq_to_hom (functor.congr_obj h X) :=
by subst h; refl

lemma nat_trans.congr {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y) :
  α.app X = F.map (eq_to_hom h) ≫ α.app Y ≫ G.map (eq_to_hom h.symm) :=
by { rw [α.naturality_assoc], simp [eq_to_hom_map], }

lemma eq_conj_eq_to_hom {X Y : C} (f : X ⟶ Y) :
  f = eq_to_hom rfl ≫ f ≫ eq_to_hom rfl :=
by simp only [category.id_comp, eq_to_hom_refl, category.comp_id]

lemma dcongr_arg {ι : Type*} {F G : ι → C} (α : ∀ i, F i ⟶ G i) {i j : ι} (h : i = j) :
  α i = eq_to_hom (congr_arg F h) ≫ α j ≫ eq_to_hom (congr_arg G h.symm) :=
by { subst h, simp }

end category_theory
