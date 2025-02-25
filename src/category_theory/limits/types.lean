/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import category_theory.limits.shapes.images
import category_theory.filtered
import tactic.equiv_rw

/-!
# Limits in the category of types.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that the category of types has all (co)limits, by providing the usual concrete models.

We also give a characterisation of filtered colimits in `Type`, via
`colimit.ι F i xi = colimit.ι F j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj`.

Finally, we prove the category of types has categorical images,
and that these agree with the range of a function.
-/

universes v u

open category_theory
open category_theory.limits

namespace category_theory.limits.types

variables {J : Type v} [small_category J]

/--
(internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
def limit_cone (F : J ⥤ Type (max v u)) : cone F :=
{ X := F.sections,
 π := { app := λ j u, u.val j } }

local attribute [elab_simple] congr_fun
/-- (internal implementation) the fact that the proposed limit cone is the limit -/
def limit_cone_is_limit (F : J ⥤ Type (max v u)) : is_limit (limit_cone F) :=
{ lift := λ s v, ⟨λ j, s.π.app j v, λ j j' f, congr_fun (cone.w s f) _⟩,
 uniq' := by { intros, ext x j, exact congr_fun (w j) x } }

/--
The category of types has all limits.

See <https://stacks.math.columbia.edu/tag/002U>.
-/
instance has_limits_of_size : has_limits_of_size.{v} (Type (max v u)) :=
{ has_limits_of_shape := λ J 𝒥, by exactI
 { has_limit := λ F, has_limit.mk
 { cone := limit_cone F, is_limit := limit_cone_is_limit F } } }

instance : has_limits (Type u) := types.has_limits_of_size.{u u}

/--
The equivalence between a limiting cone of `F` in `Type u` and the "concrete" definition as the
sections of `F`.
-/
def is_limit_equiv_sections {F : J ⥤ Type (max v u)} {c : cone F} (t : is_limit c) :
 c.X ≃ F.sections :=
(is_limit.cone_point_unique_up_to_iso t (limit_cone_is_limit F)).to_equiv

@[simp]
lemma is_limit_equiv_sections_apply
 {F : J ⥤ Type (max v u)} {c : cone F} (t : is_limit c) (j : J) (x : c.X) :
 (((is_limit_equiv_sections t) x) : Π j, F.obj j) j = c.π.app j x :=
rfl

@[simp]
lemma is_limit_equiv_sections_symm_apply
 {F : J ⥤ Type (max v u)} {c : cone F} (t : is_limit c) (x : F.sections) (j : J) :
 c.π.app j ((is_limit_equiv_sections t).symm x) = (x : Π j, F.obj j) j :=
begin
 equiv_rw (is_limit_equiv_sections t).symm at x,
 simp,
end

/--
The equivalence between the abstract limit of `F` in `Type u`
and the "concrete" definition as the sections of `F`.
-/
noncomputable
def limit_equiv_sections (F : J ⥤ Type (max v u)) : (limit F : Type (max v u)) ≃ F.sections :=
is_limit_equiv_sections (limit.is_limit _)

@[simp]
lemma limit_equiv_sections_apply (F : J ⥤ Type (max v u)) (x : limit F) (j : J) :
 (((limit_equiv_sections F) x) : Π j, F.obj j) j = limit.π F j x :=
rfl

@[simp]
lemma limit_equiv_sections_symm_apply (F : J ⥤ Type (max v u)) (x : F.sections) (j : J) :
 limit.π F j ((limit_equiv_sections F).symm x) = (x : Π j, F.obj j) j :=
is_limit_equiv_sections_symm_apply _ _ _

@[simp]
lemma limit_equiv_sections_symm_apply' (F : J ⥤ Type v) (x : F.sections) (j : J) :
 limit.π F j ((limit_equiv_sections.{v v} F).symm x) = (x : Π j, F.obj j) j :=
is_limit_equiv_sections_symm_apply _ _ _

/--
Construct a term of `limit F : Type u` from a family of terms `x : Π j, F.obj j`
which are "coherent": `∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j'`.
-/
@[ext]
noncomputable
def limit.mk (F : J ⥤ Type (max v u)) (x : Π j, F.obj j)
 (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') : (limit F : Type (max v u)) :=
(limit_equiv_sections F).symm ⟨x, h⟩

@[simp]
lemma limit.π_mk (F : J ⥤ Type (max v u)) (x : Π j, F.obj j)
 (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) : limit.π F j (limit.mk F x h) = x j :=
by { dsimp [limit.mk], simp, }

@[simp]
lemma limit.π_mk' (F : J ⥤ Type v) (x : Π j, F.obj j)
 (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
 limit.π F j (limit.mk.{v v} F x h) = x j :=
by { dsimp [limit.mk], simp, }

-- PROJECT: prove this for concrete categories where the forgetful functor preserves limits
@[ext]
lemma limit_ext (F : J ⥤ Type (max v u)) (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) :
 x = y :=
begin
 apply (limit_equiv_sections F).injective,
 ext j,
 simp [w j],
end

@[ext]
lemma limit_ext' (F : J ⥤ Type v) (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) :
 x = y :=
begin
 apply (limit_equiv_sections.{v v} F).injective,
 ext j,
 simp [w j],
end

lemma limit_ext_iff (F : J ⥤ Type (max v u)) (x y : limit F) :
 x = y ↔ (∀ j, limit.π F j x = limit.π F j y) :=
⟨λ t _, t ▸ rfl, limit_ext _ _ _⟩

lemma limit_ext_iff' (F : J ⥤ Type v) (x y : limit F) :
 x = y ↔ (∀ j, limit.π F j x = limit.π F j y) :=
⟨λ t _, t ▸ rfl, limit_ext _ _ _⟩

-- TODO: are there other limits lemmas that should have `_apply` versions?
-- Can we generate these like with `@[reassoc]`?
-- PROJECT: prove these for any concrete category where the forgetful functor preserves limits?

@[simp]
lemma limit.w_apply {F : J ⥤ Type (max v u)} {j j' : J} {x : limit F} (f : j ⟶ j') :
 F.map f (limit.π F j x) = limit.π F j' x :=
congr_fun (limit.w F f) x

@[simp]
lemma limit.lift_π_apply (F : J ⥤ Type (max v u)) (s : cone F) (j : J) (x : s.X) :
 limit.π F j (limit.lift F s x) = s.π.app j x :=
congr_fun (limit.lift_π s j) x

@[simp]
lemma limit.map_π_apply {F G : J ⥤ Type (max v u)} (α : F ⟶ G) (j : J) (x) :
 limit.π G j (lim_map α x) = α.app j (limit.π F j x) :=
congr_fun (lim_map_π α j) x

@[simp]
lemma limit.w_apply' {F : J ⥤ Type v} {j j' : J} {x : limit F} (f : j ⟶ j') :
 F.map f (limit.π F j x) = limit.π F j' x :=
congr_fun (limit.w F f) x

@[simp]
lemma limit.lift_π_apply' (F : J ⥤ Type v) (s : cone F) (j : J) (x : s.X) :
 limit.π F j (limit.lift F s x) = s.π.app j x :=
congr_fun (limit.lift_π s j) x

@[simp]
lemma limit.map_π_apply' {F G : J ⥤ Type v} (α : F ⟶ G) (j : J) (x) :
 limit.π G j (lim_map α x) = α.app j (limit.π F j x) :=
congr_fun (lim_map_π α j) x

/--
The relation defining the quotient type which implements the colimit of a functor `F : J ⥤ Type u`.
See `category_theory.limits.types.quot`.
-/
def quot.rel (F : J ⥤ Type (max v u)) : (Σ j, F.obj j) → (Σ j, F.obj j) → Prop :=
(λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2)

/--
A quotient type implementing the colimit of a functor `F : J ⥤ Type u`,
as pairs `⟨j, x⟩` where `x : F.obj j`, modulo the equivalence relation generated by
`⟨j, x⟩ ~ ⟨j', x'⟩` whenever there is a morphism `f : j ⟶ j'` so `F.map f x = x'`.
-/
@[nolint has_nonempty_instance]
def quot (F : J ⥤ Type (max v u)) : Type (max v u) :=
@quot (Σ j, F.obj j) (quot.rel F)

/--
(internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
def colimit_cocone (F : J ⥤ Type (max v u)) : cocone F :=
{ X := quot F,
 ι :=
 { app := λ j x, quot.mk _ ⟨j, x⟩,
 naturality' := λ j j' f, funext $ λ x, eq.symm (quot.sound ⟨f, rfl⟩) } }

local attribute [elab_with_expected_type] quot.lift

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
def colimit_cocone_is_colimit (F : J ⥤ Type (max v u)) : is_colimit (colimit_cocone F) :=
{ desc := λ s, quot.lift (λ (p : Σ j, F.obj j), s.ι.app p.1 p.2)
 (assume ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩, by rw hf; exact (congr_fun (cocone.w s f) x).symm) }

/--
The category of types has all colimits.

See <https://stacks.math.columbia.edu/tag/002U>.
-/
instance has_colimits_of_size : has_colimits_of_size.{v} (Type (max v u)) :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
 { has_colimit := λ F, has_colimit.mk
 { cocone := colimit_cocone F, is_colimit := colimit_cocone_is_colimit F } } }

instance : has_colimits (Type u) := types.has_colimits_of_size.{u u}

/--
The equivalence between the abstract colimit of `F` in `Type u`
and the "concrete" definition as a quotient.
-/
noncomputable
def colimit_equiv_quot (F : J ⥤ Type (max v u)) : (colimit F : Type (max v u)) ≃ quot F :=
(is_colimit.cocone_point_unique_up_to_iso
 (colimit.is_colimit F)
 (colimit_cocone_is_colimit F)).to_equiv

@[simp]
lemma colimit_equiv_quot_symm_apply (F : J ⥤ Type (max v u)) (j : J) (x : F.obj j) :
 (colimit_equiv_quot F).symm (quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
rfl

@[simp]
lemma colimit_equiv_quot_apply (F : J ⥤ Type (max v u)) (j : J) (x : F.obj j) :
 (colimit_equiv_quot F) (colimit.ι F j x) = quot.mk _ ⟨j, x⟩ :=
begin
 apply (colimit_equiv_quot F).symm.injective,
 simp,
end

@[simp]
lemma colimit.w_apply {F : J ⥤ Type (max v u)} {j j' : J} {x : F.obj j} (f : j ⟶ j') :
 colimit.ι F j' (F.map f x) = colimit.ι F j x :=
congr_fun (colimit.w F f) x

@[simp]
lemma colimit.ι_desc_apply (F : J ⥤ Type (max v u)) (s : cocone F) (j : J) (x : F.obj j) :
 colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
congr_fun (colimit.ι_desc s j) x

@[simp]
lemma colimit.ι_map_apply {F G : J ⥤ Type (max v u)} (α : F ⟶ G) (j : J) (x) :
 colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
congr_fun (colimit.ι_map α j) x

@[simp]
lemma colimit.w_apply' {F : J ⥤ Type v} {j j' : J} {x : F.obj j} (f : j ⟶ j') :
 colimit.ι F j' (F.map f x) = colimit.ι F j x :=
congr_fun (colimit.w F f) x

@[simp]
lemma colimit.ι_desc_apply' (F : J ⥤ Type v) (s : cocone F) (j : J) (x : F.obj j) :
 colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
congr_fun (colimit.ι_desc s j) x

@[simp]
lemma colimit.ι_map_apply' {F G : J ⥤ Type v} (α : F ⟶ G) (j : J) (x) :
 colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
congr_fun (colimit.ι_map α j) x

lemma colimit_sound
 {F : J ⥤ Type (max v u)} {j j' : J} {x : F.obj j} {x' : F.obj j'}
 (f : j ⟶ j') (w : F.map f x = x') : colimit.ι F j x = colimit.ι F j' x' :=
begin
 rw [←w],
 simp,
end

lemma colimit_sound'
 {F : J ⥤ Type (max v u)} {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
 (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') :
 colimit.ι F j x = colimit.ι F j' x' :=
begin
 rw [←colimit.w _ f]; rw [ ←colimit.w _ f'],
 rw [types_comp_apply]; rw [ types_comp_apply]; rw [ w],
end

lemma colimit_eq {F : J ⥤ Type (max v u)} {j j' : J} {x : F.obj j} {x' : F.obj j'}
 (w : colimit.ι F j x = colimit.ι F j' x') : eqv_gen (quot.rel F) ⟨j, x⟩ ⟨j', x'⟩ :=
begin
 apply quot.eq.1,
 simpa using congr_arg (colimit_equiv_quot F) w,
end

lemma jointly_surjective (F : J ⥤ Type (max v u)) {t : cocone F} (h : is_colimit t)
 (x : t.X) : ∃ j y, t.ι.app j y = x :=
begin
 suffices : (λ (x : t.X), ulift.up (∃ j y, t.ι.app j y = x)) = (λ _, ulift.up true),
 { have := congr_fun this x,
 have H := congr_arg ulift.down this,
 dsimp at H,
 rwa eq_true_iff at H },
 refine h.hom_ext _,
 intro j, ext y,
 erw iff_true,
 exact ⟨j, y, rfl⟩
end

/-- A variant of `jointly_surjective` for `x : colimit F`. -/
lemma jointly_surjective' {F : J ⥤ Type (max v u)}
 (x : colimit F) : ∃ j y, colimit.ι F j y = x :=
jointly_surjective F (colimit.is_colimit _) x

namespace filtered_colimit
/- For filtered colimits of types, we can give an explicit description
 of the equivalence relation generated by the relation used to form
 the colimit. -/

variables (F : J ⥤ Type (max v u))

/--
An alternative relation on `Σ j, F.obj j`,
which generates the same equivalence relation as we use to define the colimit in `Type` above,
but that is more convenient when working with filtered colimits.

Elements in `F.obj j` and `F.obj j'` are equivalent if there is some `k : J` to the right
where their images are equal.
-/
protected def rel (x y : Σ j, F.obj j) : Prop :=
∃ k (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2

lemma rel_of_quot_rel (x y : Σ j, F.obj j) : quot.rel F x y → filtered_colimit.rel F x y :=
λ ⟨f, h⟩, ⟨y.1, f, 𝟙 y.1, by rw [← h]; rw [ functor_to_types.map_id_apply]⟩

lemma eqv_gen_quot_rel_of_rel (x y : Σ j, F.obj j) :
 filtered_colimit.rel F x y → eqv_gen (quot.rel F) x y :=
λ ⟨k, f, g, h⟩, eqv_gen.trans _ ⟨k, F.map f x.2⟩ _ (eqv_gen.rel _ _ ⟨f, rfl⟩)
 (eqv_gen.symm _ _ (eqv_gen.rel _ _ ⟨g, h⟩))

local attribute [elab_simple] nat_trans.app

/-- Recognizing filtered colimits of types. -/
noncomputable def is_colimit_of (t : cocone F) (hsurj : ∀ (x : t.X), ∃ i xi, x = t.ι.app i xi)
 (hinj : ∀ i j xi xj, t.ι.app i xi = t.ι.app j xj →
 ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj) : is_colimit t :=
-- Strategy: Prove that the map from "the" colimit of F (defined above) to t.X
-- is a bijection.
begin
 apply is_colimit.of_iso_colimit (colimit.is_colimit F),
 refine cocones.ext (equiv.to_iso (equiv.of_bijective _ _)) _,
 { exact colimit.desc F t },
 { split,
 { show function.injective _,
 intros a b h,
 rcases jointly_surjective F (colimit.is_colimit F) a with ⟨i, xi, rfl⟩,
 rcases jointly_surjective F (colimit.is_colimit F) b with ⟨j, xj, rfl⟩,
 change (colimit.ι F i ≫ colimit.desc F t) xi = (colimit.ι F j ≫ colimit.desc F t) xj at h,
 rw [colimit.ι_desc] at h; rw [ colimit.ι_desc] at h,
 rcases hinj i j xi xj h with ⟨k, f, g, h'⟩,
 change colimit.ι F i xi = colimit.ι F j xj,
 rw [←colimit.w F f]; rw [ ←colimit.w F g],
 change colimit.ι F k (F.map f xi) = colimit.ι F k (F.map g xj),
 rw h' },
 { show function.surjective _,
 intro x,
 rcases hsurj x with ⟨i, xi, rfl⟩,
 use colimit.ι F i xi,
 simp } },
 { intro j, apply colimit.ι_desc }
end

variables [is_filtered_or_empty J]

protected lemma rel_equiv : equivalence (filtered_colimit.rel F) :=
⟨λ x, ⟨x.1, 𝟙 x.1, 𝟙 x.1, rfl⟩,
 λ x y ⟨k, f, g, h⟩, ⟨k, g, f, h.symm⟩,
 λ x y z ⟨k, f, g, h⟩ ⟨k', f', g', h'⟩,
 let ⟨l, fl, gl, _⟩ := is_filtered_or_empty.cocone_objs k k',
 ⟨m, n, hn⟩ := is_filtered_or_empty.cocone_maps (g ≫ fl) (f' ≫ gl) in
 ⟨m, f ≫ fl ≫ n, g' ≫ gl ≫ n, calc
 F.map (f ≫ fl ≫ n) x.2
 = F.map (fl ≫ n) (F.map f x.2) : by simp
 ... = F.map (fl ≫ n) (F.map g y.2) : by rw h
 ... = F.map ((g ≫ fl) ≫ n) y.2 : by simp
 ... = F.map ((f' ≫ gl) ≫ n) y.2 : by rw hn
 ... = F.map (gl ≫ n) (F.map f' y.2) : by simp
 ... = F.map (gl ≫ n) (F.map g' z.2) : by rw h'
 ... = F.map (g' ≫ gl ≫ n) z.2 : by simp⟩⟩

protected lemma rel_eq_eqv_gen_quot_rel :
 filtered_colimit.rel F = eqv_gen (quot.rel F) :=
begin
 ext ⟨j, x⟩ ⟨j', y⟩,
 split,
 { apply eqv_gen_quot_rel_of_rel },
 { rw ←(filtered_colimit.rel_equiv F).eqv_gen_iff,
 exact eqv_gen.mono (rel_of_quot_rel F) }
end

lemma colimit_eq_iff_aux {i j : J} {xi : F.obj i} {xj : F.obj j} :
 (colimit_cocone F).ι.app i xi = (colimit_cocone F).ι.app j xj ↔
 filtered_colimit.rel F ⟨i, xi⟩ ⟨j, xj⟩ :=
begin
 change quot.mk _ _ = quot.mk _ _ ↔ _,
 rw [quot.eq]; rw [ filtered_colimit.rel_eq_eqv_gen_quot_rel],
end

lemma is_colimit_eq_iff {t : cocone F} (ht : is_colimit t) {i j : J} {xi : F.obj i} {xj : F.obj j} :
 t.ι.app i xi = t.ι.app j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
let t' := colimit_cocone F,
 e : t' ≅ t := is_colimit.unique_up_to_iso (colimit_cocone_is_colimit F) ht,
 e' : t'.X ≅ t.X := (cocones.forget _).map_iso e in
begin
 refine iff.trans _ (colimit_eq_iff_aux F),
 convert e'.to_equiv.apply_eq_iff_eq; rw ←e.hom.w; refl
end

lemma colimit_eq_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
 colimit.ι F i xi = colimit.ι F j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
is_colimit_eq_iff _ (colimit.is_colimit F)

end filtered_colimit

variables {α β : Type u} (f : α ⟶ β)

section -- implementation of `has_image`
/-- the image of a morphism in Type is just `set.range f` -/
def image : Type u := set.range f

instance [inhabited α] : inhabited (image f) :=
{ default := ⟨f default, ⟨_, rfl⟩⟩ }

/-- the inclusion of `image f` into the target -/
def image.ι : image f ⟶ β := subtype.val

instance : mono (image.ι f) :=
(mono_iff_injective _).2 subtype.val_injective

variables {f}

/-- the universal property for the image factorisation -/
noncomputable def image.lift (F' : mono_factorisation f) : image f ⟶ F'.I :=
(λ x, F'.e (classical.indefinite_description _ x.2).1 : image f → F'.I)

lemma image.lift_fac (F' : mono_factorisation f) : image.lift F' ≫ F'.m = image.ι f :=
begin
 ext x,
 change (F'.e ≫ F'.m) _ = _,
 rw [F'.fac]; rw [ (classical.indefinite_description _ x.2).2],
 refl,
end
end

/-- the factorisation of any morphism in Type through a mono. -/
def mono_factorisation : mono_factorisation f :=
{ I := image f,
 m := image.ι f,
 e := set.range_factorization f }

/-- the facorisation through a mono has the universal property of the image. -/
noncomputable def is_image : is_image (mono_factorisation f) :=
{ lift := image.lift,
 lift_fac' := image.lift_fac }

instance : has_image f :=
has_image.mk ⟨_, is_image f⟩

instance : has_images (Type u) :=
{ has_image := by apply_instance }

instance : has_image_maps (Type u) :=
{ has_image_map := λ f g st, has_image_map.transport st (mono_factorisation f.hom) (is_image g.hom)
 (λ x, ⟨st.right x.1, ⟨st.left (classical.some x.2),
 begin
 have p := st.w,
 replace p := congr_fun p (classical.some x.2),
 simp only [functor.id_map, types_comp_apply, subtype.val_eq_coe] at p,
 erw [p]; erw [ classical.some_spec x.2],
 end⟩⟩) rfl }

end category_theory.limits.types

