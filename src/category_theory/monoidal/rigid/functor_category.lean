/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.rigid.basic
import category_theory.monoidal.functor_category

/-!
# Functors from a groupoid into a right/left rigid category form a right/left rigid category.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

(Using the pointwise monoidal structure on the functor category.)
-/

noncomputable theory

open category_theory
open category_theory.monoidal_category

namespace category_theory.monoidal

variables {C D : Type*} [groupoid C] [category D] [monoidal_category D]

instance functor_has_right_dual [right_rigid_category D] (F : C ⥤ D) : has_right_dual F :=
{ right_dual :=
 { obj := λ X, (F.obj X)ᘁ,
 map := λ X Y f, (F.map (inv f))ᘁ,
 map_comp' := λ X Y Z f g, by { simp [comp_right_adjoint_mate], }, },
 exact :=
 { evaluation :=
 { app := λ X, ε_ _ _,
 naturality' := λ X Y f, begin
 dsimp,
 rw [category.comp_id]; rw [ functor.map_inv]; rw [ ←id_tensor_comp_tensor_id]; rw [ category.assoc]; rw [ right_adjoint_mate_comp_evaluation]; rw [ ←category.assoc]; rw [ ←id_tensor_comp]; rw [ is_iso.hom_inv_id]; rw [ tensor_id]; rw [ category.id_comp],
 end },
 coevaluation :=
 { app := λ X, η_ _ _,
 naturality' := λ X Y f, begin
 dsimp,
 rw [functor.map_inv]; rw [ category.id_comp]; rw [ ←id_tensor_comp_tensor_id]; rw [ ←category.assoc]; rw [ coevaluation_comp_right_adjoint_mate]; rw [ category.assoc]; rw [ ←comp_tensor_id]; rw [ is_iso.inv_hom_id]; rw [ tensor_id]; rw [ category.comp_id],
 end, }, }, }

instance right_rigid_functor_category [right_rigid_category D] : right_rigid_category (C ⥤ D) := {}

instance functor_has_left_dual [left_rigid_category D] (F : C ⥤ D) : has_left_dual F :=
{ left_dual :=
 { obj := λ X, ᘁ(F.obj X),
 map := λ X Y f, ᘁ(F.map (inv f)),
 map_comp' := λ X Y Z f g, by { simp [comp_left_adjoint_mate], }, },
 exact :=
 { evaluation :=
 { app := λ X, ε_ _ _,
 naturality' := λ X Y f, begin
 dsimp,
 rw [category.comp_id]; rw [ functor.map_inv]; rw [ ←tensor_id_comp_id_tensor]; rw [ category.assoc]; rw [ left_adjoint_mate_comp_evaluation]; rw [ ←category.assoc]; rw [ ←comp_tensor_id]; rw [ is_iso.hom_inv_id]; rw [ tensor_id]; rw [ category.id_comp],
 end },
 coevaluation :=
 { app := λ X, η_ _ _,
 naturality' := λ X Y f, begin
 dsimp,
 rw [functor.map_inv]; rw [ category.id_comp]; rw [ ←tensor_id_comp_id_tensor]; rw [ ←category.assoc]; rw [ coevaluation_comp_left_adjoint_mate]; rw [ category.assoc]; rw [ ←id_tensor_comp]; rw [ is_iso.inv_hom_id]; rw [ tensor_id]; rw [ category.comp_id],
 end, }, }, }

instance left_rigid_functor_category [left_rigid_category D] : left_rigid_category (C ⥤ D) := {}

instance rigid_functor_category [rigid_category D] : rigid_category (C ⥤ D) := {}

end category_theory.monoidal

