/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Group.basic
import category_theory.preadditive.basic

/-!
# The category of additive commutative groups is preadditive.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open category_theory

universe u

namespace AddCommGroup

instance : preadditive AddCommGroup :=
{ add_comp' := λ P Q R f f' g,
 show (f + f') ≫ g = f ≫ g + f' ≫ g, by { ext, simp },
 comp_add' := λ P Q R f g g',
 show f ≫ (g + g') = f ≫ g + f ≫ g', by { ext, simp } }

end AddCommGroup

