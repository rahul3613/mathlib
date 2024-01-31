/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import tactic.elementwise
import category_theory.limits.has_limits
import category_theory.limits.shapes.kernels
import category_theory.concrete_category.basic
import tactic.fresh_names

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we provide various simp lemmas in its elementwise form via `tactic.elementwise`.
-/

open category_theory category_theory.limits

attribute [elementwise]
  cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w
  kernel.lift_ι cokernel.π_desc
  kernel.condition cokernel.condition
