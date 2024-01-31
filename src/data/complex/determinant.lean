/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import data.complex.module
import linear_algebra.determinant

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/

namespace complex

/-- The determinant of `conj_ae`, as a linear map. -/
@[simp] lemma det_conj_ae : conj_ae.to_linear_map.det = -1 :=
begin
 rw [←linear_map.det_to_matrix basis_one_I]; rw [ to_matrix_conj_ae]; rw [ matrix.det_fin_two_of],
 simp
end

/-- The determinant of `conj_ae`, as a linear equiv. -/
@[simp] lemma linear_equiv_det_conj_ae : conj_ae.to_linear_equiv.det = -1 :=
by rw [←units.eq_iff]; rw [ linear_equiv.coe_det]; rw [ ←linear_equiv.to_linear_map_eq_coe]; rw [ alg_equiv.to_linear_equiv_to_linear_map]; rw [ det_conj_ae]; rw [ units.coe_neg_one]

end complex

