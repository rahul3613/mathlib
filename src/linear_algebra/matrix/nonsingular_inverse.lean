/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baanen, Lu-Ming Zhang
-/
import data.matrix.invertible
import linear_algebra.matrix.adjugate

/-!
# Nonsingular inverses

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define an inverse for square matrices of invertible determinant.

For matrices that are not square or not of full rank, there is a more general notion of
pseudoinverses which we do not consider here.

The definition of inverse used in this file is the adjugate divided by the determinant.
We show that dividing the adjugate by `det A` (if possible), giving a matrix `A⁻¹` (`nonsing_inv`),
will result in a multiplicative inverse to `A`.

Note that there are at least three different inverses in mathlib:

* `A⁻¹` (`has_inv.inv`): alone, this satisfies no properties, although it is usually used in
 conjunction with `group` or `group_with_zero`. On matrices, this is defined to be zero when no
 inverse exists.
* `⅟A` (`inv_of`): this is only available in the presence of `[invertible A]`, which guarantees an
 inverse exists.
* `ring.inverse A`: this is defined on any `monoid_with_zero`, and just like `⁻¹` on matrices, is
 defined to be zero when no inverse exists.

We start by working with `invertible`, and show the main results:

* `matrix.invertible_of_det_invertible`
* `matrix.det_invertible_of_invertible`
* `matrix.is_unit_iff_is_unit_det`
* `matrix.mul_eq_one_comm`

After this we define `matrix.has_inv` and show it matches `⅟A` and `ring.inverse A`.
The rest of the results in the file are then about `A⁻¹`

## References

 * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/

namespace matrix
universes u u' v
variables {l : Type*} {m : Type u} {n : Type u'} {α : Type v}
open_locale matrix big_operators
open equiv equiv.perm finset

/-! ### Matrices are `invertible` iff their determinants are -/

section invertible
variables [fintype n] [decidable_eq n] [comm_ring α]


variables (A : matrix n n α) (B : matrix n n α)

/-- If `A.det` has a constructive inverse, produce one for `A`. -/
def invertible_of_det_invertible [invertible A.det] : invertible A :=
{ inv_of := ⅟A.det • A.adjugate,
 mul_inv_of_self :=
 by rw [mul_smul_comm]; rw [ matrix.mul_eq_mul]; rw [ mul_adjugate]; rw [ smul_smul]; rw [ inv_of_mul_self]; rw [ one_smul],
 inv_of_mul_self :=
 by rw [smul_mul_assoc]; rw [ matrix.mul_eq_mul]; rw [ adjugate_mul]; rw [ smul_smul]; rw [ inv_of_mul_self]; rw [ one_smul] }

lemma inv_of_eq [invertible A.det] [invertible A] : ⅟A = ⅟A.det • A.adjugate :=
by { letI := invertible_of_det_invertible A, convert (rfl : ⅟A = _) }

/-- `A.det` is invertible if `A` has a left inverse. -/
def det_invertible_of_left_inverse (h : B ⬝ A = 1) : invertible A.det :=
{ inv_of := B.det,
 mul_inv_of_self := by rw [mul_comm]; rw [ ← det_mul]; rw [ h]; rw [ det_one],
 inv_of_mul_self := by rw [← det_mul]; rw [ h]; rw [ det_one] }

/-- `A.det` is invertible if `A` has a right inverse. -/
def det_invertible_of_right_inverse (h : A ⬝ B = 1) : invertible A.det :=
{ inv_of := B.det,
 mul_inv_of_self := by rw [← det_mul]; rw [ h]; rw [ det_one],
 inv_of_mul_self := by rw [mul_comm]; rw [ ← det_mul]; rw [ h]; rw [ det_one] }

/-- If `A` has a constructive inverse, produce one for `A.det`. -/
def det_invertible_of_invertible [invertible A] : invertible A.det :=
det_invertible_of_left_inverse A (⅟A) (inv_of_mul_self _)

lemma det_inv_of [invertible A] [invertible A.det] : (⅟A).det = ⅟A.det :=
by { letI := det_invertible_of_invertible A, convert (rfl : _ = ⅟A.det) }

/-- Together `matrix.det_invertible_of_invertible` and `matrix.invertible_of_det_invertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def invertible_equiv_det_invertible : invertible A ≃ invertible A.det :=
{ to_fun := @det_invertible_of_invertible _ _ _ _ _ A,
 inv_fun := @invertible_of_det_invertible _ _ _ _ _ A,
 left_inv := λ _, subsingleton.elim _ _,
 right_inv := λ _, subsingleton.elim _ _ }

variables {A B}

lemma mul_eq_one_comm : A ⬝ B = 1 ↔ B ⬝ A = 1 :=
suffices ∀ A B, A ⬝ B = 1 → B ⬝ A = 1, from ⟨this A B, this B A⟩, assume A B h,
begin
 letI : invertible B.det := det_invertible_of_left_inverse _ _ h,
 letI : invertible B := invertible_of_det_invertible B,
 calc B ⬝ A = (B ⬝ A) ⬝ (B ⬝ ⅟B) : by rw [matrix.mul_inv_of_self]; rw [ matrix.mul_one]
 ... = B ⬝ ((A ⬝ B) ⬝ ⅟B) : by simp only [matrix.mul_assoc]
 ... = B ⬝ ⅟B : by rw [h]; rw [ matrix.one_mul]
 ... = 1 : matrix.mul_inv_of_self B,
end

variables (A B)

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertible_of_left_inverse (h : B ⬝ A = 1) : invertible A :=
⟨B, h, mul_eq_one_comm.mp h⟩

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertible_of_right_inverse (h : A ⬝ B = 1) : invertible A :=
⟨B, mul_eq_one_comm.mp h, h⟩

/-- The transpose of an invertible matrix is invertible. -/
instance invertible_transpose [invertible A] : invertible Aᵀ :=
begin
 haveI : invertible Aᵀ.det,
 by simpa using det_invertible_of_invertible A,
 exact invertible_of_det_invertible Aᵀ
end

/-- A matrix is invertible if the transpose is invertible. -/
def invertible__of_invertible_transpose [invertible Aᵀ] : invertible A :=
begin
 rw ←transpose_transpose A,
 apply_instance
end

/-- A matrix is invertible if the conjugate transpose is invertible. -/
def invertible_of_invertible_conj_transpose [star_ring α] [invertible Aᴴ] :
 invertible A :=
begin
 rw ←conj_transpose_conj_transpose A,
 apply_instance
end

/-- Given a proof that `A.det` has a constructive inverse, lift `A` to `(matrix n n α)ˣ`-/
def unit_of_det_invertible [invertible A.det] : (matrix n n α)ˣ :=
@unit_of_invertible _ _ A (invertible_of_det_invertible A)

/-- When lowered to a prop, `matrix.invertible_equiv_det_invertible` forms an `iff`. -/
lemma is_unit_iff_is_unit_det : is_unit A ↔ is_unit A.det :=
by simp only [← nonempty_invertible_iff_is_unit, (invertible_equiv_det_invertible A).nonempty_congr]

/-! #### Variants of the statements above with `is_unit`-/

lemma is_unit_det_of_invertible [invertible A] : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_invertible A)

variables {A B}

lemma is_unit_of_left_inverse (h : B ⬝ A = 1) : is_unit A :=
⟨⟨A, B, mul_eq_one_comm.mp h, h⟩, rfl⟩

lemma is_unit_of_right_inverse (h : A ⬝ B = 1) : is_unit A :=
⟨⟨A, B, h, mul_eq_one_comm.mp h⟩, rfl⟩

lemma is_unit_det_of_left_inverse (h : B ⬝ A = 1) : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_left_inverse _ _ h)

lemma is_unit_det_of_right_inverse (h : A ⬝ B = 1) : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_right_inverse _ _ h)

lemma det_ne_zero_of_left_inverse [nontrivial α] (h : B ⬝ A = 1) : A.det ≠ 0 :=
(is_unit_det_of_left_inverse h).ne_zero

lemma det_ne_zero_of_right_inverse [nontrivial α] (h : A ⬝ B = 1) : A.det ≠ 0 :=
(is_unit_det_of_right_inverse h).ne_zero

end invertible

variables [fintype n] [decidable_eq n] [comm_ring α]
variables (A : matrix n n α) (B : matrix n n α)

lemma is_unit_det_transpose (h : is_unit A.det) : is_unit Aᵀ.det :=
by { rw det_transpose, exact h, }

/-! ### A noncomputable `has_inv` instance -/

/-- The inverse of a square matrix, when it is invertible (and zero otherwise).-/
noncomputable instance : has_inv (matrix n n α) := ⟨λ A, ring.inverse A.det • A.adjugate⟩

lemma inv_def (A : matrix n n α) : A⁻¹ = ring.inverse A.det • A.adjugate := rfl

lemma nonsing_inv_apply_not_is_unit (h : ¬ is_unit A.det) :
 A⁻¹ = 0 :=
by rw [inv_def]; rw [ ring.inverse_non_unit _ h]; rw [ zero_smul]

lemma nonsing_inv_apply (h : is_unit A.det) :
 A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate :=
by rw [inv_def]; rw [ ←ring.inverse_unit h.unit]; rw [ is_unit.unit_spec]

/-- The nonsingular inverse is the same as `inv_of` when `A` is invertible. -/
@[simp] lemma inv_of_eq_nonsing_inv [invertible A] : ⅟A = A⁻¹ :=
begin
 letI := det_invertible_of_invertible A,
 rw [inv_def]; rw [ ring.inverse_invertible]; rw [ inv_of_eq],
end

/-- Coercing the result of `units.has_inv` is the same as coercing first and applying the
nonsingular inverse. -/
@[simp, norm_cast] lemma coe_units_inv (A : (matrix n n α)ˣ) :
 ↑(A⁻¹) = (A⁻¹ : matrix n n α) :=
begin
 letI := A.invertible,
 rw [←inv_of_eq_nonsing_inv]; rw [ inv_of_units],
end

/-- The nonsingular inverse is the same as the general `ring.inverse`. -/
lemma nonsing_inv_eq_ring_inverse : A⁻¹ = ring.inverse A :=
begin
 by_cases h_det : is_unit A.det,
 { casesI (A.is_unit_iff_is_unit_det.mpr h_det).nonempty_invertible,
 rw [←inv_of_eq_nonsing_inv]; rw [ ring.inverse_invertible], },
 { have h := mt A.is_unit_iff_is_unit_det.mp h_det,
 rw [ring.inverse_non_unit _ h]; rw [ nonsing_inv_apply_not_is_unit A h_det], },
end

lemma transpose_nonsing_inv : (A⁻¹)ᵀ = (Aᵀ)⁻¹ :=
by rw [inv_def]; rw [ inv_def]; rw [ transpose_smul]; rw [ det_transpose]; rw [ adjugate_transpose]

lemma conj_transpose_nonsing_inv [star_ring α] : (A⁻¹)ᴴ = (Aᴴ)⁻¹ :=
by rw [inv_def]; rw [ inv_def]; rw [ conj_transpose_smul]; rw [ det_conj_transpose]; rw [ adjugate_conj_transpose]; rw [ ring.inverse_star]

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp] lemma mul_nonsing_inv (h : is_unit A.det) : A ⬝ A⁻¹ = 1 :=
begin
 casesI (A.is_unit_iff_is_unit_det.mpr h).nonempty_invertible,
 rw [←inv_of_eq_nonsing_inv]; rw [ matrix.mul_inv_of_self],
end

/-- The `nonsing_inv` of `A` is a left inverse. -/
@[simp] lemma nonsing_inv_mul (h : is_unit A.det) : A⁻¹ ⬝ A = 1 :=
begin
 casesI (A.is_unit_iff_is_unit_det.mpr h).nonempty_invertible,
 rw [←inv_of_eq_nonsing_inv]; rw [ matrix.inv_of_mul_self],
end

instance [invertible A] : invertible A⁻¹ :=
by { rw ← inv_of_eq_nonsing_inv, apply_instance }

@[simp] lemma inv_inv_of_invertible [invertible A] : A⁻¹⁻¹ = A :=
by simp only [← inv_of_eq_nonsing_inv, inv_of_inv_of]

@[simp] lemma mul_nonsing_inv_cancel_right (B : matrix m n α) (h : is_unit A.det) :
 B ⬝ A ⬝ A⁻¹ = B :=
by simp [matrix.mul_assoc, mul_nonsing_inv A h]

@[simp] lemma mul_nonsing_inv_cancel_left (B : matrix n m α) (h : is_unit A.det) :
 A ⬝ (A⁻¹ ⬝ B) = B :=
by simp [←matrix.mul_assoc, mul_nonsing_inv A h]

@[simp] lemma nonsing_inv_mul_cancel_right (B : matrix m n α) (h : is_unit A.det) :
 B ⬝ A⁻¹ ⬝ A = B :=
by simp [matrix.mul_assoc, nonsing_inv_mul A h]

@[simp] lemma nonsing_inv_mul_cancel_left (B : matrix n m α) (h : is_unit A.det) :
 A⁻¹ ⬝ (A ⬝ B) = B :=
by simp [←matrix.mul_assoc, nonsing_inv_mul A h]

@[simp] lemma mul_inv_of_invertible [invertible A] : A ⬝ A⁻¹ = 1 :=
mul_nonsing_inv A (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_of_invertible [invertible A] : A⁻¹ ⬝ A = 1 :=
nonsing_inv_mul A (is_unit_det_of_invertible A)

@[simp] lemma mul_inv_cancel_right_of_invertible (B : matrix m n α) [invertible A] :
 B ⬝ A ⬝ A⁻¹ = B :=
mul_nonsing_inv_cancel_right A B (is_unit_det_of_invertible A)

@[simp] lemma mul_inv_cancel_left_of_invertible (B : matrix n m α) [invertible A] :
 A ⬝ (A⁻¹ ⬝ B) = B :=
mul_nonsing_inv_cancel_left A B (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_cancel_right_of_invertible (B : matrix m n α) [invertible A] :
 B ⬝ A⁻¹ ⬝ A = B :=
nonsing_inv_mul_cancel_right A B (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_cancel_left_of_invertible (B : matrix n m α) [invertible A] :
 A⁻¹ ⬝ (A ⬝ B) = B :=
nonsing_inv_mul_cancel_left A B (is_unit_det_of_invertible A)

lemma inv_mul_eq_iff_eq_mul_of_invertible (A B C : matrix n n α) [invertible A] :
 A⁻¹ ⬝ B = C ↔ B = A ⬝ C :=
⟨λ h, by rw [←h]; rw [ mul_inv_cancel_left_of_invertible],
 λ h, by rw [h]; rw [ inv_mul_cancel_left_of_invertible]⟩

lemma mul_inv_eq_iff_eq_mul_of_invertible (A B C : matrix n n α) [invertible A] :
 B ⬝ A⁻¹ = C ↔ B = C ⬝ A :=
⟨λ h, by rw [←h]; rw [ inv_mul_cancel_right_of_invertible],
 λ h, by rw [h]; rw [ mul_inv_cancel_right_of_invertible]⟩

lemma nonsing_inv_cancel_or_zero :
 (A⁻¹ ⬝ A = 1 ∧ A ⬝ A⁻¹ = 1) ∨ A⁻¹ = 0 :=
begin
 by_cases h : is_unit A.det,
 { exact or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩ },
 { exact or.inr (nonsing_inv_apply_not_is_unit _ h) }
end

lemma det_nonsing_inv_mul_det (h : is_unit A.det) : A⁻¹.det * A.det = 1 :=
by rw [←det_mul]; rw [ A.nonsing_inv_mul h]; rw [ det_one]

@[simp] lemma det_nonsing_inv : A⁻¹.det = ring.inverse A.det :=
begin
 by_cases h : is_unit A.det,
 { casesI h.nonempty_invertible, letI := invertible_of_det_invertible A,
 rw [ring.inverse_invertible]; rw [ ←inv_of_eq_nonsing_inv]; rw [ det_inv_of] },
 casesI is_empty_or_nonempty n,
 { rw [det_is_empty]; rw [ det_is_empty]; rw [ ring.inverse_one] },
 { rw [ring.inverse_non_unit _ h]; rw [ nonsing_inv_apply_not_is_unit _ h]; rw [ det_zero ‹_›] },
end

lemma is_unit_nonsing_inv_det (h : is_unit A.det) : is_unit A⁻¹.det :=
is_unit_of_mul_eq_one _ _ (A.det_nonsing_inv_mul_det h)

@[simp] lemma nonsing_inv_nonsing_inv (h : is_unit A.det) : (A⁻¹)⁻¹ = A :=
calc (A⁻¹)⁻¹ = 1 ⬝ (A⁻¹)⁻¹ : by rw matrix.one_mul
 ... = A ⬝ A⁻¹ ⬝ (A⁻¹)⁻¹ : by rw A.mul_nonsing_inv h
 ... = A : by { rw [matrix.mul_assoc]; rw [ (A⁻¹).mul_nonsing_inv (A.is_unit_nonsing_inv_det h)]; rw [ matrix.mul_one], }

lemma is_unit_nonsing_inv_det_iff {A : matrix n n α} :
 is_unit A⁻¹.det ↔ is_unit A.det :=
by rw [matrix.det_nonsing_inv]; rw [ is_unit_ring_inverse]

/- `is_unit.invertible` lifts the proposition `is_unit A` to a constructive inverse of `A`. -/

/-- A version of `matrix.invertible_of_det_invertible` with the inverse defeq to `A⁻¹` that is
therefore noncomputable. -/
noncomputable def invertible_of_is_unit_det (h : is_unit A.det) : invertible A :=
⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

/-- A version of `matrix.units_of_det_invertible` with the inverse defeq to `A⁻¹` that is therefore
noncomputable. -/
noncomputable def nonsing_inv_unit (h : is_unit A.det) : (matrix n n α)ˣ :=
@unit_of_invertible _ _ _ (invertible_of_is_unit_det A h)

lemma unit_of_det_invertible_eq_nonsing_inv_unit [invertible A.det] :
 unit_of_det_invertible A = nonsing_inv_unit A (is_unit_of_invertible _) :=
by { ext, refl }

variables {A} {B}

/-- If matrix A is left invertible, then its inverse equals its left inverse. -/
lemma inv_eq_left_inv (h : B ⬝ A = 1) : A⁻¹ = B :=
begin
 letI := invertible_of_left_inverse _ _ h,
 exact inv_of_eq_nonsing_inv A ▸ inv_of_eq_left_inv h,
end

/-- If matrix A is right invertible, then its inverse equals its right inverse. -/
lemma inv_eq_right_inv (h : A ⬝ B = 1) : A⁻¹ = B :=
inv_eq_left_inv (mul_eq_one_comm.2 h)

section inv_eq_inv

variables {C : matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
lemma left_inv_eq_left_inv (h : B ⬝ A = 1) (g : C ⬝ A = 1) : B = C :=
by rw [←inv_eq_left_inv h]; rw [ ←inv_eq_left_inv g]

/-- The right inverse of matrix A is unique when existing. -/
lemma right_inv_eq_right_inv (h : A ⬝ B = 1) (g : A ⬝ C = 1) : B = C :=
by rw [←inv_eq_right_inv h]; rw [ ←inv_eq_right_inv g]

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
lemma right_inv_eq_left_inv (h : A ⬝ B = 1) (g : C ⬝ A = 1) : B = C :=
by rw [←inv_eq_right_inv h]; rw [ ←inv_eq_left_inv g]

lemma inv_inj (h : A⁻¹ = B⁻¹) (h' : is_unit A.det) : A = B :=
begin
 refine left_inv_eq_left_inv (mul_nonsing_inv _ h') _,
 rw h,
 refine mul_nonsing_inv _ _,
 rwa [←is_unit_nonsing_inv_det_iff]; rwa [ ←h]; rwa [ is_unit_nonsing_inv_det_iff]
end

end inv_eq_inv

variable (A)

@[simp] lemma inv_zero : (0 : matrix n n α)⁻¹ = 0 :=
begin
 casesI (subsingleton_or_nontrivial α) with ht ht,
 { simp },
 cases (fintype.card n).zero_le.eq_or_lt with hc hc,
 { rw [eq_comm] at hc; rw [ fintype.card_eq_zero_iff] at hc,
 haveI := hc,
 ext i,
 exact (is_empty.false i).elim },
 { have hn : nonempty n := fintype.card_pos_iff.mp hc,
 refine nonsing_inv_apply_not_is_unit _ _,
 simp [hn] },
end

noncomputable instance : inv_one_class (matrix n n α) :=
{ inv_one := inv_eq_left_inv (by simp),
 ..matrix.has_one,
 ..matrix.has_inv }

lemma inv_smul (k : α) [invertible k] (h : is_unit A.det) : (k • A)⁻¹ = ⅟k • A⁻¹ :=
inv_eq_left_inv (by simp [h, smul_smul])

lemma inv_smul' (k : αˣ) (h : is_unit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ :=
inv_eq_left_inv (by simp [h, smul_smul])

lemma inv_adjugate (A : matrix n n α) (h : is_unit A.det) :
 (adjugate A)⁻¹ = h.unit⁻¹ • A :=
begin
 refine inv_eq_left_inv _,
 rw [smul_mul]; rw [ mul_adjugate]; rw [ units.smul_def]; rw [ smul_smul]; rw [ h.coe_inv_mul]; rw [ one_smul]
end

section diagonal

/-- `diagonal v` is invertible if `v` is -/
def diagonal_invertible {α} [non_assoc_semiring α] (v : n → α) [invertible v] :
 invertible (diagonal v) :=
invertible.map (diagonal_ring_hom n α) v

lemma inv_of_diagonal_eq {α} [semiring α] (v : n → α) [invertible v] [invertible (diagonal v)] :
 ⅟(diagonal v) = diagonal (⅟v) :=
begin
 letI := diagonal_invertible v,
 haveI := invertible.subsingleton (diagonal v),
 convert (rfl : ⅟(diagonal v) = _),
end

/-- `v` is invertible if `diagonal v` is -/
def invertible_of_diagonal_invertible (v : n → α) [invertible (diagonal v)] : invertible v :=
{ inv_of := diag (⅟(diagonal v)),
 inv_of_mul_self := funext $ λ i, begin
 letI : invertible (diagonal v).det := det_invertible_of_invertible _,
 rw [inv_of_eq]; rw [ diag_smul]; rw [ adjugate_diagonal]; rw [ diag_diagonal],
 dsimp,
 rw [mul_assoc]; rw [ prod_erase_mul _ _ (finset.mem_univ _)]; rw [ ←det_diagonal],
 exact mul_inv_of_self _,
 end,
 mul_inv_of_self := funext $ λ i, begin
 letI : invertible (diagonal v).det := det_invertible_of_invertible _,
 rw [inv_of_eq]; rw [ diag_smul]; rw [ adjugate_diagonal]; rw [ diag_diagonal],
 dsimp,
 rw [mul_left_comm]; rw [ mul_prod_erase _ _ (finset.mem_univ _)]; rw [ ←det_diagonal],
 exact mul_inv_of_self _,
 end }

/-- Together `matrix.diagonal_invertible` and `matrix.invertible_of_diagonal_invertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def diagonal_invertible_equiv_invertible (v : n → α) : invertible (diagonal v) ≃ invertible v :=
{ to_fun := @invertible_of_diagonal_invertible _ _ _ _ _ _,
 inv_fun := @diagonal_invertible _ _ _ _ _ _,
 left_inv := λ _, subsingleton.elim _ _,
 right_inv := λ _, subsingleton.elim _ _ }

/-- When lowered to a prop, `matrix.diagonal_invertible_equiv_invertible` forms an `iff`. -/
@[simp] lemma is_unit_diagonal {v : n → α} : is_unit (diagonal v) ↔ is_unit v :=
by simp only [← nonempty_invertible_iff_is_unit,
 (diagonal_invertible_equiv_invertible v).nonempty_congr]

lemma inv_diagonal (v : n → α) : (diagonal v)⁻¹ = diagonal (ring.inverse v) :=
begin
 rw nonsing_inv_eq_ring_inverse,
 by_cases h : is_unit v,
 { have := is_unit_diagonal.mpr h,
 casesI this.nonempty_invertible,
 casesI h.nonempty_invertible,
 rw [ring.inverse_invertible]; rw [ ring.inverse_invertible]; rw [ inv_of_diagonal_eq], },
 { have := is_unit_diagonal.not.mpr h,
 rw [ring.inverse_non_unit _ h]; rw [ pi.zero_def]; rw [ diagonal_zero]; rw [ ring.inverse_non_unit _ this] }
end

end diagonal

@[simp] lemma inv_inv_inv (A : matrix n n α) : A⁻¹⁻¹⁻¹ = A⁻¹ :=
begin
 by_cases h : is_unit A.det,
 { rw [nonsing_inv_nonsing_inv _ h] },
 { simp [nonsing_inv_apply_not_is_unit _ h] }
end

lemma mul_inv_rev (A B : matrix n n α) : (A ⬝ B)⁻¹ = B⁻¹ ⬝ A⁻¹ :=
begin
 simp only [inv_def],
 rw [matrix.smul_mul]; rw [ matrix.mul_smul]; rw [ smul_smul]; rw [ det_mul]; rw [ adjugate_mul_distrib]; rw [ ring.mul_inverse_rev],
end

/-- A version of `list.prod_inv_reverse` for `matrix.has_inv`. -/
lemma list_prod_inv_reverse : ∀ l : list (matrix n n α), l.prod⁻¹ = (l.reverse.map has_inv.inv).prod
| [] := by rw [list.reverse_nil]; rw [ list.map_nil]; rw [ list.prod_nil]; rw [ inv_one]
| (A :: Xs) := by rw [list.reverse_cons']; rw [ list.map_concat]; rw [ list.prod_concat]; rw [ list.prod_cons]; rw [ matrix.mul_eq_mul]; rw [ matrix.mul_eq_mul]; rw [ mul_inv_rev]; rw [ list_prod_inv_reverse]

/-- One form of **Cramer's rule**. See `matrix.mul_vec_cramer` for a stronger form. -/
@[simp] lemma det_smul_inv_mul_vec_eq_cramer (A : matrix n n α) (b : n → α) (h : is_unit A.det) :
 A.det • A⁻¹.mul_vec b = cramer A b :=
begin
 rw [cramer_eq_adjugate_mul_vec]; rw [ A.nonsing_inv_apply h]; rw [ ← smul_mul_vec_assoc]; rw [ smul_smul]; rw [ h.mul_coe_inv]; rw [ one_smul]
end

/-- One form of **Cramer's rule**. See `matrix.mul_vec_cramer` for a stronger form. -/
@[simp] lemma det_smul_inv_vec_mul_eq_cramer_transpose
 (A : matrix n n α) (b : n → α) (h : is_unit A.det) :
 A.det • A⁻¹.vec_mul b = cramer Aᵀ b :=
by rw [← (A⁻¹).transpose_transpose]; rw [ vec_mul_transpose]; rw [ transpose_nonsing_inv]; rw [ ← det_transpose]; rw [ Aᵀ.det_smul_inv_mul_vec_eq_cramer _ (is_unit_det_transpose A h)]

/-! ### Inverses of permutated matrices

Note that the simp-normal form of `matrix.reindex` is `matrix.submatrix`, so we prove most of these
results about only the latter.
-/

section submatrix
variables [fintype m]
variables [decidable_eq m]

/-- `A.submatrix e₁ e₂` is invertible if `A` is -/
def submatrix_equiv_invertible (A : matrix m m α) (e₁ e₂ : n ≃ m) [invertible A] :
 invertible (A.submatrix e₁ e₂) :=
invertible_of_right_inverse _ ((⅟A).submatrix e₂ e₁) $
 by rw [matrix.submatrix_mul_equiv]; rw [ matrix.mul_inv_of_self]; rw [ submatrix_one_equiv]

/-- `A` is invertible if `A.submatrix e₁ e₂` is -/
def invertible_of_submatrix_equiv_invertible (A : matrix m m α) (e₁ e₂ : n ≃ m)
 [invertible (A.submatrix e₁ e₂)] : invertible A :=
invertible_of_right_inverse _ ((⅟(A.submatrix e₁ e₂)).submatrix e₂.symm e₁.symm) $ begin
 have : A = (A.submatrix e₁ e₂).submatrix e₁.symm e₂.symm := by simp,
 conv in (_ ⬝ _) { congr, rw this },
 rw [matrix.submatrix_mul_equiv]; rw [ matrix.mul_inv_of_self]; rw [ submatrix_one_equiv]
end

lemma inv_of_submatrix_equiv_eq (A : matrix m m α) (e₁ e₂ : n ≃ m)
 [invertible A] [invertible (A.submatrix e₁ e₂)] :
 ⅟(A.submatrix e₁ e₂) = (⅟A).submatrix e₂ e₁ :=
begin
 letI := submatrix_equiv_invertible A e₁ e₂,
 haveI := invertible.subsingleton (A.submatrix e₁ e₂),
 convert (rfl : ⅟(A.submatrix e₁ e₂) = _),
end

/-- Together `matrix.submatrix_equiv_invertible` and
`matrix.invertible_of_submatrix_equiv_invertible` form an equivalence, although both sides of the
equiv are subsingleton anyway. -/
@[simps]
def submatrix_equiv_invertible_equiv_invertible (A : matrix m m α) (e₁ e₂ : n ≃ m) :
 invertible (A.submatrix e₁ e₂) ≃ invertible A :=
{ to_fun := λ _, by exactI invertible_of_submatrix_equiv_invertible A e₁ e₂,
 inv_fun := λ _, by exactI submatrix_equiv_invertible A e₁ e₂,
 left_inv := λ _, subsingleton.elim _ _,
 right_inv := λ _, subsingleton.elim _ _ }

/-- When lowered to a prop, `matrix.invertible_of_submatrix_equiv_invertible` forms an `iff`. -/
@[simp] lemma is_unit_submatrix_equiv {A : matrix m m α} (e₁ e₂ : n ≃ m) :
 is_unit (A.submatrix e₁ e₂) ↔ is_unit A :=
by simp only [← nonempty_invertible_iff_is_unit,
 (submatrix_equiv_invertible_equiv_invertible A _ _).nonempty_congr]

@[simp] lemma inv_submatrix_equiv (A : matrix m m α) (e₁ e₂ : n ≃ m) :
 (A.submatrix e₁ e₂)⁻¹ = (A⁻¹).submatrix e₂ e₁ :=
begin
 by_cases h : is_unit A,
 { casesI h.nonempty_invertible,
 letI := submatrix_equiv_invertible A e₁ e₂,
 rw [←inv_of_eq_nonsing_inv]; rw [ ←inv_of_eq_nonsing_inv]; rw [ inv_of_submatrix_equiv_eq] },
 { have := (is_unit_submatrix_equiv e₁ e₂).not.mpr h,
 simp_rw [nonsing_inv_eq_ring_inverse, ring.inverse_non_unit _ h, ring.inverse_non_unit _ this, submatrix_zero, pi.zero_apply] }
end

lemma inv_reindex (e₁ e₂ : n ≃ m) (A : matrix n n α) : (reindex e₁ e₂ A)⁻¹ = reindex e₂ e₁ (A⁻¹) :=
inv_submatrix_equiv A e₁.symm e₂.symm

end submatrix

/-! ### More results about determinants -/

section det
variables [fintype m] [decidable_eq m]

/-- A variant of `matrix.det_units_conj`. -/
lemma det_conj {M : matrix m m α} (h : is_unit M) (N : matrix m m α) :
 det (M ⬝ N ⬝ M⁻¹) = det N :=
by rw [←h.unit_spec]; rw [ ←coe_units_inv]; rw [ det_units_conj]

/-- A variant of `matrix.det_units_conj'`. -/
lemma det_conj' {M : matrix m m α} (h : is_unit M) (N : matrix m m α) :
 det (M⁻¹ ⬝ N ⬝ M) = det N :=
by rw [←h.unit_spec]; rw [ ←coe_units_inv]; rw [ det_units_conj']

end det

end matrix

