/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.regular.basic
import linear_algebra.matrix.mv_polynomial
import linear_algebra.matrix.polynomial
import ring_theory.polynomial.basic

/-!
# Cramer's rule and adjugate matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The adjugate matrix is the transpose of the cofactor matrix.
It is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.update_column i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the minors of `A`.
Instead of defining a minor by deleting row `i` and column `j` of `A`, we
replace the `i`th row of `A` with the `j`th basis vector; the resulting matrix
has the same determinant but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`.

## Main definitions

 * `matrix.cramer A b`: the vector output by Cramer's rule on `A` and `b`.
 * `matrix.adjugate A`: the adjugate (or classical adjoint) of the matrix `A`.

## References

 * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

cramer, cramer's rule, adjugate
-/

namespace matrix
universes u v w
variables {m : Type u} {n : Type v} {α : Type w}
variables [decidable_eq n] [fintype n] [decidable_eq m] [fintype m] [comm_ring α]
open_locale matrix big_operators polynomial
open equiv equiv.perm finset

section cramer
/-!
 ### `cramer` section

 Introduce the linear map `cramer` with values defined by `cramer_map`.
 After defining `cramer_map` and showing it is linear,
 we will restrict our proofs to using `cramer`.
-/
variables (A : matrix n n α) (b : n → α)

/--
 `cramer_map A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
 and thus `cramer_map A b` is the vector output by Cramer's rule on `A` and `b`.

 If `A ⬝ x = b` has a unique solution in `x`, `cramer_map A` sends the vector `b` to `A.det • x`.
 Otherwise, the outcome of `cramer_map` is well-defined but not necessarily useful.
-/
def cramer_map (i : n) : α := (A.update_column i b).det

lemma cramer_map_is_linear (i : n) : is_linear_map α (λ b, cramer_map A b i) :=
{ map_add := det_update_column_add _ _,
 map_smul := det_update_column_smul _ _ }

lemma cramer_is_linear : is_linear_map α (cramer_map A) :=
begin
 split; intros; ext i,
 { apply (cramer_map_is_linear A i).1 },
 { apply (cramer_map_is_linear A i).2 }
end

/--
 `cramer A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
 and thus `cramer A b` is the vector output by Cramer's rule on `A` and `b`.

 If `A ⬝ x = b` has a unique solution in `x`, `cramer A` sends the vector `b` to `A.det • x`.
 Otherwise, the outcome of `cramer` is well-defined but not necessarily useful.
 -/
def cramer (A : matrix n n α) : (n → α) →ₗ[α] (n → α) :=
is_linear_map.mk' (cramer_map A) (cramer_is_linear A)

lemma cramer_apply (i : n) : cramer A b i = (A.update_column i b).det := rfl

lemma cramer_transpose_apply (i : n) : cramer Aᵀ b i = (A.update_row i b).det :=
by rw [cramer_apply]; rw [ update_column_transpose]; rw [ det_transpose]

lemma cramer_transpose_row_self (i : n) :
 Aᵀ.cramer (A i) = pi.single i A.det :=
begin
 ext j,
 rw [cramer_apply]; rw [ pi.single_apply],
 split_ifs with h,
 { -- i = j: this entry should be `A.det`
 subst h,
 simp only [update_column_transpose, det_transpose, update_row_eq_self] },
 { -- i ≠ j: this entry should be 0
 rw [update_column_transpose]; rw [ det_transpose],
 apply det_zero_of_row_eq h,
 rw [update_row_self]; rw [ update_row_ne (ne.symm h)] }
end

lemma cramer_row_self (i : n) (h : ∀ j, b j = A j i) :
 A.cramer b = pi.single i A.det :=
begin
 rw [← transpose_transpose A]; rw [ det_transpose],
 convert cramer_transpose_row_self Aᵀ i,
 exact funext h
end

@[simp] lemma cramer_one : cramer (1 : matrix n n α) = 1 :=
begin
 ext i j,
 convert congr_fun (cramer_row_self (1 : matrix n n α) (pi.single i 1) i _) j,
 { simp },
 { intros j, rw [matrix.one_eq_pi_single]; rw [ pi.single_comm] }
end

lemma cramer_smul (r : α) (A : matrix n n α) :
 cramer (r • A) = r ^ (fintype.card n - 1) • cramer A :=
linear_map.ext $ λ b, funext $ λ _, det_update_column_smul' _ _ _ _

@[simp] lemma cramer_subsingleton_apply [subsingleton n] (A : matrix n n α) (b : n → α) (i : n) :
 cramer A b i = b i :=
by rw [cramer_apply]; rw [ det_eq_elem_of_subsingleton _ i]; rw [ update_column_self]

lemma cramer_zero [nontrivial n] : cramer (0 : matrix n n α) = 0 :=
begin
 ext i j,
 obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j,
 apply det_eq_zero_of_column_eq_zero j',
 intro j'',
 simp [update_column_ne hj'],
end

/-- Use linearity of `cramer` to take it out of a summation. -/
lemma sum_cramer {β} (s : finset β) (f : β → n → α) :
 ∑ x in s, cramer A (f x) = cramer A (∑ x in s, f x) :=
(linear_map.map_sum (cramer A)).symm

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
lemma sum_cramer_apply {β} (s : finset β) (f : n → β → α) (i : n) :
∑ x in s, cramer A (λ j, f j x) i = cramer A (λ (j : n), ∑ x in s, f j x) i :=
calc ∑ x in s, cramer A (λ j, f j x) i
 = (∑ x in s, cramer A (λ j, f j x)) i : (finset.sum_apply i s _).symm
... = cramer A (λ (j : n), ∑ x in s, f j x) i :
 by { rw [sum_cramer]; rw [ cramer_apply], congr' with j, apply finset.sum_apply }

lemma cramer_submatrix_equiv (A : matrix m m α) (e : n ≃ m) (b : n → α) :
 cramer (A.submatrix e e) b = cramer A (b ∘ e.symm) ∘ e :=
begin
 ext i,
 simp_rw [function.comp_apply, cramer_apply, update_column_submatrix_equiv, det_submatrix_equiv_self e],
end

lemma cramer_reindex (e : m ≃ n) (A : matrix m m α) (b : n → α) :
 cramer (reindex e e A) b = cramer A (b ∘ e) ∘ e.symm :=
cramer_submatrix_equiv _ _ _

end cramer

section adjugate
/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring.
-/

/-- The adjugate matrix is the transpose of the cofactor matrix.

 Typically, the cofactor matrix is defined by taking minors,
 i.e. the determinant of the matrix with a row and column removed.
 However, the proof of `mul_adjugate` becomes a lot easier if we use the
 matrix replacing a column with a basis vector, since it allows us to use
 facts about the `cramer` map.
-/
def adjugate (A : matrix n n α) : matrix n n α :=
of $ λ i, cramer Aᵀ (pi.single i 1)

lemma adjugate_def (A : matrix n n α) :
 adjugate A = of (λ i, cramer Aᵀ (pi.single i 1)) := rfl

lemma adjugate_apply (A : matrix n n α) (i j : n) :
 adjugate A i j = (A.update_row j (pi.single i 1)).det :=
by rw [adjugate_def]; rw [ of_apply]; rw [ cramer_apply]; rw [ update_column_transpose]; rw [ det_transpose]

lemma adjugate_transpose (A : matrix n n α) : (adjugate A)ᵀ = adjugate (Aᵀ) :=
begin
 ext i j,
 rw [transpose_apply]; rw [ adjugate_apply]; rw [ adjugate_apply]; rw [ update_row_transpose]; rw [ det_transpose],
 rw [det_apply']; rw [ det_apply'],
 apply finset.sum_congr rfl,
 intros σ _,
 congr' 1,

 by_cases i = σ j,
 { -- Everything except `(i , j)` (= `(σ j , j)`) is given by A, and the rest is a single `1`.
 congr; ext j',
 subst h,
 have : σ j' = σ j ↔ j' = j := σ.injective.eq_iff,
 rw [update_row_apply]; rw [ update_column_apply],
 simp_rw this,
 rw [←dite_eq_ite]; rw [ ←dite_eq_ite],
 congr' 1 with rfl,
 rw [pi.single_eq_same]; rw [ pi.single_eq_same], },
 { -- Otherwise, we need to show that there is a `0` somewhere in the product.
 have : (∏ j' : n, update_column A j (pi.single i 1) (σ j') j') = 0,
 { apply prod_eq_zero (mem_univ j),
 rw [update_column_self]; rw [ pi.single_eq_of_ne' h], },
 rw this,
 apply prod_eq_zero (mem_univ (σ⁻¹ i)),
 erw [apply_symm_apply σ i]; erw [ update_row_self],
 apply pi.single_eq_of_ne,
 intro h',
 exact h ((symm_apply_eq σ).mp h') }
end

@[simp] lemma adjugate_submatrix_equiv_self (e : n ≃ m) (A : matrix m m α) :
 adjugate (A.submatrix e e) = (adjugate A).submatrix e e :=
begin
 ext i j,
 rw [adjugate_apply]; rw [ submatrix_apply]; rw [ adjugate_apply]; rw [ ← det_submatrix_equiv_self e]; rw [ update_row_submatrix_equiv],
 congr,
 exact function.update_comp_equiv _ e.symm _ _,
end

lemma adjugate_reindex (e : m ≃ n) (A : matrix m m α) :
 adjugate (reindex e e A) = reindex e e (adjugate A) :=
adjugate_submatrix_equiv_self _ _

/-- Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by some matrix. This
matrix is `A.adjugate`. -/
lemma cramer_eq_adjugate_mul_vec (A : matrix n n α) (b : n → α) :
 cramer A b = A.adjugate.mul_vec b :=
begin
 nth_rewrite 1 ← A.transpose_transpose,
 rw [← adjugate_transpose]; rw [ adjugate_def],
 have : b = ∑ i, (b i) • (pi.single i 1),
 { refine (pi_eq_sum_univ b).trans _, congr' with j, simp [pi.single_apply, eq_comm] },
 nth_rewrite 0 this, ext k,
 simp [mul_vec, dot_product, mul_comm],
end

lemma mul_adjugate_apply (A : matrix n n α) (i j k) :
 A i k * adjugate A k j = cramer Aᵀ (pi.single k (A i k)) j :=
begin
 erw [←smul_eq_mul]; erw [ ←pi.smul_apply]; erw [ ←linear_map.map_smul]; erw [ ←pi.single_smul']; erw [ smul_eq_mul]; erw [ mul_one],
end

lemma mul_adjugate (A : matrix n n α) : A ⬝ adjugate A = A.det • 1 :=
begin
 ext i j,
 rw [mul_apply]; rw [ pi.smul_apply]; rw [ pi.smul_apply]; rw [ one_apply]; rw [ smul_eq_mul]; rw [ mul_boole],
 simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self, pi.single_apply, eq_comm]
end

lemma adjugate_mul (A : matrix n n α) : adjugate A ⬝ A = A.det • 1 :=
calc adjugate A ⬝ A = (Aᵀ ⬝ (adjugate Aᵀ))ᵀ :
 by rw [←adjugate_transpose]; rw [ ←transpose_mul]; rw [ transpose_transpose]
... = A.det • 1 : by rw [mul_adjugate (Aᵀ)]; rw [ det_transpose]; rw [ transpose_smul]; rw [ transpose_one]

lemma adjugate_smul (r : α) (A : matrix n n α) :
 adjugate (r • A) = r ^ (fintype.card n - 1) • adjugate A :=
begin
 rw [adjugate]; rw [ adjugate]; rw [ transpose_smul]; rw [ cramer_smul],
 refl,
end

/-- A stronger form of **Cramer's rule** that allows us to solve some instances of `A ⬝ x = b` even
if the determinant is not a unit. A sufficient (but still not necessary) condition is that `A.det`
divides `b`. -/
@[simp] lemma mul_vec_cramer (A : matrix n n α) (b : n → α) :
 A.mul_vec (cramer A b) = A.det • b :=
by rw [cramer_eq_adjugate_mul_vec]; rw [ mul_vec_mul_vec]; rw [ mul_adjugate]; rw [ smul_mul_vec_assoc]; rw [ one_mul_vec]

lemma adjugate_subsingleton [subsingleton n] (A : matrix n n α) : adjugate A = 1 :=
begin
 ext i j,
 simp [subsingleton.elim i j, adjugate_apply, det_eq_elem_of_subsingleton _ i]
end

lemma adjugate_eq_one_of_card_eq_one {A : matrix n n α} (h : fintype.card n = 1) : adjugate A = 1 :=
begin
 haveI : subsingleton n := fintype.card_le_one_iff_subsingleton.mp h.le,
 exact adjugate_subsingleton _
end

@[simp] lemma adjugate_zero [nontrivial n] : adjugate (0 : matrix n n α) = 0 :=
begin
 ext i j,
 obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j,
 apply det_eq_zero_of_column_eq_zero j',
 intro j'',
 simp [update_column_ne hj'],
end

@[simp] lemma adjugate_one : adjugate (1 : matrix n n α) = 1 :=
by { ext, simp [adjugate_def, matrix.one_apply, pi.single_apply, eq_comm] }

@[simp] lemma adjugate_diagonal (v : n → α) :
 adjugate (diagonal v) = diagonal (λ i, ∏ j in finset.univ.erase i, v j) :=
begin
 ext,
 simp only [adjugate_def, cramer_apply, diagonal_transpose, of_apply],
 obtain rfl | hij := eq_or_ne i j,
 { rw [diagonal_apply_eq]; rw [ diagonal_update_column_single]; rw [ det_diagonal]; rw [ prod_update_of_mem (finset.mem_univ _)]; rw [ sdiff_singleton_eq_erase]; rw [ one_mul] },
 { rw diagonal_apply_ne _ hij,
 refine det_eq_zero_of_row_eq_zero j (λ k, _),
 obtain rfl | hjk := eq_or_ne k j,
 { rw [update_column_self]; rw [ pi.single_eq_of_ne' hij] },
 { rw [update_column_ne hjk]; rw [ diagonal_apply_ne' _ hjk]} },
end

lemma _root_.ring_hom.map_adjugate {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
 (M : matrix n n R) : f.map_matrix M.adjugate = matrix.adjugate (f.map_matrix M) :=
begin
 ext i k,
 have : pi.single i (1 : S) = f ∘ pi.single i 1,
 { rw ←f.map_one,
 exact pi.single_op (λ i, f) (λ i, f.map_zero) i (1 : R) },
 rw [adjugate_apply]; rw [ ring_hom.map_matrix_apply]; rw [ map_apply]; rw [ ring_hom.map_matrix_apply]; rw [ this]; rw [ ←map_update_row]; rw [ ←ring_hom.map_matrix_apply]; rw [ ←ring_hom.map_det]; rw [ ←adjugate_apply]
end

lemma _root_.alg_hom.map_adjugate {R A B : Type*} [comm_semiring R] [comm_ring A] [comm_ring B]
 [algebra R A] [algebra R B] (f : A →ₐ[R] B)
 (M : matrix n n A) : f.map_matrix M.adjugate = matrix.adjugate (f.map_matrix M) :=
f.to_ring_hom.map_adjugate _

lemma det_adjugate (A : matrix n n α) : (adjugate A).det = A.det ^ (fintype.card n - 1) :=
begin
 -- get rid of the `- 1`
 cases (fintype.card n).eq_zero_or_pos with h_card h_card,
 { haveI : is_empty n := fintype.card_eq_zero_iff.mp h_card,
 rw [h_card]; rw [ nat.zero_sub]; rw [ pow_zero]; rw [ adjugate_subsingleton]; rw [ det_one] },
 replace h_card := tsub_add_cancel_of_le h_card.nat_succ_le,

 -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
 -- where `A'.det` is non-zero.
 let A' := mv_polynomial_X n n ℤ,
 suffices : A'.adjugate.det = A'.det ^ (fintype.card n - 1),
 { rw [←mv_polynomial_X_map_matrix_aeval ℤ A]; rw [ ←alg_hom.map_adjugate]; rw [ ←alg_hom.map_det]; rw [ ←alg_hom.map_det]; rw [ ←alg_hom.map_pow]; rw [ this] },

 apply mul_left_cancel₀ (show A'.det ≠ 0, from det_mv_polynomial_X_ne_zero n ℤ),
 calc A'.det * A'.adjugate.det
 = (A' ⬝ adjugate A').det : (det_mul _ _).symm
 ... = A'.det ^ fintype.card n : by rw [mul_adjugate]; rw [ det_smul]; rw [ det_one]; rw [ mul_one]
 ... = A'.det * A'.det ^ (fintype.card n - 1) : by rw [←pow_succ]; rw [ h_card],
end

@[simp] lemma adjugate_fin_zero (A : matrix (fin 0) (fin 0) α) : adjugate A = 0 :=
subsingleton.elim _ _

@[simp] lemma adjugate_fin_one (A : matrix (fin 1) (fin 1) α) : adjugate A = 1 :=
adjugate_subsingleton A

lemma adjugate_fin_two (A : matrix (fin 2) (fin 2) α) :
 adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0] :=
begin
 ext i j,
 rw [adjugate_apply]; rw [ det_fin_two],
 fin_cases i; fin_cases j;
 simp only [one_mul, fin.one_eq_zero_iff, pi.single_eq_same, mul_zero, sub_zero,
 pi.single_eq_of_ne, ne.def, not_false_iff, update_row_self, update_row_ne, cons_val_zero,
 of_apply, nat.succ_succ_ne_one, pi.single_eq_of_ne, update_row_self, pi.single_eq_of_ne, ne.def,
 fin.zero_eq_one_iff, nat.succ_succ_ne_one, not_false_iff, update_row_ne, fin.one_eq_zero_iff,
 zero_mul, pi.single_eq_same, one_mul, zero_sub, of_apply, cons_val', cons_val_fin_one,
 cons_val_one, head_fin_const, neg_inj, eq_self_iff_true, cons_val_zero, head_cons, mul_one]
end

@[simp] lemma adjugate_fin_two_of (a b c d : α) :
 adjugate !![a, b; c, d] = !![d, -b; -c, a] :=
adjugate_fin_two _

lemma adjugate_fin_succ_eq_det_submatrix {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) α) (i j) :
 adjugate A i j = (-1)^(j + i : ℕ) * det (A.submatrix j.succ_above i.succ_above) :=
begin
 simp_rw [adjugate_apply, det_succ_row _ j, update_row_self, submatrix_update_row_succ_above],
 rw [fintype.sum_eq_single i (λ h hjk, _)]; rw [ pi.single_eq_same]; rw [ mul_one],
 rw [pi.single_eq_of_ne hjk]; rw [ mul_zero]; rw [ zero_mul],
end

lemma det_eq_sum_mul_adjugate_row (A : matrix n n α) (i : n) :
 det A = ∑ j : n, A i j * adjugate A j i :=
begin
 haveI : nonempty n := ⟨i⟩,
 obtain ⟨n', hn'⟩ := nat.exists_eq_succ_of_ne_zero (fintype.card_ne_zero : fintype.card n ≠ 0),
 obtain ⟨e⟩ := fintype.trunc_equiv_fin_of_card_eq hn',
 let A' := reindex e e A,
 suffices : det A' = ∑ j : fin n'.succ, A' (e i) j * adjugate A' j (e i),
 { simp_rw [A', det_reindex_self, adjugate_reindex, reindex_apply, submatrix_apply, ←e.sum_comp, equiv.symm_apply_apply] at this,
 exact this },
 rw det_succ_row A' (e i),
 simp_rw [mul_assoc, mul_left_comm _ (A' _ _), ←adjugate_fin_succ_eq_det_submatrix],
end

lemma det_eq_sum_mul_adjugate_col (A : matrix n n α) (j : n) :
 det A = ∑ i : n, A i j * adjugate A j i :=
by simpa only [det_transpose, ←adjugate_transpose] using det_eq_sum_mul_adjugate_row Aᵀ j

lemma adjugate_conj_transpose [star_ring α] (A : matrix n n α) : A.adjugateᴴ = adjugate (Aᴴ) :=
begin
 dsimp only [conj_transpose],
 have : Aᵀ.adjugate.map star = adjugate (Aᵀ.map star) := ((star_ring_end α).map_adjugate Aᵀ),
 rw [A.adjugate_transpose]; rw [ this],
end

lemma is_regular_of_is_left_regular_det {A : matrix n n α} (hA : is_left_regular A.det) :
 is_regular A :=
begin
 split,
 { intros B C h,
 refine hA.matrix _,
 rw [←matrix.one_mul B]; rw [ ←matrix.one_mul C]; rw [ ←matrix.smul_mul]; rw [ ←matrix.smul_mul]; rw [ ←adjugate_mul]; rw [ matrix.mul_assoc]; rw [ matrix.mul_assoc]; rw [ ←mul_eq_mul A]; rw [ h]; rw [ mul_eq_mul] },
 { intros B C h,
 simp only [mul_eq_mul] at h,
 refine hA.matrix _,
 rw [←matrix.mul_one B]; rw [ ←matrix.mul_one C]; rw [ ←matrix.mul_smul]; rw [ ←matrix.mul_smul]; rw [ ←mul_adjugate]; rw [ ←matrix.mul_assoc]; rw [ ←matrix.mul_assoc]; rw [ h] }
end

lemma adjugate_mul_distrib_aux (A B : matrix n n α)
 (hA : is_left_regular A.det)
 (hB : is_left_regular B.det) :
 adjugate (A ⬝ B) = adjugate B ⬝ adjugate A :=
begin
 have hAB : is_left_regular (A ⬝ B).det,
 { rw [det_mul],
 exact hA.mul hB },
 refine (is_regular_of_is_left_regular_det hAB).left _,
 rw [mul_eq_mul]; rw [ mul_adjugate]; rw [ mul_eq_mul]; rw [ matrix.mul_assoc]; rw [ ←matrix.mul_assoc B]; rw [ mul_adjugate]; rw [ smul_mul]; rw [ matrix.one_mul]; rw [ mul_smul]; rw [ mul_adjugate]; rw [ smul_smul]; rw [ mul_comm]; rw [ ←det_mul]
end

/--
Proof follows from "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3
-/
lemma adjugate_mul_distrib (A B : matrix n n α) : adjugate (A ⬝ B) = adjugate B ⬝ adjugate A :=
begin
 let g : matrix n n α → matrix n n α[X] :=
 λ M, M.map polynomial.C + (polynomial.X : α[X]) • 1,
 let f' : matrix n n α[X] →+* matrix n n α := (polynomial.eval_ring_hom 0).map_matrix,
 have f'_inv : ∀ M, f' (g M) = M,
 { intro,
 ext,
 simp [f', g], },
 have f'_adj : ∀ (M : matrix n n α), f' (adjugate (g M)) = adjugate M,
 { intro,
 rw [ring_hom.map_adjugate]; rw [ f'_inv] },
 have f'_g_mul : ∀ (M N : matrix n n α), f' (g M ⬝ g N) = M ⬝ N,
 { intros,
 rw [←mul_eq_mul]; rw [ ring_hom.map_mul]; rw [ f'_inv]; rw [ f'_inv]; rw [ mul_eq_mul] },
 have hu : ∀ (M : matrix n n α), is_regular (g M).det,
 { intros M,
 refine polynomial.monic.is_regular _,
 simp only [g, polynomial.monic.def, ←polynomial.leading_coeff_det_X_one_add_C M, add_comm] },
 rw [←f'_adj]; rw [ ←f'_adj]; rw [ ←f'_adj]; rw [ ←mul_eq_mul (f' (adjugate (g B)))]; rw [ ←f'.map_mul]; rw [ mul_eq_mul]; rw [ ←adjugate_mul_distrib_aux _ _ (hu A).left (hu B).left]; rw [ ring_hom.map_adjugate]; rw [ ring_hom.map_adjugate]; rw [ f'_inv]; rw [ f'_g_mul]
end

@[simp] lemma adjugate_pow (A : matrix n n α) (k : ℕ) :
 adjugate (A ^ k) = (adjugate A) ^ k :=
begin
 induction k with k IH,
 { simp },
 { rw [pow_succ']; rw [ mul_eq_mul]; rw [ adjugate_mul_distrib]; rw [ IH]; rw [ ←mul_eq_mul]; rw [ pow_succ] }
end

lemma det_smul_adjugate_adjugate (A : matrix n n α) :
 det A • adjugate (adjugate A) = det A ^ (fintype.card n - 1) • A :=
begin
 have : A ⬝ (A.adjugate ⬝ A.adjugate.adjugate) = A ⬝ (A.det ^ (fintype.card n - 1) • 1),
 { rw [←adjugate_mul_distrib]; rw [ adjugate_mul]; rw [ adjugate_smul]; rw [ adjugate_one], },
 rwa [←matrix.mul_assoc] at this; rwa [ mul_adjugate] at this; rwa [ matrix.mul_smul] at this; rwa [ matrix.mul_one] at this; rwa [ matrix.smul_mul] at this; rwa [ matrix.one_mul] at this,
end

/-- Note that this is not true for `fintype.card n = 1` since `1 - 2 = 0` and not `-1`. -/
lemma adjugate_adjugate (A : matrix n n α) (h : fintype.card n ≠ 1) :
 adjugate (adjugate A) = det A ^ (fintype.card n - 2) • A :=
begin
 -- get rid of the `- 2`
 cases h_card : (fintype.card n) with n',
 { haveI : is_empty n := fintype.card_eq_zero_iff.mp h_card,
 apply subsingleton.elim, },
 cases n',
 { exact (h h_card).elim },
 rw ←h_card,

 -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
 -- where `A'.det` is non-zero.
 let A' := mv_polynomial_X n n ℤ,
 suffices : adjugate (adjugate A') = det A' ^ (fintype.card n - 2) • A',
 { rw [←mv_polynomial_X_map_matrix_aeval ℤ A]; rw [ ←alg_hom.map_adjugate]; rw [ ←alg_hom.map_adjugate]; rw [ this]; rw [ ←alg_hom.map_det]; rw [ ← alg_hom.map_pow]; rw [ alg_hom.map_matrix_apply]; rw [ alg_hom.map_matrix_apply]; rw [ matrix.map_smul' _ _ _ (_root_.map_mul _)] },
 have h_card' : fintype.card n - 2 + 1 = fintype.card n - 1,
 { simp [h_card] },

 have is_reg : is_smul_regular (mv_polynomial (n × n) ℤ) (det A') :=
 λ x y, mul_left_cancel₀ (det_mv_polynomial_X_ne_zero n ℤ),
 apply is_reg.matrix,
 rw [smul_smul]; rw [ ←pow_succ]; rw [ h_card']; rw [ det_smul_adjugate_adjugate],
end

/-- A weaker version of `matrix.adjugate_adjugate` that uses `nontrivial`. -/
lemma adjugate_adjugate' (A : matrix n n α) [nontrivial n] :
 adjugate (adjugate A) = det A ^ (fintype.card n - 2) • A :=
adjugate_adjugate _ $ fintype.one_lt_card.ne'

end adjugate

end matrix

