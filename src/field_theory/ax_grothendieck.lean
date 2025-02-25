/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.mv_polynomial.basic
import ring_theory.algebraic
import data.fintype.card

/-!
# Ax-Grothendieck for algebraic extensions of `zmod p`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves that if `R` is an algebraic extension of a finite field,
then any injective polynomial map `R^n -> R^n` is also surjective.

This proof is required for the true Ax-Grothendieck theorem, which proves the same result
for any algebraically closed field of characteristic zero.

## TODO

The proof of the theorem for characteristic zero is not in mathlib, but it is at
https://github.com/Jlh18/ModelTheoryInLean8
-/

noncomputable theory

open mv_polynomial finset function

/-- Any injective polynomial map over an algebraic extension of a finite field is surjective. -/
lemma ax_grothendieck_of_locally_finite {ι K R : Type*} [field K] [finite K] [comm_ring R]
 [finite ι] [algebra K R] (alg : algebra.is_algebraic K R)
 (ps : ι → mv_polynomial ι R)
 (hinj : injective (λ v i, eval v (ps i))) :
 surjective (λ v i, eval v (ps i)) :=
begin
 have is_int : ∀ x : R, is_integral K x,
 from λ x, is_algebraic_iff_is_integral.1 (alg x),
 classical,
 intros v,
 casesI nonempty_fintype ι,
 /- `s` is the set of all coefficients of the polynomial, as well as all of
 the coordinates of `v`, the point I am trying to find the preimage of. -/
 let s : finset R := finset.bUnion (univ : finset ι)
 (λ i, (ps i).support.image (λ x, coeff x (ps i)))
 ∪ (univ : finset ι).image v,
 have hv : ∀ i, v i ∈ algebra.adjoin K (s : set R),
 from λ j, algebra.subset_adjoin
 (mem_union_right _
 (mem_image.2 ⟨j, mem_univ _, rfl⟩)),
 have hs₁ : ∀ (i : ι) (k : ι →₀ ℕ), k ∈ (ps i).support →
 coeff k (ps i) ∈ algebra.adjoin K (s : set R),
 from λ i k hk, algebra.subset_adjoin
 (mem_union_left _ (mem_bUnion.2
 ⟨i, mem_univ _, mem_image_of_mem _ hk⟩)),
 have hs : ∀ i, mv_polynomial.eval v (ps i) ∈ algebra.adjoin K (s : set R),
 from λ i, eval_mem (hs₁ _) hv,
 letI := is_noetherian_adjoin_finset s (λ x _, is_int x),
 letI := module.is_noetherian.finite K (algebra.adjoin K (s : set R)),
 letI : finite (algebra.adjoin K (s : set R)) :=
 finite_dimensional.finite_of_finite
 K (algebra.adjoin K (s : set R)),
 /- The restriction of the polynomial map, `ps`, to the subalgebra generated by `s` -/
 let res : (ι → algebra.adjoin K (s : set R)) →
 (ι → algebra.adjoin K (s : set R)) :=
 λ x i, ⟨eval (λ j : ι, (x j : R)) (ps i),
 eval_mem (hs₁ _) (λ i, (x i).2)⟩,
 have hres_inj : injective res,
 { intros x y hxy,
 ext i,
 simp only [res, subtype.ext_iff, funext_iff] at hxy,
 exact congr_fun (hinj (funext hxy)) i },
 have hres_surj : surjective res,
 from finite.injective_iff_surjective.1 hres_inj,
 cases hres_surj (λ i, ⟨v i, hv i⟩) with w hw,
 use λ i, w i,
 simpa only [res, subtype.ext_iff, funext_iff] using hw,
end

