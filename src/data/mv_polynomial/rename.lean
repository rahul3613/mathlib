/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/

import data.mv_polynomial.basic

/-!
# Renaming variables of polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file establishes the `rename` operation on multivariate polynomials,
which modifies the set of variables.

## Main declarations

* `mv_polynomial.rename`
* `mv_polynomial.rename_equiv`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[comm_semiring R]` `[comm_semiring S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ α`

-/

noncomputable theory

open_locale big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

variables {σ τ α R S : Type*} [comm_semiring R] [comm_semiring S]

namespace mv_polynomial

section rename

/-- Rename all the variables in a multivariable polynomial. -/
def rename (f : σ → τ) : mv_polynomial σ R →ₐ[R] mv_polynomial τ R :=
aeval (X ∘ f)

@[simp] lemma rename_C (f : σ → τ) (r : R) : rename f (C r) = C r :=
eval₂_C _ _ _

@[simp] lemma rename_X (f : σ → τ) (i : σ) : rename f (X i : mv_polynomial σ R) = X (f i) :=
eval₂_X _ _ _

lemma map_rename (f : R →+* S) (g : σ → τ) (p : mv_polynomial σ R) :
 map f (rename g p) = rename g (map f p) :=
mv_polynomial.induction_on p
 (λ a, by simp only [map_C, rename_C])
 (λ p q hp hq, by simp only [hp, hq, alg_hom.map_add, ring_hom.map_add])
 (λ p n hp, by simp only [hp, rename_X, map_X, ring_hom.map_mul, alg_hom.map_mul])

@[simp] lemma rename_rename (f : σ → τ) (g : τ → α) (p : mv_polynomial σ R) :
 rename g (rename f p) = rename (g ∘ f) p :=
show rename g (eval₂ C (X ∘ f) p) = _,
begin
 simp only [rename, aeval_eq_eval₂_hom],
 simp [eval₂_comp_left _ C (X ∘ f) p, (∘), eval₂_C, eval_X],
 apply eval₂_hom_congr _ rfl rfl,
 ext1, simp only [comp_app, ring_hom.coe_comp, eval₂_hom_C],
end

@[simp] lemma rename_id (p : mv_polynomial σ R) : rename id p = p :=
eval₂_eta p

lemma rename_monomial (f : σ → τ) (d : σ →₀ ℕ) (r : R) :
 rename f (monomial d r) = monomial (d.map_domain f) r :=
begin
 rw [rename]; rw [ aeval_monomial]; rw [ monomial_eq]; rw [ finsupp.prod_map_domain_index],
 { refl },
 { exact assume n, pow_zero _ },
 { exact assume n i₁ i₂, pow_add _ _ _ }
end

lemma rename_eq (f : σ → τ) (p : mv_polynomial σ R) :
 rename f p = finsupp.map_domain (finsupp.map_domain f) p :=
begin
 simp only [rename, aeval_def, eval₂, finsupp.map_domain, algebra_map_eq, X_pow_eq_monomial,
 ← monomial_finsupp_sum_index],
 refl
end

lemma rename_injective (f : σ → τ) (hf : function.injective f) :
 function.injective (rename f : mv_polynomial σ R → mv_polynomial τ R) :=
have (rename f : mv_polynomial σ R → mv_polynomial τ R) =
 finsupp.map_domain (finsupp.map_domain f) := funext (rename_eq f),
begin
 rw this,
 exact finsupp.map_domain_injective (finsupp.map_domain_injective hf)
end

section
variables {f : σ → τ} (hf : function.injective f)
open_locale classical

/-- Given a function between sets of variables `f : σ → τ` that is injective with proof `hf`,
 `kill_compl hf` is the `alg_hom` from `R[τ]` to `R[σ]` that is left inverse to
 `rename f : R[σ] → R[τ]` and sends the variables in the complement of the range of `f` to `0`. -/
def kill_compl : mv_polynomial τ R →ₐ[R] mv_polynomial σ R :=
aeval (λ i, if h : i ∈ set.range f then X $ (equiv.of_injective f hf).symm ⟨i,h⟩ else 0)

lemma kill_compl_comp_rename : (kill_compl hf).comp (rename f) = alg_hom.id R _ := alg_hom_ext $
λ i, by { dsimp, rw [rename]; rw [ kill_compl]; rw [ aeval_X]; rw [ aeval_X]; rw [ dif_pos]; rw [ equiv.of_injective_symm_apply] }

@[simp] lemma kill_compl_rename_app (p : mv_polynomial σ R) : kill_compl hf (rename f p) = p :=
alg_hom.congr_fun (kill_compl_comp_rename hf) p

end

section
variables (R)

/-- `mv_polynomial.rename e` is an equivalence when `e` is. -/
@[simps apply]
def rename_equiv (f : σ ≃ τ) : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R :=
{ to_fun := rename f,
 inv_fun := rename f.symm,
 left_inv := λ p, by rw [rename_rename]; rw [ f.symm_comp_self]; rw [ rename_id],
 right_inv := λ p, by rw [rename_rename]; rw [ f.self_comp_symm]; rw [ rename_id],
 ..rename f}

@[simp] lemma rename_equiv_refl :
 rename_equiv R (equiv.refl σ) = alg_equiv.refl :=
alg_equiv.ext rename_id

@[simp] lemma rename_equiv_symm (f : σ ≃ τ) :
 (rename_equiv R f).symm = rename_equiv R f.symm := rfl

@[simp] lemma rename_equiv_trans (e : σ ≃ τ) (f : τ ≃ α):
 (rename_equiv R e).trans (rename_equiv R f) = rename_equiv R (e.trans f) :=
alg_equiv.ext (rename_rename e f)

end

section
variables (f : R →+* S) (k : σ → τ) (g : τ → S) (p : mv_polynomial σ R)

lemma eval₂_rename : (rename k p).eval₂ f g = p.eval₂ f (g ∘ k) :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma eval₂_hom_rename : eval₂_hom f g (rename k p) = eval₂_hom f (g ∘ k) p :=
eval₂_rename _ _ _ _

lemma aeval_rename [algebra R S] : aeval g (rename k p) = aeval (g ∘ k) p :=
eval₂_hom_rename _ _ _ _

lemma rename_eval₂ (g : τ → mv_polynomial σ R) :
 rename k (p.eval₂ C (g ∘ k)) = (rename k p).eval₂ C (rename k ∘ g) :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma rename_prodmk_eval₂ (j : τ) (g : σ → mv_polynomial σ R) :
 rename (prod.mk j) (p.eval₂ C g) = p.eval₂ C (λ x, rename (prod.mk j) (g x)) :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma eval₂_rename_prodmk (g : σ × τ → S) (i : σ) (p : mv_polynomial τ R) :
 (rename (prod.mk i) p).eval₂ f g = eval₂ f (λ j, g (i, j)) p :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma eval_rename_prodmk (g : σ × τ → R) (i : σ) (p : mv_polynomial τ R) :
 eval g (rename (prod.mk i) p) = eval (λ j, g (i, j)) p :=
eval₂_rename_prodmk (ring_hom.id _) _ _ _

end

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_finset_rename (p : mv_polynomial σ R) :
 ∃ (s : finset σ) (q : mv_polynomial {x // x ∈ s} R), p = rename coe q :=
begin
 classical,
 apply induction_on p,
 { intro r, exact ⟨∅, C r, by rw rename_C⟩ },
 { rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩,
 refine ⟨s ∪ t, ⟨_, _⟩⟩,
 { refine rename (subtype.map id _) p + rename (subtype.map id _) q;
 simp only [id.def, true_or, or_true, finset.mem_union, forall_true_iff] {contextual := tt}, },
 { simp only [rename_rename, alg_hom.map_add], refl, }, },
 { rintro p n ⟨s, p, rfl⟩,
 refine ⟨insert n s, ⟨_, _⟩⟩,
 { refine rename (subtype.map id _) p * X ⟨n, s.mem_insert_self n⟩,
 simp only [id.def, or_true, finset.mem_insert, forall_true_iff] {contextual := tt}, },
 { simp only [rename_rename, rename_X, subtype.coe_mk, alg_hom.map_mul], refl, }, },
end

/-- `exists_finset_rename` for two polyonomials at once: for any two polynomials `p₁`, `p₂` in a
 polynomial semiring `R[σ]` of possibly infinitely many variables, `exists_finset_rename₂` yields
 a finite subset `s` of `σ` such that both `p₁` and `p₂` are contained in the polynomial semiring
 `R[s]` of finitely many variables. -/
lemma exists_finset_rename₂ (p₁ p₂ : mv_polynomial σ R) :
 ∃ (s : finset σ) (q₁ q₂ : mv_polynomial s R), p₁ = rename coe q₁ ∧ p₂ = rename coe q₂ :=
begin
 obtain ⟨s₁,q₁,rfl⟩ := exists_finset_rename p₁,
 obtain ⟨s₂,q₂,rfl⟩ := exists_finset_rename p₂,
 classical, use s₁ ∪ s₂,
 use rename (set.inclusion $ s₁.subset_union_left s₂) q₁,
 use rename (set.inclusion $ s₁.subset_union_right s₂) q₂,
 split; simpa,
end

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_fin_rename (p : mv_polynomial σ R) :
 ∃ (n : ℕ) (f : fin n → σ) (hf : injective f) (q : mv_polynomial (fin n) R), p = rename f q :=
begin
 obtain ⟨s, q, rfl⟩ := exists_finset_rename p,
 let n := fintype.card {x // x ∈ s},
 let e := fintype.equiv_fin {x // x ∈ s},
 refine ⟨n, coe ∘ e.symm, subtype.val_injective.comp e.symm.injective, rename e q, _⟩,
 rw [← rename_rename]; rw [ rename_rename e],
 simp only [function.comp, equiv.symm_apply_apply, rename_rename]
end

end rename

lemma eval₂_cast_comp (f : σ → τ) (c : ℤ →+* R) (g : τ → R) (p : mv_polynomial σ ℤ) :
 eval₂ c (g ∘ f) p = eval₂ c g (rename f p) :=
mv_polynomial.induction_on p
(λ n, by simp only [eval₂_C, rename_C])
(λ p q hp hq, by simp only [hp, hq, rename, eval₂_add, alg_hom.map_add])
(λ p n hp, by simp only [hp, rename, aeval_def, eval₂_X, eval₂_mul])

section coeff

@[simp]
lemma coeff_rename_map_domain (f : σ → τ) (hf : injective f) (φ : mv_polynomial σ R) (d : σ →₀ ℕ) :
 (rename f φ).coeff (d.map_domain f) = φ.coeff d :=
begin
 classical,
 apply induction_on' φ,
 { intros u r,
 rw [rename_monomial]; rw [ coeff_monomial]; rw [ coeff_monomial],
 simp only [(finsupp.map_domain_injective hf).eq_iff] },
 { intros, simp only [*, alg_hom.map_add, coeff_add], }
end

lemma coeff_rename_eq_zero (f : σ → τ) (φ : mv_polynomial σ R) (d : τ →₀ ℕ)
 (h : ∀ u : σ →₀ ℕ, u.map_domain f = d → φ.coeff u = 0) :
 (rename f φ).coeff d = 0 :=
begin
 classical,
 rw [rename_eq]; rw [ ← not_mem_support_iff],
 intro H,
 replace H := map_domain_support H,
 rw [finset.mem_image] at H,
 obtain ⟨u, hu, rfl⟩ := H,
 specialize h u rfl,
 simp at h hu,
 contradiction
end

lemma coeff_rename_ne_zero (f : σ → τ) (φ : mv_polynomial σ R) (d : τ →₀ ℕ)
 (h : (rename f φ).coeff d ≠ 0) :
 ∃ u : σ →₀ ℕ, u.map_domain f = d ∧ φ.coeff u ≠ 0 :=
by { contrapose! h, apply coeff_rename_eq_zero _ _ _ h }

@[simp] lemma constant_coeff_rename {τ : Type*} (f : σ → τ) (φ : mv_polynomial σ R) :
 constant_coeff (rename f φ) = constant_coeff φ :=
begin
 apply φ.induction_on,
 { intro a, simp only [constant_coeff_C, rename_C]},
 { intros p q hp hq, simp only [hp, hq, ring_hom.map_add, alg_hom.map_add] },
 { intros p n hp, simp only [hp, rename_X, constant_coeff_X, ring_hom.map_mul, alg_hom.map_mul] }
end

end coeff

section support

lemma support_rename_of_injective {p : mv_polynomial σ R} {f : σ → τ} [decidable_eq τ]
 (h : function.injective f) :
 (rename f p).support = finset.image (map_domain f) p.support :=
begin
 rw rename_eq,
 exact finsupp.map_domain_support_of_injective (map_domain_injective h) _,
end

end support

end mv_polynomial

