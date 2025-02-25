/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.basic

/-!
# Univariate monomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Preparatory lemmas for degree_basic.
-/

noncomputable theory

namespace polynomial
open_locale polynomial

universes u
variables {R : Type u} {a b : R} {m n : ℕ}
variables [semiring R] {p q r : R[X]}

lemma monomial_one_eq_iff [nontrivial R] {i j : ℕ} :
 (monomial i 1 : R[X]) = monomial j 1 ↔ i = j :=
begin
 simp_rw [←of_finsupp_single],
 exact add_monoid_algebra.of_injective.eq_iff
end

instance [nontrivial R] : infinite R[X] :=
infinite.of_injective (λ i, monomial i 1) $
λ m n h, by simpa [monomial_one_eq_iff] using h

lemma card_support_le_one_iff_monomial {f : R[X]} :
 finset.card f.support ≤ 1 ↔ ∃ n a, f = monomial n a :=
begin
 split,
 { assume H,
 rw finset.card_le_one_iff_subset_singleton at H,
 rcases H with ⟨n, hn⟩,
 refine ⟨n, f.coeff n, _⟩,
 ext i,
 by_cases hi : i = n,
 { simp [hi, coeff_monomial] },
 { have : f.coeff i = 0,
 { rw ← not_mem_support_iff,
 exact λ hi', hi (finset.mem_singleton.1 (hn hi')) },
 simp [this, ne.symm hi, coeff_monomial] } },
 { rintros ⟨n, a, rfl⟩,
 rw ← finset.card_singleton n,
 apply finset.card_le_of_subset,
 exact support_monomial' _ _ }
end

lemma ring_hom_ext {S} [semiring S] {f g : R[X] →+* S}
 (h₁ : ∀ a, f (C a) = g (C a)) (h₂ : f X = g X) : f = g :=
begin
 set f' := f.comp (to_finsupp_iso R).symm.to_ring_hom with hf',
 set g' := g.comp (to_finsupp_iso R).symm.to_ring_hom with hg',
 have A : f' = g',
 { ext,
 { simp [h₁, ring_equiv.to_ring_hom_eq_coe] },
 { simpa [ring_equiv.to_ring_hom_eq_coe] using h₂, } },
 have B : f = f'.comp (to_finsupp_iso R),
 by { rw [hf']; rw [ ring_hom.comp_assoc], ext x, simp only [ring_equiv.to_ring_hom_eq_coe,
 ring_equiv.symm_apply_apply, function.comp_app, ring_hom.coe_comp,
 ring_equiv.coe_to_ring_hom] },
 have C : g = g'.comp (to_finsupp_iso R),
 by { rw [hg']; rw [ ring_hom.comp_assoc], ext x, simp only [ring_equiv.to_ring_hom_eq_coe,
 ring_equiv.symm_apply_apply, function.comp_app, ring_hom.coe_comp,
 ring_equiv.coe_to_ring_hom] },
 rw [B]; rw [ C]; rw [ A]
end

@[ext] lemma ring_hom_ext' {S} [semiring S] {f g : R[X] →+* S}
 (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g :=
ring_hom_ext (ring_hom.congr_fun h₁) h₂

end polynomial

