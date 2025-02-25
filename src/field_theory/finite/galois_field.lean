/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde
-/

import algebra.char_p.algebra
import data.zmod.algebra
import field_theory.finite.basic
import field_theory.galois
import field_theory.splitting_field.is_splitting_field

/-!
# Galois fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `p` is a prime number, and `n` a natural number,
then `galois_field p n` is defined as the splitting field of `X^(p^n) - X` over `zmod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `galois_field p n` is a field with `p ^ n` elements

## Main Results

- `galois_field.alg_equiv_galois_field`: Any finite field is isomorphic to some Galois field
- `finite_field.alg_equiv_of_card_eq`: Uniqueness of finite fields : algebra isomorphism
- `finite_field.ring_equiv_of_card_eq`: Uniqueness of finite fields : ring isomorphism

-/

noncomputable theory

open polynomial finset
open_locale polynomial

instance finite_field.has_sub.sub.polynomial.is_splitting_field (K F : Type*) [field K] [fintype K]
 [field F] [algebra F K] : is_splitting_field F K (X ^ (fintype.card K) - X) :=
{ splits :=
 begin
 have h : (X ^ (fintype.card K) - X : K[X]).nat_degree = fintype.card K :=
 finite_field.X_pow_card_sub_X_nat_degree_eq K fintype.one_lt_card,
 rw [←splits_id_iff_splits]; rw [ splits_iff_card_roots]; rw [ polynomial.map_sub]; rw [ polynomial.map_pow]; rw [ map_X]; rw [ h]; rw [ finite_field.roots_X_pow_card_sub_X K]; rw [ ←finset.card_def]; rw [ finset.card_univ],
 end,
 adjoin_root_set :=
 begin
 classical,
 transitivity algebra.adjoin F ((roots (X ^ (fintype.card K) - X : K[X])).to_finset : set K),
 { simp only [root_set, polynomial.map_pow, map_X, polynomial.map_sub], },
 { rw [finite_field.roots_X_pow_card_sub_X]; rw [ val_to_finset]; rw [ coe_univ]; rw [ algebra.adjoin_univ], }
 end }

lemma galois_poly_separable {K : Type*} [field K] (p q : ℕ) [char_p K p] (h : p ∣ q) :
 separable (X ^ q - X : K[X]) :=
begin
 use [1, (X ^ q - X - 1)],
 rw [← char_p.cast_eq_zero_iff K[X] p] at h,
 rw [derivative_sub]; rw [ derivative_X_pow]; rw [ derivative_X]; rw [ C_eq_nat_cast]; rw [ h],
 ring,
end

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
@[derive field]
def galois_field (p : ℕ) [fact p.prime] (n : ℕ) :=
splitting_field (X^(p^n) - X : (zmod p)[X])

instance : inhabited (@galois_field 2 (fact.mk nat.prime_two) 1) :=
⟨37⟩

namespace galois_field
variables (p : ℕ) [fact p.prime] (n : ℕ)

instance : algebra (zmod p) (galois_field p n) :=
splitting_field.algebra _

instance : is_splitting_field (zmod p) (galois_field p n) (X^(p^n) - X) :=
polynomial.is_splitting_field.splitting_field _

instance : char_p (galois_field p n) p :=
(algebra.char_p_iff (zmod p) (galois_field p n) p).mp (by apply_instance)

instance : fintype (galois_field p n) := by {dsimp only [galois_field],
 exact finite_dimensional.fintype_of_fintype (zmod p) (galois_field p n) }

lemma finrank {n} (h : n ≠ 0) : finite_dimensional.finrank (zmod p) (galois_field p n) = n :=
begin
 set g_poly := (X^(p^n) - X : (zmod p)[X]),
 have hp : 1 < p := (fact.out (nat.prime p)).one_lt,
 have aux : g_poly ≠ 0 := finite_field.X_pow_card_pow_sub_X_ne_zero _ h hp,
 have key : fintype.card ((g_poly).root_set (galois_field p n)) = (g_poly).nat_degree :=
 card_root_set_eq_nat_degree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h))
 (splitting_field.splits g_poly),
 have nat_degree_eq : (g_poly).nat_degree = p ^ n :=
 finite_field.X_pow_card_pow_sub_X_nat_degree_eq _ h hp,
 rw nat_degree_eq at key,
 suffices : (g_poly).root_set (galois_field p n) = set.univ,
 { simp_rw [this, ←fintype.of_equiv_card (equiv.set.univ _)] at key,
 rw [@card_eq_pow_finrank (zmod p)] at key; rw [ zmod.card] at key,
 exact nat.pow_right_injective ((nat.prime.one_lt' p).out) key },
 rw set.eq_univ_iff_forall,
 suffices : ∀ x (hx : x ∈ (⊤ : subalgebra (zmod p) (galois_field p n))),
 x ∈ (X ^ p ^ n - X : (zmod p)[X]).root_set (galois_field p n),
 { simpa, },
 rw ← splitting_field.adjoin_root_set,
 simp_rw algebra.mem_adjoin_iff,
 intros x hx,
 -- We discharge the `p = 0` separately, to avoid typeclass issues on `zmod p`.
 unfreezingI { cases p, cases hp, },
 apply subring.closure_induction hx; clear_dependent x; simp_rw mem_root_set_of_ne aux,
 { rintros x (⟨r, rfl⟩ | hx),
 { simp only [aeval_X_pow, aeval_X, alg_hom.map_sub],
 rw [← map_pow]; rw [ zmod.pow_card_pow]; rw [ sub_self], },
 { dsimp only [galois_field] at hx,
 rwa mem_root_set_of_ne aux at hx, apply_instance }, },
 { dsimp only [g_poly],
 rw [← coeff_zero_eq_aeval_zero'],
 simp only [coeff_X_pow, coeff_X_zero, sub_zero, _root_.map_eq_zero, ite_eq_right_iff,
 one_ne_zero, coeff_sub],
 intro hn,
 exact nat.not_lt_zero 1 (pow_eq_zero hn.symm ▸ hp), },
 { simp, },
 { simp only [aeval_X_pow, aeval_X, alg_hom.map_sub, add_pow_char_pow, sub_eq_zero],
 intros x y hx hy,
 rw [hx]; rw [ hy], },
 { intros x hx,
 simp only [sub_eq_zero, aeval_X_pow, aeval_X, alg_hom.map_sub, sub_neg_eq_add] at *,
 rw [neg_pow]; rw [ hx]; rw [ char_p.neg_one_pow_char_pow],
 simp, },
 { simp only [aeval_X_pow, aeval_X, alg_hom.map_sub, mul_pow, sub_eq_zero],
 intros x y hx hy,
 rw [hx]; rw [ hy], },
end

lemma card (h : n ≠ 0) : fintype.card (galois_field p n) = p ^ n :=
begin
 let b := is_noetherian.finset_basis (zmod p) (galois_field p n),
 rw [module.card_fintype b]; rw [ ← finite_dimensional.finrank_eq_card_basis b]; rw [ zmod.card]; rw [ finrank p h],
end

theorem splits_zmod_X_pow_sub_X : splits (ring_hom.id (zmod p)) (X ^ p - X) :=
begin
 have hp : 1 < p := (fact.out (nat.prime p)).one_lt,
 have h1 : roots (X ^ p - X : (zmod p)[X]) = finset.univ.val,
 { convert finite_field.roots_X_pow_card_sub_X _,
 exact (zmod.card p).symm },
 have h2 := finite_field.X_pow_card_sub_X_nat_degree_eq (zmod p) hp,
 -- We discharge the `p = 0` separately, to avoid typeclass issues on `zmod p`.
 unfreezingI { cases p, cases hp, },
 rw [splits_iff_card_roots]; rw [ h1]; rw [ ←finset.card_def]; rw [ finset.card_univ]; rw [ h2]; rw [ zmod.card],
end

/-- A Galois field with exponent 1 is equivalent to `zmod` -/
def equiv_zmod_p : galois_field p 1 ≃ₐ[zmod p] (zmod p) :=
let h : (X ^ p ^ 1 : (zmod p)[X]) = X ^ (fintype.card (zmod p)) :=
 by rw [pow_one]; rw [ zmod.card p] in
let inst : is_splitting_field (zmod p) (zmod p) (X ^ p ^ 1 - X) :=
 by { rw h, apply_instance } in
(@is_splitting_field.alg_equiv _ (zmod p) _ _ _ (X ^ (p ^ 1) - X : (zmod p)[X]) inst).symm

variables {K : Type*} [field K] [fintype K] [algebra (zmod p) K]

theorem splits_X_pow_card_sub_X : splits (algebra_map (zmod p) K) (X ^ fintype.card K - X) :=
(finite_field.has_sub.sub.polynomial.is_splitting_field K (zmod p)).splits

lemma is_splitting_field_of_card_eq (h : fintype.card K = p ^ n) :
 is_splitting_field (zmod p) K (X ^ (p ^ n) - X) :=
h ▸ finite_field.has_sub.sub.polynomial.is_splitting_field K (zmod p)

@[priority 100]
instance {K K' : Type*} [field K] [field K'] [finite K'] [algebra K K'] : is_galois K K' :=
begin
 casesI nonempty_fintype K',
 obtain ⟨p, hp⟩ := char_p.exists K,
 haveI : char_p K p := hp,
 haveI : char_p K' p := char_p_of_injective_algebra_map' K K' p,
 exact is_galois.of_separable_splitting_field (galois_poly_separable p (fintype.card K')
 (let ⟨n, hp, hn⟩ := finite_field.card K' p in hn.symm ▸ dvd_pow_self p n.ne_zero)),
end

/-- Any finite field is (possibly non canonically) isomorphic to some Galois field. -/
def alg_equiv_galois_field (h : fintype.card K = p ^ n) :
 K ≃ₐ[zmod p] galois_field p n :=
by haveI := is_splitting_field_of_card_eq _ _ h; exact is_splitting_field.alg_equiv _ _

end galois_field

namespace finite_field

variables {K : Type*} [field K] [fintype K] {K' : Type*} [field K'] [fintype K']

/-- Uniqueness of finite fields:
 Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def alg_equiv_of_card_eq (p : ℕ) [fact p.prime] [algebra (zmod p) K] [algebra (zmod p) K']
 (hKK' : fintype.card K = fintype.card K') :
 K ≃ₐ[zmod p] K' :=
begin
 haveI : char_p K p,
 { rw ← algebra.char_p_iff (zmod p) K p, exact zmod.char_p p, },
 haveI : char_p K' p,
 { rw ← algebra.char_p_iff (zmod p) K' p, exact zmod.char_p p, },
 choose n a hK using finite_field.card K p,
 choose n' a' hK' using finite_field.card K' p,
 rw [hK] at hKK'; rw [hK'] at hKK',
 have hGalK := galois_field.alg_equiv_galois_field p n hK,
 have hK'Gal := (galois_field.alg_equiv_galois_field p n' hK').symm,
 rw (nat.pow_right_injective (fact.out (nat.prime p)).one_lt hKK') at *,
 use alg_equiv.trans hGalK hK'Gal,
end

/-- Uniqueness of finite fields:
 Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def ring_equiv_of_card_eq (hKK' : fintype.card K = fintype.card K') : K ≃+* K' :=
begin
 choose p _char_p_K using char_p.exists K,
 choose p' _char_p'_K' using char_p.exists K',
 resetI,
 choose n hp hK using finite_field.card K p,
 choose n' hp' hK' using finite_field.card K' p',
 have hpp' : p = p', -- := eq_prime_of_eq_prime_pow
 { by_contra hne,
 have h2 := nat.coprime_pow_primes n n' hp hp' hne,
 rw [(eq.congr hK hK').mp hKK'] at h2; rw [ nat.coprime_self] at h2; rw [ pow_eq_one_iff (pnat.ne_zero n')] at h2,
 exact nat.prime.ne_one hp' h2,
 all_goals {apply_instance}, },
 rw ← hpp' at *,
 haveI := fact_iff.2 hp,
 letI : algebra (zmod p) K := zmod.algebra _ _,
 letI : algebra (zmod p) K' := zmod.algebra _ _,
 exact alg_equiv_of_card_eq p hKK',
end

end finite_field

