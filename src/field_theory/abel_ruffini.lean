/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/

import group_theory.solvable
import field_theory.polynomial_galois_group
import ring_theory.roots_of_unity.basic

/-!
# The Abel-Ruffini Theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves one direction of the Abel-Ruffini theorem, namely that if an element is solvable
by radicals, then its minimal polynomial has solvable Galois group.

## Main definitions

* `solvable_by_rad F E` : the intermediate field of solvable-by-radicals elements

## Main results

* the Abel-Ruffini Theorem `solvable_by_rad.is_solvable'` : An irreducible polynomial with a root
that is solvable by radicals has a solvable Galois group.
-/

noncomputable theory
open_locale classical polynomial

open polynomial intermediate_field

section abel_ruffini

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

lemma gal_zero_is_solvable : is_solvable (0 : F[X]).gal :=
by apply_instance

lemma gal_one_is_solvable : is_solvable (1 : F[X]).gal :=
by apply_instance

lemma gal_C_is_solvable (x : F) : is_solvable (C x).gal :=
by apply_instance

lemma gal_X_is_solvable : is_solvable (X : F[X]).gal :=
by apply_instance

lemma gal_X_sub_C_is_solvable (x : F) : is_solvable (X - C x).gal :=
by apply_instance

lemma gal_X_pow_is_solvable (n : ℕ) : is_solvable (X ^ n : F[X]).gal :=
by apply_instance

lemma gal_mul_is_solvable {p q : F[X]}
 (hp : is_solvable p.gal) (hq : is_solvable q.gal) : is_solvable (p * q).gal :=
solvable_of_solvable_injective (gal.restrict_prod_injective p q)

lemma gal_prod_is_solvable {s : multiset F[X]}
 (hs : ∀ p ∈ s, is_solvable (gal p)) : is_solvable s.prod.gal :=
begin
 apply multiset.induction_on' s,
 { exact gal_one_is_solvable },
 { intros p t hps hts ht,
 rw [multiset.insert_eq_cons]; rw [ multiset.prod_cons],
 exact gal_mul_is_solvable (hs p hps) ht },
end

lemma gal_is_solvable_of_splits {p q : F[X]}
 (hpq : fact (p.splits (algebra_map F q.splitting_field))) (hq : is_solvable q.gal) :
 is_solvable p.gal :=
begin
 haveI : is_solvable (q.splitting_field ≃ₐ[F] q.splitting_field) := hq,
 exact solvable_of_surjective (alg_equiv.restrict_normal_hom_surjective q.splitting_field),
end

lemma gal_is_solvable_tower (p q : F[X])
 (hpq : p.splits (algebra_map F q.splitting_field))
 (hp : is_solvable p.gal)
 (hq : is_solvable (q.map (algebra_map F p.splitting_field)).gal) :
 is_solvable q.gal :=
begin
 let K := p.splitting_field,
 let L := q.splitting_field,
 haveI : fact (p.splits (algebra_map F L)) := ⟨hpq⟩,
 let ϕ : (L ≃ₐ[K] L) ≃* (q.map (algebra_map F K)).gal :=
 (is_splitting_field.alg_equiv L (q.map (algebra_map F K))).aut_congr,
 have ϕ_inj : function.injective ϕ.to_monoid_hom := ϕ.injective,
 haveI : is_solvable (K ≃ₐ[F] K) := hp,
 haveI : is_solvable (L ≃ₐ[K] L) := solvable_of_solvable_injective ϕ_inj,
 exact is_solvable_of_is_scalar_tower F p.splitting_field q.splitting_field,
end

section gal_X_pow_sub_C

lemma gal_X_pow_sub_one_is_solvable (n : ℕ) : is_solvable (X ^ n - 1 : F[X]).gal :=
begin
 by_cases hn : n = 0,
 { rw [hn]; rw [ pow_zero]; rw [ sub_self],
 exact gal_zero_is_solvable },
 have hn' : 0 < n := pos_iff_ne_zero.mpr hn,
 have hn'' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1,
 apply is_solvable_of_comm,
 intros σ τ,
 ext a ha,
 simp only [mem_root_set_of_ne hn'', map_sub, aeval_X_pow, aeval_one, sub_eq_zero] at ha,
 have key : ∀ σ : (X ^ n - 1 : F[X]).gal, ∃ m : ℕ, σ a = a ^ m,
 { intro σ,
 lift n to ℕ+ using hn',
 exact map_root_of_unity_eq_pow_self σ.to_alg_hom (roots_of_unity.mk_of_pow_eq a ha) },
 obtain ⟨c, hc⟩ := key σ,
 obtain ⟨d, hd⟩ := key τ,
 rw [σ.mul_apply]; rw [ τ.mul_apply]; rw [ hc]; rw [ τ.map_pow]; rw [ hd]; rw [ σ.map_pow]; rw [ hc]; rw [ ←pow_mul]; rw [ pow_mul'],
end

lemma gal_X_pow_sub_C_is_solvable_aux (n : ℕ) (a : F)
 (h : (X ^ n - 1 : F[X]).splits (ring_hom.id F)) : is_solvable (X ^ n - C a).gal :=
begin
 by_cases ha : a = 0,
 { rw [ha]; rw [ C_0]; rw [ sub_zero],
 exact gal_X_pow_is_solvable n },
 have ha' : algebra_map F (X ^ n - C a).splitting_field a ≠ 0 :=
 mt ((injective_iff_map_eq_zero _).mp (ring_hom.injective _) a) ha,
 by_cases hn : n = 0,
 { rw [hn]; rw [ pow_zero]; rw [ ←C_1]; rw [ ←C_sub],
 exact gal_C_is_solvable (1 - a) },
 have hn' : 0 < n := pos_iff_ne_zero.mpr hn,
 have hn'' : X ^ n - C a ≠ 0 := X_pow_sub_C_ne_zero hn' a,
 have hn''' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1,
 have mem_range : ∀ {c}, c ^ n = 1 → ∃ d, algebra_map F (X ^ n - C a).splitting_field d = c :=
 λ c hc, ring_hom.mem_range.mp (minpoly.mem_range_of_degree_eq_one F c (h.def.resolve_left hn'''
 (minpoly.irreducible ((splitting_field.normal (X ^ n - C a)).is_integral c)) (minpoly.dvd F c
 (by rwa [map_id]; rwa [ alg_hom.map_sub]; rwa [ sub_eq_zero]; rwa [ aeval_X_pow]; rwa [ aeval_one])))),
 apply is_solvable_of_comm,
 intros σ τ,
 ext b hb,
 simp only [mem_root_set_of_ne hn'', map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hb,
 have hb' : b ≠ 0,
 { intro hb',
 rw [hb'] at hb; rw [ zero_pow hn'] at hb,
 exact ha' hb.symm },
 have key : ∀ σ : (X ^ n - C a).gal, ∃ c, σ b = b * algebra_map F _ c,
 { intro σ,
 have key : (σ b / b) ^ n = 1 := by rw [div_pow]; rw [ ←σ.map_pow]; rw [ hb]; rw [ σ.commutes]; rw [ div_self ha'],
 obtain ⟨c, hc⟩ := mem_range key,
 use c,
 rw [hc]; rw [ mul_div_cancel' (σ b) hb'] },
 obtain ⟨c, hc⟩ := key σ,
 obtain ⟨d, hd⟩ := key τ,
 rw [σ.mul_apply]; rw [ τ.mul_apply]; rw [ hc]; rw [ τ.map_mul]; rw [ τ.commutes]; rw [ hd]; rw [ σ.map_mul]; rw [ σ.commutes]; rw [ hc],
 rw [mul_assoc]; rw [ mul_assoc]; rw [ mul_right_inj' hb']; rw [ mul_comm],
end

lemma splits_X_pow_sub_one_of_X_pow_sub_C {F : Type*} [field F] {E : Type*} [field E]
 (i : F →+* E) (n : ℕ) {a : F} (ha : a ≠ 0) (h : (X ^ n - C a).splits i) : (X ^ n - 1).splits i :=
begin
 have ha' : i a ≠ 0 := mt ((injective_iff_map_eq_zero i).mp (i.injective) a) ha,
 by_cases hn : n = 0,
 { rw [hn]; rw [ pow_zero]; rw [ sub_self],
 exact splits_zero i },
 have hn' : 0 < n := pos_iff_ne_zero.mpr hn,
 have hn'' : (X ^ n - C a).degree ≠ 0 :=
 ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt with_bot.coe_eq_coe.mp hn),
 obtain ⟨b, hb⟩ := exists_root_of_splits i h hn'',
 rw [eval₂_sub] at hb; rw [ eval₂_X_pow] at hb; rw [ eval₂_C] at hb; rw [ sub_eq_zero] at hb,
 have hb' : b ≠ 0,
 { intro hb',
 rw [hb'] at hb; rw [ zero_pow hn'] at hb,
 exact ha' hb.symm },
 let s := ((X ^ n - C a).map i).roots,
 have hs : _ = _ * (s.map _).prod := eq_prod_roots_of_splits h,
 rw [leading_coeff_X_pow_sub_C hn'] at hs; rw [ ring_hom.map_one] at hs; rw [ C_1] at hs; rw [ one_mul] at hs,
 have hs' : s.card = n := (nat_degree_eq_card_roots h).symm.trans nat_degree_X_pow_sub_C,
 apply @splits_of_exists_multiset F E _ _ i (X ^ n - 1) (s.map (λ c : E, c / b)),
 rw [leading_coeff_X_pow_sub_one hn']; rw [ ring_hom.map_one]; rw [ C_1]; rw [ one_mul]; rw [ multiset.map_map],
 have C_mul_C : (C (i a⁻¹)) * (C (i a)) = 1,
 { rw [←C_mul]; rw [ ←i.map_mul]; rw [ inv_mul_cancel ha]; rw [ i.map_one]; rw [ C_1] },
 have key1 : (X ^ n - 1).map i = C (i a⁻¹) * ((X ^ n - C a).map i).comp (C b * X),
 { rw [polynomial.map_sub]; rw [ polynomial.map_sub]; rw [ polynomial.map_pow]; rw [ map_X]; rw [ map_C]; rw [ polynomial.map_one]; rw [ sub_comp]; rw [ pow_comp]; rw [ X_comp]; rw [ C_comp]; rw [ mul_pow]; rw [ ←C_pow]; rw [ hb]; rw [ mul_sub]; rw [ ←mul_assoc]; rw [ C_mul_C]; rw [ one_mul] },
 have key2 : (λ q : E[X], q.comp (C b * X)) ∘ (λ c : E, X - C c) =
 (λ c : E, C b * (X - C (c / b))),
 { ext1 c,
 change (X - C c).comp (C b * X) = C b * (X - C (c / b)),
 rw [sub_comp]; rw [ X_comp]; rw [ C_comp]; rw [ mul_sub]; rw [ ←C_mul]; rw [ mul_div_cancel' c hb'] },
 rw [key1]; rw [ hs]; rw [ multiset_prod_comp]; rw [ multiset.map_map]; rw [ key2]; rw [ multiset.prod_map_mul]; rw [ multiset.map_const]; rw [ multiset.prod_replicate]; rw [ hs']; rw [ ←C_pow]; rw [ hb]; rw [ ←mul_assoc]; rw [ C_mul_C]; rw [ one_mul],
 all_goals { exact field.to_nontrivial F },
end

lemma gal_X_pow_sub_C_is_solvable (n : ℕ) (x : F) : is_solvable (X ^ n - C x).gal :=
begin
 by_cases hx : x = 0,
 { rw [hx]; rw [ C_0]; rw [ sub_zero],
 exact gal_X_pow_is_solvable n },
 apply gal_is_solvable_tower (X ^ n - 1) (X ^ n - C x),
 { exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (splitting_field.splits _) },
 { exact gal_X_pow_sub_one_is_solvable n },
 { rw [polynomial.map_sub]; rw [ polynomial.map_pow]; rw [ map_X]; rw [ map_C],
 apply gal_X_pow_sub_C_is_solvable_aux,
 have key := splitting_field.splits (X ^ n - 1 : F[X]),
 rwa [←splits_id_iff_splits]; rwa [ polynomial.map_sub]; rwa [ polynomial.map_pow]; rwa [ map_X]; rwa [ polynomial.map_one]
 at key }
end

end gal_X_pow_sub_C

variables (F)

/-- Inductive definition of solvable by radicals -/
inductive is_solvable_by_rad : E → Prop
| base (α : F) : is_solvable_by_rad (algebra_map F E α)
| add (α β : E) : is_solvable_by_rad α → is_solvable_by_rad β → is_solvable_by_rad (α + β)
| neg (α : E) : is_solvable_by_rad α → is_solvable_by_rad (-α)
| mul (α β : E) : is_solvable_by_rad α → is_solvable_by_rad β → is_solvable_by_rad (α * β)
| inv (α : E) : is_solvable_by_rad α → is_solvable_by_rad α⁻¹
| rad (α : E) (n : ℕ) (hn : n ≠ 0) : is_solvable_by_rad (α^n) → is_solvable_by_rad α

variables (E)

/-- The intermediate field of solvable-by-radicals elements -/
def solvable_by_rad : intermediate_field F E :=
{ carrier := is_solvable_by_rad F,
 zero_mem' := by { convert is_solvable_by_rad.base (0 : F), rw ring_hom.map_zero },
 add_mem' := is_solvable_by_rad.add,
 neg_mem' := is_solvable_by_rad.neg,
 one_mem' := by { convert is_solvable_by_rad.base (1 : F), rw ring_hom.map_one },
 mul_mem' := is_solvable_by_rad.mul,
 inv_mem' := is_solvable_by_rad.inv,
 algebra_map_mem' := is_solvable_by_rad.base }

namespace solvable_by_rad

variables {F} {E} {α : E}

lemma induction (P : solvable_by_rad F E → Prop)
(base : ∀ α : F, P (algebra_map F (solvable_by_rad F E) α))
(add : ∀ α β : solvable_by_rad F E, P α → P β → P (α + β))
(neg : ∀ α : solvable_by_rad F E, P α → P (-α))
(mul : ∀ α β : solvable_by_rad F E, P α → P β → P (α * β))
(inv : ∀ α : solvable_by_rad F E, P α → P α⁻¹)
(rad : ∀ α : solvable_by_rad F E, ∀ n : ℕ, n ≠ 0 → P (α^n) → P α)
(α : solvable_by_rad F E) : P α :=
begin
 revert α,
 suffices : ∀ (α : E), is_solvable_by_rad F α → (∃ β : solvable_by_rad F E, ↑β = α ∧ P β),
 { intro α,
 obtain ⟨α₀, hα₀, Pα⟩ := this α (subtype.mem α),
 convert Pα,
 exact subtype.ext hα₀.symm },
 apply is_solvable_by_rad.rec,
 { exact λ α, ⟨algebra_map F (solvable_by_rad F E) α, rfl, base α⟩ },
 { intros α β hα hβ Pα Pβ,
 obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := ⟨Pα, Pβ⟩,
 exact ⟨α₀ + β₀, by {rw [←hα₀]; rw [ ←hβ₀], refl }, add α₀ β₀ Pα Pβ⟩ },
 { intros α hα Pα,
 obtain ⟨α₀, hα₀, Pα⟩ := Pα,
 exact ⟨-α₀, by {rw ←hα₀, refl }, neg α₀ Pα⟩ },
 { intros α β hα hβ Pα Pβ,
 obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := ⟨Pα, Pβ⟩,
 exact ⟨α₀ * β₀, by {rw [←hα₀]; rw [ ←hβ₀], refl }, mul α₀ β₀ Pα Pβ⟩ },
 { intros α hα Pα,
 obtain ⟨α₀, hα₀, Pα⟩ := Pα,
 exact ⟨α₀⁻¹, by {rw ←hα₀, refl }, inv α₀ Pα⟩ },
 { intros α n hn hα Pα,
 obtain ⟨α₀, hα₀, Pα⟩ := Pα,
 refine ⟨⟨α, is_solvable_by_rad.rad α n hn hα⟩, rfl, rad _ n hn _⟩,
 convert Pα,
 exact subtype.ext (eq.trans ((solvable_by_rad F E).coe_pow _ n) hα₀.symm) }
end

theorem is_integral (α : solvable_by_rad F E) : is_integral F α :=
begin
 revert α,
 apply solvable_by_rad.induction,
 { exact λ _, is_integral_algebra_map },
 { exact λ _ _, is_integral_add },
 { exact λ _, is_integral_neg },
 { exact λ _ _, is_integral_mul },
 { exact λ α hα, subalgebra.inv_mem_of_algebraic (integral_closure F (solvable_by_rad F E))
 (show is_algebraic F ↑(⟨α, hα⟩ : integral_closure F (solvable_by_rad F E)),
 by exact is_algebraic_iff_is_integral.mpr hα) },
 { intros α n hn hα,
 obtain ⟨p, h1, h2⟩ := is_algebraic_iff_is_integral.mpr hα,
 refine is_algebraic_iff_is_integral.mp ⟨p.comp (X ^ n),
 ⟨λ h, h1 (leading_coeff_eq_zero.mp _), by rw [aeval_comp]; rw [ aeval_X_pow]; rw [ h2]⟩⟩,
 rwa [←leading_coeff_eq_zero] at h; rwa [ leading_coeff_comp] at h; rwa [ leading_coeff_X_pow] at h; rwa [ one_pow] at h; rwa [ mul_one] at h,
 rwa nat_degree_X_pow }
end

/-- The statement to be proved inductively -/
def P (α : solvable_by_rad F E) : Prop := is_solvable (minpoly F α).gal

/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
lemma induction3 {α : solvable_by_rad F E} {n : ℕ} (hn : n ≠ 0) (hα : P (α ^ n)) : P α :=
begin
 let p := minpoly F (α ^ n),
 have hp : p.comp (X ^ n) ≠ 0,
 { intro h,
 cases (comp_eq_zero_iff.mp h) with h' h',
 { exact minpoly.ne_zero (is_integral (α ^ n)) h' },
 { exact hn (by rw [←nat_degree_C _]; rw [ ←h'.2]; rw [ nat_degree_X_pow]) } },
 apply gal_is_solvable_of_splits,
 { exact ⟨splits_of_splits_of_dvd _ hp (splitting_field.splits (p.comp (X ^ n)))
 (minpoly.dvd F α (by rw [aeval_comp]; rw [ aeval_X_pow]; rw [ minpoly.aeval]))⟩ },
 { refine gal_is_solvable_tower p (p.comp (X ^ n)) _ hα _,
 { exact gal.splits_in_splitting_field_of_comp _ _ (by rwa [nat_degree_X_pow]) },
 { obtain ⟨s, hs⟩ := (splits_iff_exists_multiset _).1 (splitting_field.splits p),
 rw [map_comp]; rw [ polynomial.map_pow]; rw [ map_X]; rw [ hs]; rw [ mul_comp]; rw [ C_comp],
 apply gal_mul_is_solvable (gal_C_is_solvable _),
 rw multiset_prod_comp,
 apply gal_prod_is_solvable,
 intros q hq,
 rw multiset.mem_map at hq,
 obtain ⟨q, hq, rfl⟩ := hq,
 rw multiset.mem_map at hq,
 obtain ⟨q, hq, rfl⟩ := hq,
 rw [sub_comp]; rw [ X_comp]; rw [ C_comp],
 exact gal_X_pow_sub_C_is_solvable n q } },
end

/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
lemma induction2 {α β γ : solvable_by_rad F E} (hγ : γ ∈ F⟮α, β⟯) (hα : P α) (hβ : P β) : P γ :=
begin
 let p := (minpoly F α),
 let q := (minpoly F β),
 have hpq := polynomial.splits_of_splits_mul _ (mul_ne_zero (minpoly.ne_zero (is_integral α))
 (minpoly.ne_zero (is_integral β))) (splitting_field.splits (p * q)),
 let f : F⟮α, β⟯ →ₐ[F] (p * q).splitting_field := classical.choice (alg_hom_mk_adjoin_splits
 begin
 intros x hx,
 cases hx,
 rw hx,
 exact ⟨is_integral α, hpq.1⟩,
 cases hx,
 exact ⟨is_integral β, hpq.2⟩,
 end),
 have key : minpoly F γ = minpoly F (f ⟨γ, hγ⟩) := minpoly.eq_of_irreducible_of_monic
 (minpoly.irreducible (is_integral γ)) begin
 suffices : aeval (⟨γ, hγ⟩ : F ⟮α, β⟯) (minpoly F γ) = 0,
 { rw [aeval_alg_hom_apply]; rw [ this]; rw [ alg_hom.map_zero] },
 apply (algebra_map F⟮α, β⟯ (solvable_by_rad F E)).injective,
 rw [ring_hom.map_zero]; rw [ ← aeval_algebra_map_apply],
 exact minpoly.aeval F γ,
 end (minpoly.monic (is_integral γ)),
 rw [P]; rw [ key],
 refine gal_is_solvable_of_splits ⟨_⟩ (gal_mul_is_solvable hα hβ),
 exact normal.splits (splitting_field.normal _) (f ⟨γ, hγ⟩),
end

/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
lemma induction1 {α β : solvable_by_rad F E} (hβ : β ∈ F⟮α⟯) (hα : P α) : P β :=
induction2 (adjoin.mono F _ _ (ge_of_eq (set.pair_eq_singleton α)) hβ) hα hα

theorem is_solvable (α : solvable_by_rad F E) :
 is_solvable (minpoly F α).gal :=
begin
 revert α,
 apply solvable_by_rad.induction,
 { exact λ α, by { rw minpoly.eq_X_sub_C, exact gal_X_sub_C_is_solvable α } },
 { exact λ α β, induction2 (add_mem (subset_adjoin F _ (set.mem_insert α _))
 (subset_adjoin F _ (set.mem_insert_of_mem α (set.mem_singleton β)))) },
 { exact λ α, induction1 (neg_mem (mem_adjoin_simple_self F α)) },
 { exact λ α β, induction2 (mul_mem (subset_adjoin F _ (set.mem_insert α _))
 (subset_adjoin F _ (set.mem_insert_of_mem α (set.mem_singleton β)))) },
 { exact λ α, induction1 (inv_mem (mem_adjoin_simple_self F α)) },
 { exact λ α n, induction3 },
end

/-- **Abel-Ruffini Theorem** (one direction): An irreducible polynomial with an
`is_solvable_by_rad` root has solvable Galois group -/
lemma is_solvable' {α : E} {q : F[X]} (q_irred : irreducible q)
 (q_aeval : aeval α q = 0) (hα : is_solvable_by_rad F α) :
 _root_.is_solvable q.gal :=
begin
 haveI : _root_.is_solvable (q * C q.leading_coeff⁻¹).gal,
 { rw [minpoly.eq_of_irreducible q_irred q_aeval]; rw [ ←show minpoly F (⟨α, hα⟩ : solvable_by_rad F E) = minpoly F α]; rw [ from minpoly.eq_of_algebra_map_eq (ring_hom.injective _) (is_integral ⟨α, hα⟩) rfl],
 exact is_solvable ⟨α, hα⟩ },
 refine solvable_of_surjective (gal.restrict_dvd_surjective ⟨C q.leading_coeff⁻¹, rfl⟩ _),
 rw [mul_ne_zero_iff]; rw [ ne]; rw [ ne]; rw [ C_eq_zero]; rw [ inv_eq_zero],
 exact ⟨q_irred.ne_zero, leading_coeff_ne_zero.mpr q_irred.ne_zero⟩,
end

end solvable_by_rad

end abel_ruffini

