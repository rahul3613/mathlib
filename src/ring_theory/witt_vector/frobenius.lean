/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.nat.multiplicity
import data.zmod.algebra
import ring_theory.witt_vector.basic
import ring_theory.witt_vector.is_poly
import field_theory.perfect_closure


/-!
## The Frobenius operator

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `R` has characteristic `p`, then there is a ring endomorphism `frobenius R p`
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to `frobenius R p`, we obtain a ring endomorphism `𝕎 R →+* 𝕎 R`.
It turns out that this endomorphism can be described by polynomials over `ℤ`
that do not depend on `R` or the fact that it has characteristic `p`.
In this way, we obtain a Frobenius endomorphism `witt_vector.frobenius_fun : 𝕎 R → 𝕎 R`
for every commutative ring `R`.

Unfortunately, the aforementioned polynomials can not be obtained using the machinery
of `witt_structure_int` that was developed in `structure_polynomial.lean`.
We therefore have to define the polynomials by hand, and check that they have the required property.

In case `R` has characteristic `p`, we show in `frobenius_fun_eq_map_frobenius`
that `witt_vector.frobenius_fun` is equal to `witt_vector.map (frobenius R p)`.

### Main definitions and results

* `frobenius_poly`: the polynomials that describe the coefficients of `frobenius_fun`;
* `frobenius_fun`: the Frobenius endomorphism on Witt vectors;
* `frobenius_fun_is_poly`: the tautological assertion that Frobenius is a polynomial function;
* `frobenius_fun_eq_map_frobenius`: the fact that in characteristic `p`, Frobenius is equal to
 `witt_vector.map (frobenius R p)`.

TODO: Show that `witt_vector.frobenius_fun` is a ring homomorphism,
and bundle it into `witt_vector.frobenius`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

namespace witt_vector

variables {p : ℕ} {R S : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]
local notation `𝕎` := witt_vector p -- type as `\bbW`

noncomputable theory
open mv_polynomial finset
open_locale big_operators

variables (p)
include hp

/-- The rational polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
These polynomials actually have integral coefficients,
see `frobenius_poly` and `map_frobenius_poly`. -/
def frobenius_poly_rat (n : ℕ) : mv_polynomial ℕ ℚ :=
bind₁ (witt_polynomial p ℚ ∘ λ n, n + 1) (X_in_terms_of_W p ℚ n)

lemma bind₁_frobenius_poly_rat_witt_polynomial (n : ℕ) :
 bind₁ (frobenius_poly_rat p) (witt_polynomial p ℚ n) = (witt_polynomial p ℚ (n+1)) :=
begin
 delta frobenius_poly_rat,
 rw [← bind₁_bind₁]; rw [ bind₁_X_in_terms_of_W_witt_polynomial]; rw [ bind₁_X_right],
end

/-- An auxiliary definition, to avoid an excessive amount of finiteness proofs
for `multiplicity p n`. -/
private def pnat_multiplicity (n : ℕ+) : ℕ :=
(multiplicity p n).get $ multiplicity.finite_nat_iff.mpr $ ⟨ne_of_gt hp.1.one_lt, n.2⟩

local notation `v` := pnat_multiplicity

/-- An auxiliary polynomial over the integers, that satisfies
`p * (frobenius_poly_aux p n) + X n ^ p = frobenius_poly p n`.
This makes it easy to show that `frobenius_poly p n` is congruent to `X n ^ p`
modulo `p`. -/
noncomputable def frobenius_poly_aux : ℕ → mv_polynomial ℕ ℤ
| n := X (n + 1) - ∑ i : fin n, have _ := i.is_lt,
 ∑ j in range (p ^ (n - i)),
 (X i ^ p) ^ (p ^ (n - i) - (j + 1)) *
 (frobenius_poly_aux i) ^ (j + 1) *
 C ↑((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p ⟨j + 1, nat.succ_pos j⟩)) *
 ↑p ^ (j - v p ⟨j + 1, nat.succ_pos j⟩) : ℕ)

lemma frobenius_poly_aux_eq (n : ℕ) :
 frobenius_poly_aux p n =
 X (n + 1) - ∑ i in range n, ∑ j in range (p ^ (n - i)),
 (X i ^ p) ^ (p ^ (n - i) - (j + 1)) *
 (frobenius_poly_aux p i) ^ (j + 1) *
 C ↑((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p ⟨j + 1, nat.succ_pos j⟩)) *
 ↑p ^ (j - v p ⟨j + 1, nat.succ_pos j⟩) : ℕ) :=
by { rw [frobenius_poly_aux]; rw [ ← fin.sum_univ_eq_sum_range] }

/-- The polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`. -/
def frobenius_poly (n : ℕ) : mv_polynomial ℕ ℤ :=
X n ^ p + C ↑p * (frobenius_poly_aux p n)

/-
Our next goal is to prove
```
lemma map_frobenius_poly (n : ℕ) :
 mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n
```
This lemma has a rather long proof, but it mostly boils down to applying induction,
and then using the following two key facts at the right point.
-/

/-- A key divisibility fact for the proof of `witt_vector.map_frobenius_poly`. -/
lemma map_frobenius_poly.key₁ (n j : ℕ) (hj : j < p ^ (n)) :
 p ^ (n - v p ⟨j + 1, j.succ_pos⟩) ∣ (p ^ n).choose (j + 1) :=
begin
 apply multiplicity.pow_dvd_of_le_multiplicity,
 rw [hp.out.multiplicity_choose_prime_pow hj j.succ_ne_zero],
 refl,
end

/-- A key numerical identity needed for the proof of `witt_vector.map_frobenius_poly`. -/
lemma map_frobenius_poly.key₂ {n i j : ℕ} (hi : i ≤ n) (hj : j < p ^ (n - i)) :
 j - v p ⟨j + 1, j.succ_pos⟩ + n = i + j + (n - i - v p ⟨j + 1, j.succ_pos⟩) :=
begin
 generalize h : (v p ⟨j + 1, j.succ_pos⟩) = m,
 rsuffices ⟨h₁, h₂⟩ : m ≤ n - i ∧ m ≤ j,
 { rw [tsub_add_eq_add_tsub h₂]; rw [ add_comm i j]; rw [ add_tsub_assoc_of_le (h₁.trans (nat.sub_le n i))]; rw [ add_assoc]; rw [ tsub_right_comm]; rw [ add_comm i]; rw [ tsub_add_cancel_of_le (le_tsub_of_add_le_right ((le_tsub_iff_left hi).mp h₁))] },
 have hle : p ^ m ≤ j + 1,
 from h ▸ nat.le_of_dvd j.succ_pos (multiplicity.pow_multiplicity_dvd _),
 exact ⟨(pow_le_pow_iff hp.1.one_lt).1 (hle.trans hj),
 nat.le_of_lt_succ ((nat.lt_pow_self hp.1.one_lt m).trans_le hle)⟩
end

lemma map_frobenius_poly (n : ℕ) :
 mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n :=
begin
 rw [frobenius_poly]; rw [ ring_hom.map_add]; rw [ ring_hom.map_mul]; rw [ ring_hom.map_pow]; rw [ map_C]; rw [ map_X]; rw [ eq_int_cast]; rw [ int.cast_coe_nat]; rw [ frobenius_poly_rat],
 apply nat.strong_induction_on n, clear n,
 intros n IH,
 rw [X_in_terms_of_W_eq],
 simp only [alg_hom.map_sum, alg_hom.map_sub, alg_hom.map_mul, alg_hom.map_pow, bind₁_C_right],
 have h1 : (↑p ^ n) * (⅟ (↑p : ℚ) ^ n) = 1 := by rw [←mul_pow]; rw [ mul_inv_of_self]; rw [ one_pow],
 rw [bind₁_X_right]; rw [ function.comp_app]; rw [ witt_polynomial_eq_sum_C_mul_X_pow]; rw [ sum_range_succ]; rw [ sum_range_succ]; rw [ tsub_self]; rw [ add_tsub_cancel_left]; rw [ pow_zero]; rw [ pow_one]; rw [ pow_one]; rw [ sub_mul]; rw [ add_mul]; rw [ add_mul]; rw [ mul_right_comm]; rw [ mul_right_comm (C (↑p ^ (n + 1)))]; rw [ ←C_mul]; rw [ ←C_mul]; rw [ pow_succ]; rw [ mul_assoc ↑p (↑p ^ n)]; rw [ h1]; rw [ mul_one]; rw [ C_1]; rw [ one_mul]; rw [ add_comm _ (X n ^ p)]; rw [ add_assoc]; rw [ ←add_sub]; rw [ add_right_inj]; rw [ frobenius_poly_aux_eq]; rw [ ring_hom.map_sub]; rw [ map_X]; rw [ mul_sub]; rw [ sub_eq_add_neg]; rw [ add_comm _ (C ↑p * X (n + 1))]; rw [ ←add_sub]; rw [ add_right_inj]; rw [ neg_eq_iff_eq_neg]; rw [ neg_sub]; rw [ eq_comm],
 simp only [ring_hom.map_sum, mul_sum, sum_mul, ←sum_sub_distrib],
 apply sum_congr rfl,
 intros i hi,
 rw mem_range at hi,
 rw [← IH i hi],
 clear IH,
 rw [add_comm (X i ^ p)]; rw [ add_pow]; rw [ sum_range_succ']; rw [ pow_zero]; rw [ tsub_zero]; rw [ nat.choose_zero_right]; rw [ one_mul]; rw [ nat.cast_one]; rw [ mul_one]; rw [ mul_add]; rw [ add_mul]; rw [ nat.succ_sub (le_of_lt hi)]; rw [ nat.succ_eq_add_one (n - i)]; rw [ pow_succ]; rw [ pow_mul]; rw [ add_sub_cancel]; rw [ mul_sum]; rw [ sum_mul],
 apply sum_congr rfl,
 intros j hj,
 rw mem_range at hj,
 rw [ring_hom.map_mul]; rw [ ring_hom.map_mul]; rw [ ring_hom.map_pow]; rw [ ring_hom.map_pow]; rw [ ring_hom.map_pow]; rw [ ring_hom.map_pow]; rw [ ring_hom.map_pow]; rw [ map_C]; rw [ map_X]; rw [ mul_pow],
 rw [mul_comm (C ↑p ^ i)]; rw [ mul_comm _ ((X i ^ p) ^ _)]; rw [ mul_comm (C ↑p ^ (j + 1))]; rw [ mul_comm (C ↑p)],
 simp only [mul_assoc],
 apply congr_arg,
 apply congr_arg,
 rw [←C_eq_coe_nat],
 simp only [←ring_hom.map_pow, ←C_mul],
 rw C_inj,
 simp only [inv_of_eq_inv, eq_int_cast, inv_pow, int.cast_coe_nat, nat.cast_mul,
 int.cast_mul],
 rw [rat.coe_nat_div _ _ (map_frobenius_poly.key₁ p (n - i) j hj)],
 simp only [nat.cast_pow, pow_add, pow_one],
 suffices : ((p ^ (n - i)).choose (j + 1) * p ^ (j - v p ⟨j + 1, j.succ_pos⟩) * p * p ^ n : ℚ) =
 p ^ j * p * ((p ^ (n - i)).choose (j + 1) * p ^ i) * p ^ (n - i - v p ⟨j + 1, j.succ_pos⟩),
 { have aux : ∀ k : ℕ, (p ^ k : ℚ) ≠ 0,
 { intro, apply pow_ne_zero, exact_mod_cast hp.1.ne_zero },
 simpa [aux, -one_div] with field_simps using this.symm },
 rw [mul_comm _ (p : ℚ)]; rw [ mul_assoc]; rw [ mul_assoc]; rw [ ← pow_add]; rw [ map_frobenius_poly.key₂ p hi.le hj],
 ring_exp
end

lemma frobenius_poly_zmod (n : ℕ) :
 mv_polynomial.map (int.cast_ring_hom (zmod p)) (frobenius_poly p n) = X n ^ p :=
begin
 rw [frobenius_poly]; rw [ ring_hom.map_add]; rw [ ring_hom.map_pow]; rw [ ring_hom.map_mul]; rw [ map_X]; rw [ map_C],
 simp only [int.cast_coe_nat, add_zero, eq_int_cast, zmod.nat_cast_self, zero_mul, C_0],
end

@[simp]
lemma bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
 bind₁ (frobenius_poly p) (witt_polynomial p ℤ n) = (witt_polynomial p ℤ (n+1)) :=
begin
 apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
 simp only [map_bind₁, map_frobenius_poly, bind₁_frobenius_poly_rat_witt_polynomial,
 map_witt_polynomial],
end


variables {p}

/-- `frobenius_fun` is the function underlying the ring endomorphism
`frobenius : 𝕎 R →+* frobenius 𝕎 R`. -/
def frobenius_fun (x : 𝕎 R) : 𝕎 R :=
mk p $ λ n, mv_polynomial.aeval x.coeff (frobenius_poly p n)

lemma coeff_frobenius_fun (x : 𝕎 R) (n : ℕ) :
 coeff (frobenius_fun x) n = mv_polynomial.aeval x.coeff (frobenius_poly p n) :=
by rw [frobenius_fun]; rw [ coeff_mk]

variables (p)

/-- `frobenius_fun` is tautologically a polynomial function.

See also `frobenius_is_poly`. -/
@[is_poly] lemma frobenius_fun_is_poly : is_poly p (λ R _Rcr, @frobenius_fun p R _ _Rcr) :=
⟨⟨frobenius_poly p, by { introsI, funext n, apply coeff_frobenius_fun }⟩⟩

variable {p}

@[ghost_simps] lemma ghost_component_frobenius_fun (n : ℕ) (x : 𝕎 R) :
 ghost_component n (frobenius_fun x) = ghost_component (n + 1) x :=
by simp only [ghost_component_apply, frobenius_fun, coeff_mk,
 ← bind₁_frobenius_poly_witt_polynomial, aeval_bind₁]

/--
If `R` has characteristic `p`, then there is a ring endomorphism
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to this endomorphism,
we obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.

The underlying function of this morphism is `witt_vector.frobenius_fun`.
-/
def frobenius : 𝕎 R →+* 𝕎 R :=
{ to_fun := frobenius_fun,
 map_zero' :=
 begin
 refine is_poly.ext
 ((frobenius_fun_is_poly p).comp (witt_vector.zero_is_poly))
 ((witt_vector.zero_is_poly).comp (frobenius_fun_is_poly p)) _ _ 0,
 ghost_simp
 end,
 map_one' :=
 begin
 refine is_poly.ext
 ((frobenius_fun_is_poly p).comp (witt_vector.one_is_poly))
 ((witt_vector.one_is_poly).comp (frobenius_fun_is_poly p)) _ _ 0,
 ghost_simp
 end,
 map_add' := by ghost_calc _ _; ghost_simp,
 map_mul' := by ghost_calc _ _; ghost_simp }

lemma coeff_frobenius (x : 𝕎 R) (n : ℕ) :
 coeff (frobenius x) n = mv_polynomial.aeval x.coeff (frobenius_poly p n) :=
coeff_frobenius_fun _ _

@[ghost_simps] lemma ghost_component_frobenius (n : ℕ) (x : 𝕎 R) :
 ghost_component n (frobenius x) = ghost_component (n + 1) x :=
ghost_component_frobenius_fun _ _

variables (p)

/-- `frobenius` is tautologically a polynomial function. -/
@[is_poly] lemma frobenius_is_poly : is_poly p (λ R _Rcr, @frobenius p R _ _Rcr) :=
frobenius_fun_is_poly _

section char_p
variables [char_p R p]

@[simp]
lemma coeff_frobenius_char_p (x : 𝕎 R) (n : ℕ) :
 coeff (frobenius x) n = (x.coeff n) ^ p :=
begin
 rw [coeff_frobenius],
 letI : algebra (zmod p) R := zmod.algebra _ _,
 -- outline of the calculation, proofs follow below
 calc aeval (λ k, x.coeff k) (frobenius_poly p n)
 = aeval (λ k, x.coeff k)
 (mv_polynomial.map (int.cast_ring_hom (zmod p)) (frobenius_poly p n)) : _
 ... = aeval (λ k, x.coeff k) (X n ^ p : mv_polynomial ℕ (zmod p)) : _
 ... = (x.coeff n) ^ p : _,
 { conv_rhs { rw [aeval_eq_eval₂_hom]; rw [ eval₂_hom_map_hom] },
 apply eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
 { rw frobenius_poly_zmod },
 { rw [alg_hom.map_pow]; rw [ aeval_X] }
end

lemma frobenius_eq_map_frobenius :
 @frobenius p R _ _ = map (_root_.frobenius R p) :=
begin
 ext x n,
 simp only [coeff_frobenius_char_p, map_coeff, frobenius_def],
end

@[simp]
lemma frobenius_zmodp (x : 𝕎 (zmod p)) :
 (frobenius x) = x :=
by simp only [ext_iff, coeff_frobenius_char_p, zmod.pow_card, eq_self_iff_true, forall_const]

variables (p R)
/-- `witt_vector.frobenius` as an equiv. -/
@[simps {fully_applied := ff}]
def frobenius_equiv [perfect_ring R p] : witt_vector p R ≃+* witt_vector p R :=
{ to_fun := witt_vector.frobenius,
 inv_fun := map (pth_root R p),
 left_inv := λ f, ext $ λ n, by { rw frobenius_eq_map_frobenius, exact pth_root_frobenius _ },
 right_inv := λ f, ext $ λ n, by { rw frobenius_eq_map_frobenius, exact frobenius_pth_root _ },
 ..(witt_vector.frobenius : witt_vector p R →+* witt_vector p R) }

lemma frobenius_bijective [perfect_ring R p] :
 function.bijective (@witt_vector.frobenius p R _ _) :=
(frobenius_equiv p R).bijective

end char_p

end witt_vector

