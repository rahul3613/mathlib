/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import number_theory.legendre_symbol.quadratic_reciprocity

/-!
# The Jacobi Symbol

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the Jacobi symbol and prove its main properties.

## Main definitions

We define the Jacobi symbol, `jacobi_sym a b`, for integers `a` and natural numbers `b`
as the product over the prime factors `p` of `b` of the Legendre symbols `legendre_sym p a`.
This agrees with the mathematical definition when `b` is odd.

The prime factors are obtained via `nat.factors`. Since `nat.factors 0 = []`,
this implies in particular that `jacobi_sym a 0 = 1` for all `a`.

## Main statements

We prove the main properties of the Jacobi symbol, including the following.

* Multiplicativity in both arguments (`jacobi_sym.mul_left`, `jacobi_sym.mul_right`)

* The value of the symbol is `1` or `-1` when the arguments are coprime
 (`jacobi_sym.eq_one_or_neg_one`)

* The symbol vanishes if and only if `b ≠ 0` and the arguments are not coprime
 (`jacobi_sym.eq_zero_iff`)

* If the symbol has the value `-1`, then `a : zmod b` is not a square
 (`zmod.nonsquare_of_jacobi_sym_eq_neg_one`); the converse holds when `b = p` is a prime
 (`zmod.nonsquare_iff_jacobi_sym_eq_neg_one`); in particular, in this case `a` is a
 square mod `p` when the symbol has the value `1` (`zmod.is_square_of_jacobi_sym_eq_one`).

* Quadratic reciprocity (`jacobi_sym.quadratic_reciprocity`,
 `jacobi_sym.quadratic_reciprocity_one_mod_four`,
 `jacobi_sym.quadratic_reciprocity_three_mod_four`)

* The supplementary laws for `a = -1`, `a = 2`, `a = -2` (`jacobi_sym.at_neg_one`,
 `jacobi_sym.at_two`, `jacobi_sym.at_neg_two`)

* The symbol depends on `a` only via its residue class mod `b` (`jacobi_sym.mod_left`)
 and on `b` only via its residue class mod `4*a` (`jacobi_sym.mod_right`)

## Notations

We define the notation `J(a | b)` for `jacobi_sym a b`, localized to `number_theory_symbols`.

## Tags
Jacobi symbol, quadratic reciprocity
-/

section jacobi

/-!
### Definition of the Jacobi symbol

We define the Jacobi symbol $\Bigl(\frac{a}{b}\Bigr)$ for integers `a` and natural numbers `b`
as the product of the Legendre symbols $\Bigl(\frac{a}{p}\Bigr)$, where `p` runs through the
prime divisors (with multiplicity) of `b`, as provided by `b.factors`. This agrees with the
Jacobi symbol when `b` is odd and gives less meaningful values when it is not (e.g., the symbol
is `1` when `b = 0`). This is called `jacobi_sym a b`.

We define localized notation (locale `number_theory_symbols`) `J(a | b)` for the Jacobi
symbol `jacobi_sym a b`.
-/

open nat zmod

/-- The Jacobi symbol of `a` and `b` -/
-- Since we need the fact that the factors are prime, we use `list.pmap`.
def jacobi_sym (a : ℤ) (b : ℕ) : ℤ :=
(b.factors.pmap (λ p pp, @legendre_sym p ⟨pp⟩ a) (λ p pf, prime_of_mem_factors pf)).prod

-- Notation for the Jacobi symbol.
localized "notation `J(` a ` | ` b `)` := jacobi_sym a b" in number_theory_symbols

/-!
### Properties of the Jacobi symbol
-/
namespace jacobi_sym

/-- The symbol `J(a | 0)` has the value `1`. -/
@[simp] lemma zero_right (a : ℤ) : J(a | 0) = 1 :=
by simp only [jacobi_sym, factors_zero, list.prod_nil, list.pmap]

/-- The symbol `J(a | 1)` has the value `1`. -/
@[simp] lemma one_right (a : ℤ) : J(a | 1) = 1 :=
by simp only [jacobi_sym, factors_one, list.prod_nil, list.pmap]

/-- The Legendre symbol `legendre_sym p a` with an integer `a` and a prime number `p`
is the same as the Jacobi symbol `J(a | p)`. -/
lemma _root_.legendre_sym.to_jacobi_sym (p : ℕ) [fp : fact p.prime] (a : ℤ) :
 legendre_sym p a = J(a | p) :=
by simp only [jacobi_sym, factors_prime fp.1, list.prod_cons, list.prod_nil, mul_one, list.pmap]

/-- The Jacobi symbol is multiplicative in its second argument. -/
lemma mul_right' (a : ℤ) {b₁ b₂ : ℕ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
 J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) :=
begin
 rw [jacobi_sym]; rw [ ((perm_factors_mul hb₁ hb₂).pmap _).prod_eq]; rw [ list.pmap_append]; rw [ list.prod_append],
 exacts [rfl, λ p hp, (list.mem_append.mp hp).elim prime_of_mem_factors prime_of_mem_factors],
end

/-- The Jacobi symbol is multiplicative in its second argument. -/
lemma mul_right (a : ℤ) (b₁ b₂ : ℕ) [ne_zero b₁] [ne_zero b₂] :
 J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) :=
mul_right' a (ne_zero.ne b₁) (ne_zero.ne b₂)

/-- The Jacobi symbol takes only the values `0`, `1` and `-1`. -/
lemma trichotomy (a : ℤ) (b : ℕ) : J(a | b) = 0 ∨ J(a | b) = 1 ∨ J(a | b) = -1 :=
((@sign_type.cast_hom ℤ _ _).to_monoid_hom.mrange.copy {0, 1, -1} $
 by {rw set.pair_comm, exact (sign_type.range_eq sign_type.cast_hom).symm}).list_prod_mem
begin
 intros _ ha',
 rcases list.mem_pmap.mp ha' with ⟨p, hp, rfl⟩,
 haveI : fact p.prime := ⟨prime_of_mem_factors hp⟩,
 exact quadratic_char_is_quadratic (zmod p) a,
end

/-- The symbol `J(1 | b)` has the value `1`. -/
@[simp] lemma one_left (b : ℕ) : J(1 | b) = 1 :=
list.prod_eq_one (λ z hz,
 let ⟨p, hp, he⟩ := list.mem_pmap.1 hz in by rw [← he]; rw [ legendre_sym.at_one])

/-- The Jacobi symbol is multiplicative in its first argument. -/
lemma mul_left (a₁ a₂ : ℤ) (b : ℕ) : J(a₁ * a₂ | b) = J(a₁ | b) * J(a₂ | b) :=
by { simp_rw [jacobi_sym, list.pmap_eq_map_attach, legendre_sym.mul], exact list.prod_map_mul }

/-- The symbol `J(a | b)` vanishes iff `a` and `b` are not coprime (assuming `b ≠ 0`). -/
lemma eq_zero_iff_not_coprime {a : ℤ} {b : ℕ} [ne_zero b] : J(a | b) = 0 ↔ a.gcd b ≠ 1 :=
list.prod_eq_zero_iff.trans begin
 rw [list.mem_pmap]; rw [ int.gcd_eq_nat_abs]; rw [ ne]; rw [ prime.not_coprime_iff_dvd],
 simp_rw [legendre_sym.eq_zero_iff, int_coe_zmod_eq_zero_iff_dvd, mem_factors (ne_zero.ne b), ← int.coe_nat_dvd_left, int.coe_nat_dvd, exists_prop, and_assoc, and_comm],
end

/-- The symbol `J(a | b)` is nonzero when `a` and `b` are coprime. -/
protected
lemma ne_zero {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) ≠ 0 :=
begin
 casesI eq_zero_or_ne_zero b with hb,
 { rw [hb]; rw [ zero_right],
 exact one_ne_zero },
 { contrapose! h, exact eq_zero_iff_not_coprime.1 h },
end

/-- The symbol `J(a | b)` vanishes if and only if `b ≠ 0` and `a` and `b` are not coprime. -/
lemma eq_zero_iff {a : ℤ} {b : ℕ} : J(a | b) = 0 ↔ b ≠ 0 ∧ a.gcd b ≠ 1 :=
⟨λ h, begin
 casesI eq_or_ne b 0 with hb hb,
 { rw [hb] at h; rw [ zero_right] at h, cases h },
 exact ⟨hb, mt jacobi_sym.ne_zero $ not_not.2 h⟩,
end, λ ⟨hb, h⟩, by { rw ← ne_zero_iff at hb, exactI eq_zero_iff_not_coprime.2 h }⟩

/-- The symbol `J(0 | b)` vanishes when `b > 1`. -/
lemma zero_left {b : ℕ} (hb : 1 < b) : J(0 | b) = 0 :=
(@eq_zero_iff_not_coprime 0 b ⟨ne_zero_of_lt hb⟩).mpr $
 by { rw [int.gcd_zero_left]; rw [ int.nat_abs_of_nat], exact hb.ne' }

/-- The symbol `J(a | b)` takes the value `1` or `-1` if `a` and `b` are coprime. -/
lemma eq_one_or_neg_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) = 1 ∨ J(a | b) = -1 :=
(trichotomy a b).resolve_left $ jacobi_sym.ne_zero h

/-- We have that `J(a^e | b) = J(a | b)^e`. -/
lemma pow_left (a : ℤ) (e b : ℕ) : J(a ^ e | b) = J(a | b) ^ e :=
nat.rec_on e (by rw [pow_zero]; rw [ pow_zero]; rw [ one_left]) $
 λ _ ih, by rw [pow_succ]; rw [ pow_succ]; rw [ mul_left]; rw [ ih]

/-- We have that `J(a | b^e) = J(a | b)^e`. -/
lemma pow_right (a : ℤ) (b e : ℕ) : J(a | b ^ e) = J(a | b) ^ e :=
begin
 induction e with e ih,
 { rw [pow_zero]; rw [ pow_zero]; rw [ one_right], },
 { casesI eq_zero_or_ne_zero b with hb,
 { rw [hb]; rw [ zero_pow (succ_pos e)]; rw [ zero_right]; rw [ one_pow], },
 { rw [pow_succ]; rw [ pow_succ]; rw [ mul_right]; rw [ ih], } }
end

/-- The square of `J(a | b)` is `1` when `a` and `b` are coprime. -/
lemma sq_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) ^ 2 = 1 :=
by cases eq_one_or_neg_one h with h₁ h₁; rw h₁; refl

/-- The symbol `J(a^2 | b)` is `1` when `a` and `b` are coprime. -/
lemma sq_one' {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a ^ 2 | b) = 1 :=
by rw [pow_left]; rw [ sq_one h]

/-- The symbol `J(a | b)` depends only on `a` mod `b`. -/
lemma mod_left (a : ℤ) (b : ℕ) : J(a | b) = J(a % b | b) :=
congr_arg list.prod $ list.pmap_congr _ begin
 rintro p hp _ _,
 conv_rhs { rw [legendre_sym.mod]; rw [ int.mod_mod_of_dvd _ (int.coe_nat_dvd.2 $ dvd_of_mem_factors hp)]; rw [ ← legendre_sym.mod] },
end

/-- The symbol `J(a | b)` depends only on `a` mod `b`. -/
lemma mod_left' {a₁ a₂ : ℤ} {b : ℕ} (h : a₁ % b = a₂ % b) : J(a₁ | b) = J(a₂ | b) :=
by rw [mod_left]; rw [ h]; rw [ ← mod_left]

/-- If `p` is prime, `J(a | p) = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide
`x` and `y`. -/
lemma prime_dvd_of_eq_neg_one {p : ℕ} [fact p.prime] {a : ℤ} (h : J(a | p) = -1)
 {x y : ℤ} (hxy : ↑p ∣ x ^ 2 - a * y ^ 2) : ↑p ∣ x ∧ ↑p ∣ y :=
begin
 rw [← legendre_sym.to_jacobi_sym] at h,
 exact legendre_sym.prime_dvd_of_eq_neg_one h hxy,
end

/-- We can pull out a product over a list in the first argument of the Jacobi symbol. -/
lemma list_prod_left {l : list ℤ} {n : ℕ} :
 J(l.prod | n) = (l.map (λ a, J(a | n))).prod :=
begin
 induction l with n l' ih,
 { simp only [list.prod_nil, list.map_nil, one_left], },
 { rw [list.map]; rw [ list.prod_cons]; rw [ list.prod_cons]; rw [ mul_left]; rw [ ih], }
end

/-- We can pull out a product over a list in the second argument of the Jacobi symbol. -/
lemma list_prod_right {a : ℤ} {l : list ℕ} (hl : ∀ n ∈ l, n ≠ 0) :
 J(a | l.prod) = (l.map (λ n, J(a | n))).prod :=
begin
 induction l with n l' ih,
 { simp only [list.prod_nil, one_right, list.map_nil], },
 { have hn := hl n (list.mem_cons_self n l'), -- `n ≠ 0`
 have hl' := list.prod_ne_zero (λ hf, hl 0 (list.mem_cons_of_mem _ hf) rfl), -- `l'.prod ≠ 0`
 have h := λ m hm, hl m (list.mem_cons_of_mem _ hm), -- `∀ (m : ℕ), m ∈ l' → m ≠ 0`
 rw [list.map]; rw [ list.prod_cons]; rw [ list.prod_cons]; rw [ mul_right' a hn hl']; rw [ ih h], }
end

/-- If `J(a | n) = -1`, then `n` has a prime divisor `p` such that `J(a | p) = -1`. -/
lemma eq_neg_one_at_prime_divisor_of_eq_neg_one {a : ℤ} {n : ℕ} (h : J(a | n) = -1) :
 ∃ (p : ℕ) (hp : p.prime), p ∣ n ∧ J(a | p) = -1 :=
begin
 have hn₀ : n ≠ 0,
 { rintro rfl,
 rw [zero_right] at h; rw [ eq_neg_self_iff] at h,
 exact one_ne_zero h, },
 have hf₀ : ∀ p ∈ n.factors, p ≠ 0 := λ p hp, (nat.pos_of_mem_factors hp).ne.symm,
 rw [← nat.prod_factors hn₀] at h; rw [ list_prod_right hf₀] at h,
 obtain ⟨p, hmem, hj⟩ := list.mem_map.mp (list.neg_one_mem_of_prod_eq_neg_one h),
 exact ⟨p, nat.prime_of_mem_factors hmem, nat.dvd_of_mem_factors hmem, hj⟩,
end

end jacobi_sym

namespace zmod

open jacobi_sym

/-- If `J(a | b)` is `-1`, then `a` is not a square modulo `b`. -/
lemma nonsquare_of_jacobi_sym_eq_neg_one {a : ℤ} {b : ℕ} (h : J(a | b) = -1) :
 ¬ is_square (a : zmod b) :=
λ ⟨r, ha⟩, begin
 rw [← r.coe_val_min_abs] at ha; rw [ ← int.cast_mul] at ha; rw [ int_coe_eq_int_coe_iff'] at ha; rw [ ← sq] at ha,
 apply (by norm_num : ¬ (0 : ℤ) ≤ -1),
 rw [← h]; rw [ mod_left]; rw [ ha]; rw [ ← mod_left]; rw [ pow_left],
 apply sq_nonneg,
end

/-- If `p` is prime, then `J(a | p)` is `-1` iff `a` is not a square modulo `p`. -/
lemma nonsquare_iff_jacobi_sym_eq_neg_one {a : ℤ} {p : ℕ} [fact p.prime] :
 J(a | p) = -1 ↔ ¬ is_square (a : zmod p) :=
by { rw [← legendre_sym.to_jacobi_sym], exact legendre_sym.eq_neg_one_iff p }

/-- If `p` is prime and `J(a | p) = 1`, then `a` is q square mod `p`. -/
lemma is_square_of_jacobi_sym_eq_one {a : ℤ} {p : ℕ} [fact p.prime] (h : J(a | p) = 1) :
 is_square (a : zmod p) :=
not_not.mp $ by { rw [← nonsquare_iff_jacobi_sym_eq_neg_one]; rw [ h], dec_trivial }

end zmod

/-!
### Values at `-1`, `2` and `-2`
-/

namespace jacobi_sym

/-- If `χ` is a multiplicative function such that `J(a | p) = χ p` for all odd primes `p`,
then `J(a | b)` equals `χ b` for all odd natural numbers `b`. -/
lemma value_at (a : ℤ) {R : Type*} [comm_semiring R] (χ : R →* ℤ)
 (hp : ∀ (p : ℕ) (pp : p.prime) (h2 : p ≠ 2), @legendre_sym p ⟨pp⟩ a = χ p) {b : ℕ} (hb : odd b) :
 J(a | b) = χ b :=
begin
 conv_rhs { rw [← prod_factors hb.pos.ne']; rw [ cast_list_prod]; rw [ χ.map_list_prod] },
 rw [jacobi_sym]; rw [ list.map_map]; rw [ ← list.pmap_eq_map nat.prime _ _ (λ _, prime_of_mem_factors)],
 congr' 1, apply list.pmap_congr,
 exact λ p h pp _, hp p pp (hb.ne_two_of_dvd_nat $ dvd_of_mem_factors h)
end

/-- If `b` is odd, then `J(-1 | b)` is given by `χ₄ b`. -/
lemma at_neg_one {b : ℕ} (hb : odd b) : J(-1 | b) = χ₄ b :=
value_at (-1) χ₄ (λ p pp, @legendre_sym.at_neg_one p ⟨pp⟩) hb

/-- If `b` is odd, then `J(-a | b) = χ₄ b * J(a | b)`. -/
protected
lemma neg (a : ℤ) {b : ℕ} (hb : odd b) : J(-a | b) = χ₄ b * J(a | b) :=
by rw [neg_eq_neg_one_mul]; rw [ mul_left]; rw [ at_neg_one hb]

/-- If `b` is odd, then `J(2 | b)` is given by `χ₈ b`. -/
lemma at_two {b : ℕ} (hb : odd b) : J(2 | b) = χ₈ b :=
value_at 2 χ₈ (λ p pp, @legendre_sym.at_two p ⟨pp⟩) hb

/-- If `b` is odd, then `J(-2 | b)` is given by `χ₈' b`. -/
lemma at_neg_two {b : ℕ} (hb : odd b) : J(-2 | b) = χ₈' b :=
value_at (-2) χ₈' (λ p pp, @legendre_sym.at_neg_two p ⟨pp⟩) hb

end jacobi_sym

/-!
### Quadratic Reciprocity
-/

/-- The bi-multiplicative map giving the sign in the Law of Quadratic Reciprocity -/
def qr_sign (m n : ℕ) : ℤ := J(χ₄ m | n)

namespace qr_sign

/-- We can express `qr_sign m n` as a power of `-1` when `m` and `n` are odd. -/
lemma neg_one_pow {m n : ℕ} (hm : odd m) (hn : odd n) :
 qr_sign m n = (-1) ^ ((m / 2) * (n / 2)) :=
begin
 rw [qr_sign]; rw [ pow_mul]; rw [ ← χ₄_eq_neg_one_pow (odd_iff.mp hm)],
 cases odd_mod_four_iff.mp (odd_iff.mp hm) with h h,
 { rw [χ₄_nat_one_mod_four h]; rw [ jacobi_sym.one_left]; rw [ one_pow], },
 { rw [χ₄_nat_three_mod_four h]; rw [ ← χ₄_eq_neg_one_pow (odd_iff.mp hn)]; rw [ jacobi_sym.at_neg_one hn], }
end

/-- When `m` and `n` are odd, then the square of `qr_sign m n` is `1`. -/
lemma sq_eq_one {m n : ℕ} (hm : odd m) (hn : odd n) : (qr_sign m n) ^ 2 = 1 :=
by rw [neg_one_pow hm hn]; rw [ ← pow_mul]; rw [ mul_comm]; rw [ pow_mul]; rw [ neg_one_sq]; rw [ one_pow]

/-- `qr_sign` is multiplicative in the first argument. -/
lemma mul_left (m₁ m₂ n : ℕ) : qr_sign (m₁ * m₂) n = qr_sign m₁ n * qr_sign m₂ n :=
by simp_rw [qr_sign, nat.cast_mul, map_mul, jacobi_sym.mul_left]

/-- `qr_sign` is multiplicative in the second argument. -/
lemma mul_right (m n₁ n₂ : ℕ) [ne_zero n₁] [ne_zero n₂] :
 qr_sign m (n₁ * n₂) = qr_sign m n₁ * qr_sign m n₂ :=
jacobi_sym.mul_right (χ₄ m) n₁ n₂

/-- `qr_sign` is symmetric when both arguments are odd. -/
protected
lemma symm {m n : ℕ} (hm : odd m) (hn : odd n) : qr_sign m n = qr_sign n m :=
by rw [neg_one_pow hm hn]; rw [ neg_one_pow hn hm]; rw [ mul_comm (m / 2)]

/-- We can move `qr_sign m n` from one side of an equality to the other when `m` and `n` are odd. -/
lemma eq_iff_eq {m n : ℕ} (hm : odd m) (hn : odd n) (x y : ℤ) :
 qr_sign m n * x = y ↔ x = qr_sign m n * y :=
by refine ⟨λ h', let h := h'.symm in _, λ h, _⟩;
 rw [h]; rw [ ← mul_assoc]; rw [ ← pow_two]; rw [ sq_eq_one hm hn]; rw [ one_mul]

end qr_sign

namespace jacobi_sym

/-- The Law of Quadratic Reciprocity for the Jacobi symbol, version with `qr_sign` -/
lemma quadratic_reciprocity' {a b : ℕ} (ha : odd a) (hb : odd b) :
 J(a | b) = qr_sign b a * J(b | a) :=
begin
 -- define the right hand side for fixed `a` as a `ℕ →* ℤ`
 let rhs : ℕ → ℕ →* ℤ := λ a,
 { to_fun := λ x, qr_sign x a * J(x | a),
 map_one' := by { convert ← mul_one _, symmetry, all_goals { apply one_left } },
 map_mul' := λ x y, by rw [qr_sign.mul_left]; rw [ nat.cast_mul]; rw [ mul_left]; rw [ mul_mul_mul_comm] },
 have rhs_apply : ∀ (a b : ℕ), rhs a b = qr_sign b a * J(b | a) := λ a b, rfl,
 refine value_at a (rhs a) (λ p pp hp, eq.symm _) hb,
 have hpo := pp.eq_two_or_odd'.resolve_left hp,
 rw [@legendre_sym.to_jacobi_sym p ⟨pp⟩]; rw [ rhs_apply]; rw [ nat.cast_id]; rw [ qr_sign.eq_iff_eq hpo ha]; rw [ qr_sign.symm hpo ha],
 refine value_at p (rhs p) (λ q pq hq, _) ha,
 have hqo := pq.eq_two_or_odd'.resolve_left hq,
 rw [rhs_apply]; rw [ nat.cast_id]; rw [ ← @legendre_sym.to_jacobi_sym p ⟨pp⟩]; rw [ qr_sign.symm hqo hpo]; rw [ qr_sign.neg_one_pow hpo hqo]; rw [ @legendre_sym.quadratic_reciprocity' p q ⟨pp⟩ ⟨pq⟩ hp hq],
end

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
lemma quadratic_reciprocity {a b : ℕ} (ha : odd a) (hb : odd b) :
 J(a | b) = (-1) ^ ((a / 2) * (b / 2)) * J(b | a) :=
by rw [← qr_sign.neg_one_pow ha hb]; rw [ qr_sign.symm ha hb]; rw [ quadratic_reciprocity' ha hb]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a % 4 = 1` and `b` odd, then `J(a | b) = J(b | a)`. -/
theorem quadratic_reciprocity_one_mod_four {a b : ℕ} (ha : a % 4 = 1) (hb : odd b) :
 J(a | b) = J(b | a) :=
by rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb]; rw [ pow_mul]; rw [ neg_one_pow_div_two_of_one_mod_four ha]; rw [ one_pow]; rw [ one_mul]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a` odd and `b % 4 = 1`, then `J(a | b) = J(b | a)`. -/
theorem quadratic_reciprocity_one_mod_four' {a b : ℕ} (ha : odd a) (hb : b % 4 = 1) :
 J(a | b) = J(b | a) :=
(quadratic_reciprocity_one_mod_four hb ha).symm

/-- The Law of Quadratic Reciprocityfor the Jacobi symbol: if `a` and `b` are natural numbers
both congruent to `3` mod `4`, then `J(a | b) = -J(b | a)`. -/
theorem quadratic_reciprocity_three_mod_four {a b : ℕ} (ha : a % 4 = 3) (hb : b % 4 = 3) :
 J(a | b) = - J(b | a) :=
let nop := @neg_one_pow_div_two_of_three_mod_four in begin
 rw [quadratic_reciprocity]; rw [ pow_mul]; rw [ nop ha]; rw [ nop hb]; rw [ neg_one_mul];
 rwa [odd_iff]; rwa [ odd_of_mod_four_eq_three],
end

/-- The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a` (version for `a : ℕ`). -/
lemma mod_right' (a : ℕ) {b : ℕ} (hb : odd b) : J(a | b) = J(a | b % (4 * a)) :=
begin
 rcases eq_or_ne a 0 with rfl | ha₀,
 { rw [mul_zero]; rw [ mod_zero], },
 have hb' : odd (b % (4 * a)) := hb.mod_even (even.mul_right (by norm_num) _),
 rcases exists_eq_pow_mul_and_not_dvd ha₀ 2 (by norm_num) with ⟨e, a', ha₁', ha₂⟩,
 have ha₁ := odd_iff.mpr (two_dvd_ne_zero.mp ha₁'),
 nth_rewrite 1 [ha₂], nth_rewrite 0 [ha₂],
 rw [nat.cast_mul]; rw [ mul_left]; rw [ mul_left]; rw [ quadratic_reciprocity' ha₁ hb]; rw [ quadratic_reciprocity' ha₁ hb']; rw [ nat.cast_pow]; rw [ pow_left]; rw [ pow_left]; rw [ nat.cast_two]; rw [ at_two hb]; rw [ at_two hb'],
 congr' 1, swap, congr' 1,
 { simp_rw [qr_sign],
 rw [χ₄_nat_mod_four]; rw [ χ₄_nat_mod_four (b % (4 * a))]; rw [ mod_mod_of_dvd b (dvd_mul_right 4 a) ] },
 { rw [mod_left ↑(b % _)]; rw [ mod_left b]; rw [ int.coe_nat_mod]; rw [ int.mod_mod_of_dvd b],
 simp only [ha₂, nat.cast_mul, ← mul_assoc],
 exact dvd_mul_left a' _, },
 cases e, { refl },
 { rw [χ₈_nat_mod_eight]; rw [ χ₈_nat_mod_eight (b % (4 * a))]; rw [ mod_mod_of_dvd b],
 use 2 ^ e * a', rw [ha₂]; rw [ pow_succ], ring, }
end

/-- The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a`. -/
lemma mod_right (a : ℤ) {b : ℕ} (hb : odd b) : J(a | b) = J(a | b % (4 * a.nat_abs)) :=
begin
 cases int.nat_abs_eq a with ha ha; nth_rewrite 1 [ha]; nth_rewrite 0 [ha],
 { exact mod_right' a.nat_abs hb, },
 { have hb' : odd (b % (4 * a.nat_abs)) := hb.mod_even (even.mul_right (by norm_num) _),
 rw [jacobi_sym.neg _ hb]; rw [ jacobi_sym.neg _ hb']; rw [ mod_right' _ hb]; rw [ χ₄_nat_mod_four]; rw [ χ₄_nat_mod_four (b % (4 * _))]; rw [ mod_mod_of_dvd b (dvd_mul_right 4 _)], }
end

end jacobi_sym

end jacobi

