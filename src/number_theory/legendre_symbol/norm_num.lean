/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import number_theory.legendre_symbol.jacobi_symbol

/-!
# A `norm_num` extension for Jacobi and Legendre symbols

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We extend the `tactic.interactive.norm_num` tactic so that it can be used to provably compute
the value of the Jacobi symbol `J(a | b)` or the Legendre symbol `legendre_sym p a` when
the arguments are numerals.

## Implementation notes

We use the Law of Quadratic Reciprocity for the Jacobi symbol to compute the value of `J(a | b)`
efficiently, roughly comparable in effort with the euclidean algorithm for the computation
of the gcd of `a` and `b`. More precisely, the computation is done in the following steps.

* Use `J(a | 0) = 1` (an artifact of the definition) and `J(a | 1) = 1` to deal
 with corner cases.

* Use `J(a | b) = J(a % b | b)` to reduce to the case that `a` is a natural number.
 We define a version of the Jacobi symbol restricted to natural numbers for use in
 the following steps; see `norm_num.jacobi_sym_nat`. (But we'll continue to write `J(a | b)`
 in this description.)

* Remove powers of two from `b`. This is done via `J(2a | 2b) = 0` and
 `J(2a+1 | 2b) = J(2a+1 | b)` (another artifact of the definition).

* Now `0 ≤ a < b` and `b` is odd. If `b = 1`, then the value is `1`.
 If `a = 0` (and `b > 1`), then the value is `0`. Otherwise, we remove powers of two from `a`
 via `J(4a | b) = J(a | b)` and `J(2a | b) = ±J(a | b)`, where the sign is determined
 by the residue class of `b` mod 8, to reduce to `a` odd.

* Once `a` is odd, we use Quadratic Reciprocity (QR) in the form
 `J(a | b) = ±J(b % a | a)`, where the sign is determined by the residue classes
 of `a` and `b` mod 4. We are then back in the previous case.

We provide customized versions of these results for the various reduction steps,
where we encode the residue classes mod 2, mod 4, or mod 8 by using terms like
`bit1 (bit0 a)`. In this way, the only divisions we have to compute and prove
are the ones occurring in the use of QR above.
-/

section lemmas

namespace norm_num

/-- The Jacobi symbol restricted to natural numbers in both arguments. -/
def jacobi_sym_nat (a b : ℕ) : ℤ := jacobi_sym a b

/-!
### API Lemmas

We repeat part of the API for `jacobi_sym` with `norm_num.jacobi_sym_nat` and without implicit
arguments, in a form that is suitable for constructing proofs in `norm_num`.
-/

/-- Base cases: `b = 0`, `b = 1`, `a = 0`, `a = 1`. -/
lemma jacobi_sym_nat.zero_right (a : ℕ) : jacobi_sym_nat a 0 = 1 :=
by rwa [jacobi_sym_nat]; rwa [ jacobi_sym.zero_right]

lemma jacobi_sym_nat.one_right (a : ℕ) : jacobi_sym_nat a 1 = 1 :=
by rwa [jacobi_sym_nat]; rwa [ jacobi_sym.one_right]

lemma jacobi_sym_nat.zero_left_even (b : ℕ) (hb : b ≠ 0) : jacobi_sym_nat 0 (bit0 b) = 0 :=
by rw [jacobi_sym_nat]; rw [ nat.cast_zero]; rw [ jacobi_sym.zero_left (nat.one_lt_bit0 hb)]

lemma jacobi_sym_nat.zero_left_odd (b : ℕ) (hb : b ≠ 0) : jacobi_sym_nat 0 (bit1 b) = 0 :=
by rw [jacobi_sym_nat]; rw [ nat.cast_zero]; rw [ jacobi_sym.zero_left (nat.one_lt_bit1 hb)]

lemma jacobi_sym_nat.one_left_even (b : ℕ) : jacobi_sym_nat 1 (bit0 b) = 1 :=
by rw [jacobi_sym_nat]; rw [ nat.cast_one]; rw [ jacobi_sym.one_left]

lemma jacobi_sym_nat.one_left_odd (b : ℕ) : jacobi_sym_nat 1 (bit1 b) = 1 :=
by rw [jacobi_sym_nat]; rw [ nat.cast_one]; rw [ jacobi_sym.one_left]

/-- Turn a Legendre symbol into a Jacobi symbol. -/
lemma legendre_sym.to_jacobi_sym (p : ℕ) (pp : fact (p.prime)) (a r : ℤ) (hr : jacobi_sym a p = r) :
 legendre_sym p a = r :=
by rwa [@legendre_sym.to_jacobi_sym p pp a]

/-- The value depends only on the residue class of `a` mod `b`. -/
lemma jacobi_sym.mod_left (a : ℤ) (b ab' : ℕ) (ab r b' : ℤ) (hb' : (b : ℤ) = b')
 (hab : a % b' = ab) (h : (ab' : ℤ) = ab) (hr : jacobi_sym_nat ab' b = r) :
 jacobi_sym a b = r :=
by rw [← hr]; rw [ jacobi_sym_nat]; rw [ jacobi_sym.mod_left]; rw [ hb']; rw [ hab]; rw [ ← h]

lemma jacobi_sym_nat.mod_left (a b ab : ℕ) (r : ℤ) (hab : a % b = ab)
 (hr : jacobi_sym_nat ab b = r) :
 jacobi_sym_nat a b = r :=
by { rw [← hr]; rw [ jacobi_sym_nat]; rw [ jacobi_sym_nat]; rw [ _root_.jacobi_sym.mod_left a b]; rw [ ← hab], refl, }

/-- The symbol vanishes when both entries are even (and `b ≠ 0`). -/
lemma jacobi_sym_nat.even_even (a b : ℕ) (hb₀ : b ≠ 0) :
 jacobi_sym_nat (bit0 a) (bit0 b) = 0 :=
begin
 refine jacobi_sym.eq_zero_iff.mpr ⟨nat.bit0_ne_zero hb₀, λ hf, _⟩,
 have h : 2 ∣ (bit0 a).gcd (bit0 b) := nat.dvd_gcd two_dvd_bit0 two_dvd_bit0,
 change 2 ∣ (bit0 a : ℤ).gcd (bit0 b) at h,
 rw [← nat.cast_bit0] at h; rw [ ← nat.cast_bit0] at h; rw [ hf] at h; rw [ ← even_iff_two_dvd] at h,
 exact nat.not_even_one h,
end

/-- When `a` is odd and `b` is even, we can replace `b` by `b / 2`. -/
lemma jacobi_sym_nat.odd_even (a b : ℕ) (r : ℤ) (hr : jacobi_sym_nat (bit1 a) b = r) :
 jacobi_sym_nat (bit1 a) (bit0 b) = r :=
begin
 have ha : legendre_sym 2 (bit1 a) = 1 :=
 by simp only [legendre_sym, quadratic_char_apply, quadratic_char_fun_one, int.cast_bit1,
 char_two.bit1_eq_one, pi.one_apply],
 cases eq_or_ne b 0 with hb hb,
 { rw [← hr]; rw [ hb]; rw [ jacobi_sym_nat.zero_right], },
 { haveI : ne_zero b := ⟨hb⟩, -- for `jacobi_sym.mul_right`
 rwa [bit0_eq_two_mul b]; rwa [ jacobi_sym_nat]; rwa [ jacobi_sym.mul_right]; rwa [ ← _root_.legendre_sym.to_jacobi_sym]; rwa [ nat.cast_bit1]; rwa [ ha]; rwa [ one_mul], }
end

/-- If `a` is divisible by `4` and `b` is odd, then we can remove the factor `4` from `a`. -/
lemma jacobi_sym_nat.double_even (a b : ℕ) (r : ℤ) (hr : jacobi_sym_nat a (bit1 b) = r) :
 jacobi_sym_nat (bit0 (bit0 a)) (bit1 b) = r :=
begin
 have : ((2 : ℕ) : ℤ).gcd ((bit1 b) : ℕ) = 1,
 { rw [int.coe_nat_gcd]; rw [ nat.bit1_eq_succ_bit0]; rw [ bit0_eq_two_mul b]; rw [ nat.succ_eq_add_one]; rw [ nat.gcd_mul_left_add_right]; rw [ nat.gcd_one_right], },
 rwa [bit0_eq_two_mul a]; rwa [ bit0_eq_two_mul (2 * a)]; rwa [ ← mul_assoc]; rwa [ ← pow_two]; rwa [ jacobi_sym_nat]; rwa [ nat.cast_mul]; rwa [ nat.cast_pow]; rwa [ jacobi_sym.mul_left]; rwa [ jacobi_sym.sq_one' this]; rwa [ one_mul],
end

/-- If `a` is even and `b` is odd, then we can remove a factor `2` from `a`,
but we may have to change the sign, depending on `b % 8`.
We give one version for each of the four odd residue classes mod `8`. -/
lemma jacobi_sym_nat.even_odd₁ (a b : ℕ) (r : ℤ)
 (hr : jacobi_sym_nat a (bit1 (bit0 (bit0 b))) = r) :
 jacobi_sym_nat (bit0 a) (bit1 (bit0 (bit0 b))) = r :=
begin
 have hb : (bit1 (bit0 (bit0 b))) % 8 = 1,
 { rw [nat.bit1_mod_bit0]; rw [ nat.bit0_mod_bit0]; rw [ nat.bit0_mod_two], },
 rw [jacobi_sym_nat]; rw [ bit0_eq_two_mul a]; rw [ nat.cast_mul]; rw [ jacobi_sym.mul_left]; rw [ nat.cast_two]; rw [ jacobi_sym.at_two (odd_bit1 _)]; rw [ zmod.χ₈_nat_mod_eight]; rw [ hb],
 norm_num,
 exact hr,
end

lemma jacobi_sym_nat.even_odd₇ (a b : ℕ) (r : ℤ)
 (hr : jacobi_sym_nat a (bit1 (bit1 (bit1 b))) = r) :
 jacobi_sym_nat (bit0 a) (bit1 (bit1 (bit1 b))) = r :=
begin
 have hb : (bit1 (bit1 (bit1 b))) % 8 = 7,
 { rw [nat.bit1_mod_bit0]; rw [ nat.bit1_mod_bit0]; rw [ nat.bit1_mod_two], },
 rw [jacobi_sym_nat]; rw [ bit0_eq_two_mul a]; rw [ nat.cast_mul]; rw [ jacobi_sym.mul_left]; rw [ nat.cast_two]; rw [ jacobi_sym.at_two (odd_bit1 _)]; rw [ zmod.χ₈_nat_mod_eight]; rw [ hb],
 norm_num,
 exact hr,
end

lemma jacobi_sym_nat.even_odd₃ (a b : ℕ) (r : ℤ)
 (hr : jacobi_sym_nat a (bit1 (bit1 (bit0 b))) = r) :
 jacobi_sym_nat (bit0 a) (bit1 (bit1 (bit0 b))) = -r :=
begin
 have hb : (bit1 (bit1 (bit0 b))) % 8 = 3,
 { rw [nat.bit1_mod_bit0]; rw [ nat.bit1_mod_bit0]; rw [ nat.bit0_mod_two], },
 rw [jacobi_sym_nat]; rw [ bit0_eq_two_mul a]; rw [ nat.cast_mul]; rw [ jacobi_sym.mul_left]; rw [ nat.cast_two]; rw [ jacobi_sym.at_two (odd_bit1 _)]; rw [ zmod.χ₈_nat_mod_eight]; rw [ hb],
 norm_num,
 exact hr,
end

lemma jacobi_sym_nat.even_odd₅ (a b : ℕ) (r : ℤ)
 (hr : jacobi_sym_nat a (bit1 (bit0 (bit1 b))) = r) :
 jacobi_sym_nat (bit0 a) (bit1 (bit0 (bit1 b))) = -r :=
begin
 have hb : (bit1 (bit0 (bit1 b))) % 8 = 5,
 { rw [nat.bit1_mod_bit0]; rw [ nat.bit0_mod_bit0]; rw [ nat.bit1_mod_two], },
 rw [jacobi_sym_nat]; rw [ bit0_eq_two_mul a]; rw [ nat.cast_mul]; rw [ jacobi_sym.mul_left]; rw [ nat.cast_two]; rw [ jacobi_sym.at_two (odd_bit1 _)]; rw [ zmod.χ₈_nat_mod_eight]; rw [ hb],
 norm_num,
 exact hr,
end

/-- Use quadratic reciproity to reduce to smaller `b`. -/
lemma jacobi_sym_nat.qr₁ (a b : ℕ) (r : ℤ) (hr : jacobi_sym_nat (bit1 b) (bit1 (bit0 a)) = r) :
 jacobi_sym_nat (bit1 (bit0 a)) (bit1 b) = r :=
begin
 have ha : (bit1 (bit0 a)) % 4 = 1,
 { rw [nat.bit1_mod_bit0]; rw [ nat.bit0_mod_two], },
 have hb := nat.bit1_mod_two,
 rwa [jacobi_sym_nat]; rwa [ jacobi_sym.quadratic_reciprocity_one_mod_four ha (nat.odd_iff.mpr hb)],
end

lemma jacobi_sym_nat.qr₁_mod (a b ab : ℕ) (r : ℤ) (hab : (bit1 b) % (bit1 (bit0 a)) = ab)
 (hr : jacobi_sym_nat ab (bit1 (bit0 a)) = r) :
 jacobi_sym_nat (bit1 (bit0 a)) (bit1 b) = r :=
jacobi_sym_nat.qr₁ _ _ _ $ jacobi_sym_nat.mod_left _ _ ab r hab hr

lemma jacobi_sym_nat.qr₁' (a b : ℕ) (r : ℤ) (hr : jacobi_sym_nat (bit1 (bit0 b)) (bit1 a) = r) :
 jacobi_sym_nat (bit1 a) (bit1 (bit0 b)) = r :=
begin
 have hb : (bit1 (bit0 b)) % 4 = 1,
 { rw [nat.bit1_mod_bit0]; rw [ nat.bit0_mod_two], },
 have ha := nat.bit1_mod_two,
 rwa [jacobi_sym_nat]; rwa [ ← jacobi_sym.quadratic_reciprocity_one_mod_four hb (nat.odd_iff.mpr ha)]
end

lemma jacobi_sym_nat.qr₁'_mod (a b ab : ℕ) (r : ℤ) (hab : (bit1 (bit0 b)) % (bit1 a) = ab)
 (hr : jacobi_sym_nat ab (bit1 a) = r) :
 jacobi_sym_nat (bit1 a) (bit1 (bit0 b)) = r :=
jacobi_sym_nat.qr₁' _ _ _ $ jacobi_sym_nat.mod_left _ _ ab r hab hr

lemma jacobi_sym_nat.qr₃ (a b : ℕ) (r : ℤ)
 (hr : jacobi_sym_nat (bit1 (bit1 b)) (bit1 (bit1 a)) = r) :
 jacobi_sym_nat (bit1 (bit1 a)) (bit1 (bit1 b)) = -r :=
begin
 have hb : (bit1 (bit1 b)) % 4 = 3,
 { rw [nat.bit1_mod_bit0]; rw [ nat.bit1_mod_two], },
 have ha : (bit1 (bit1 a)) % 4 = 3,
 { rw [nat.bit1_mod_bit0]; rw [ nat.bit1_mod_two], },
 rwa [jacobi_sym_nat]; rwa [ jacobi_sym.quadratic_reciprocity_three_mod_four ha hb]; rwa [ neg_inj]
end

lemma jacobi_sym_nat.qr₃_mod (a b ab : ℕ) (r : ℤ) (hab : (bit1 (bit1 b)) % (bit1 (bit1 a)) = ab)
 (hr : jacobi_sym_nat ab (bit1 (bit1 a)) = r) :
 jacobi_sym_nat (bit1 (bit1 a)) (bit1 (bit1 b)) = -r :=
jacobi_sym_nat.qr₃ _ _ _ $ jacobi_sym_nat.mod_left _ _ ab r hab hr

end norm_num

end lemmas

section evaluation

/-!
### Certified evaluation of the Jacobi symbol

The following functions recursively evaluate a Jacobi symbol and construct the
corresponding proof term.
-/

namespace norm_num
open tactic

/-- This evaluates `r := jacobi_sym_nat a b` recursively using quadratic reciprocity
and produces a proof term for the equality, assuming that `a < b` and `b` is odd. -/
meta def prove_jacobi_sym_odd : instance_cache → instance_cache → expr → expr →
 tactic (instance_cache × instance_cache × expr × expr)
| zc nc ea eb := do
 match match_numeral eb with
 | match_numeral_result.one := -- `b = 1`, result is `1`
 pure (zc, nc, `(1 : ℤ), `(jacobi_sym_nat.one_right).mk_app [ea])
 | match_numeral_result.bit1 eb₁ := do -- `b > 1` (recall that `b` is odd)
 match match_numeral ea with
 | match_numeral_result.zero := do -- `a = 0`, result is `0`
 b ← eb₁.to_nat,
 (nc, phb₀) ← prove_ne nc eb₁ `(0 : ℕ) b 0, -- proof of `b ≠ 0`
 pure (zc, nc, `(0 : ℤ), `(jacobi_sym_nat.zero_left_odd).mk_app [eb₁, phb₀])
 | match_numeral_result.one := do -- `a = 1`, result is `1`
 pure (zc, nc, `(1 : ℤ), `(jacobi_sym_nat.one_left_odd).mk_app [eb₁])
 | match_numeral_result.bit0 ea₁ := do -- `a` is even; check if divisible by `4`
 match match_numeral ea₁ with
 | match_numeral_result.bit0 ea₂ := do
 (zc, nc, er, p) ← prove_jacobi_sym_odd zc nc ea₂ eb, -- compute `jacobi_sym_nat (a / 4) b`
 pure (zc, nc, er, `(jacobi_sym_nat.double_even).mk_app [ea₂, eb₁, er, p])
 | _ := do -- reduce to `a / 2`; need to consider `b % 8`
 (zc, nc, er, p) ← prove_jacobi_sym_odd zc nc ea₁ eb, -- compute `jacobi_sym_nat (a / 2) b`
 match match_numeral eb₁ with
 -- | match_numeral_result.zero := -- `b = 1`, not reached
 | match_numeral_result.one := do -- `b = 3`
 r ← er.to_int,
 (zc, er') ← zc.of_int (- r),
 pure (zc, nc, er', `(jacobi_sym_nat.even_odd₃).mk_app [ea₁, `(0 : ℕ), er, p])
 | match_numeral_result.bit0 eb₂ := do -- `b % 4 = 1`
 match match_numeral eb₂ with
 -- | match_numeral_result.zero := -- not reached
 | match_numeral_result.one := do -- `b = 5`
 r ← er.to_int,
 (zc, er') ← zc.of_int (- r),
 pure (zc, nc, er', `(jacobi_sym_nat.even_odd₅).mk_app [ea₁, `(0 : ℕ), er, p])
 | match_numeral_result.bit0 eb₃ := do -- `b % 8 = 1`
 pure (zc, nc, er, `(jacobi_sym_nat.even_odd₁).mk_app [ea₁, eb₃, er, p])
 | match_numeral_result.bit1 eb₃ := do -- `b % 8 = 5`
 r ← er.to_int,
 (zc, er') ← zc.of_int (- r),
 pure (zc, nc, er', `(jacobi_sym_nat.even_odd₅).mk_app [ea₁, eb₃, er, p])
 | _ := failed
 end
 | match_numeral_result.bit1 eb₂ := do -- `b % 4 = 3`
 match match_numeral eb₂ with
 -- | match_numeral_result.zero := -- not reached
 | match_numeral_result.one := do -- `b = 7`
 pure (zc, nc, er, `(jacobi_sym_nat.even_odd₇).mk_app [ea₁, `(0 : ℕ), er, p])
 | match_numeral_result.bit0 eb₃ := do -- `b % 8 = 3`
 r ← er.to_int,
 (zc, er') ← zc.of_int (- r),
 pure (zc, nc, er', `(jacobi_sym_nat.even_odd₃).mk_app [ea₁, eb₃, er, p])
 | match_numeral_result.bit1 eb₃ := do -- `b % 8 = 7`
 pure (zc, nc, er, `(jacobi_sym_nat.even_odd₇).mk_app [ea₁, eb₃, er, p])
 | _ := failed
 end
 | _ := failed
 end
 end
 | match_numeral_result.bit1 ea₁ := do -- `a` is odd
 -- use Quadratic Reciprocity; look at `a` and `b` mod `4`
 (nc, bma, phab) ← prove_div_mod nc eb ea tt, -- compute `b % a`
 (zc, nc, er, p) ← prove_jacobi_sym_odd zc nc bma ea, -- compute `jacobi_sym_nat (b % a) a`
 match match_numeral ea₁ with
 -- | match_numeral_result.zero := -- `a = 1`, not reached
 | match_numeral_result.one := do -- `a = 3`; need to consider `b`
 match match_numeral eb₁ with
 -- | match_numeral_result.zero := -- `b = 1`, not reached
 -- | match_numeral_result.one := -- `b = 3`, not reached, since `a < b`
 | match_numeral_result.bit0 eb₂ := do -- `b % 4 = 1`
 pure (zc, nc, er, `(jacobi_sym_nat.qr₁'_mod).mk_app [ea₁, eb₂, bma, er, phab, p])
 | match_numeral_result.bit1 eb₂ := do -- `b % 4 = 3`
 r ← er.to_int,
 (zc, er') ← zc.of_int (- r),
 pure (zc, nc, er', `(jacobi_sym_nat.qr₃_mod).mk_app [`(0 : ℕ), eb₂, bma, er, phab, p])
 | _ := failed
 end
 | match_numeral_result.bit0 ea₂ := do -- `a % 4 = 1`
 pure (zc, nc, er, `(jacobi_sym_nat.qr₁_mod).mk_app [ea₂, eb₁, bma, er, phab, p])
 | match_numeral_result.bit1 ea₂ := do -- `a % 4 = 3`; need to consider `b`
 match match_numeral eb₁ with
 -- | match_numeral_result.zero := do -- `b = 1`, not reached
 -- | match_numeral_result.one := do -- `b = 3`, not reached, since `a < b`
 | match_numeral_result.bit0 eb₂ := do -- `b % 4 = 1`
 pure (zc, nc, er, `(jacobi_sym_nat.qr₁'_mod).mk_app [ea₁, eb₂, bma, er, phab, p])
 | match_numeral_result.bit1 eb₂ := do -- `b % 4 = 3`
 r ← er.to_int,
 (zc, er') ← zc.of_int (- r),
 pure (zc, nc, er', `(jacobi_sym_nat.qr₃_mod).mk_app [ea₂, eb₂, bma, er, phab, p])
 | _ := failed
 end
 | _ := failed
 end
 | _ := failed
 end
 | _ := failed
 end

/-- This evaluates `r := jacobi_sym_nat a b` and produces a proof term for the equality
by removing powers of `2` from `b` and then calling `prove_jacobi_sym_odd`. -/
meta def prove_jacobi_sym_nat : instance_cache → instance_cache → expr → expr →
 tactic (instance_cache × instance_cache × expr × expr)
| zc nc ea eb := do
 match match_numeral eb with
 | match_numeral_result.zero := -- `b = 0`, result is `1`
 pure (zc, nc, `(1 : ℤ), `(jacobi_sym_nat.zero_right).mk_app [ea])
 | match_numeral_result.one := -- `b = 1`, result is `1`
 pure (zc, nc, `(1 : ℤ), `(jacobi_sym_nat.one_right).mk_app [ea])
 | match_numeral_result.bit0 eb₁ := -- `b` is even and nonzero
 match match_numeral ea with
 | match_numeral_result.zero := do -- `a = 0`, result is `0`
 b ← eb₁.to_nat,
 (nc, phb₀) ← prove_ne nc eb₁ `(0 : ℕ) b 0, -- proof of `b ≠ 0`
 pure (zc, nc, `(0 : ℤ), `(jacobi_sym_nat.zero_left_even).mk_app [eb₁, phb₀])
 | match_numeral_result.one := do -- `a = 1`, result is `1`
 pure (zc, nc, `(1 : ℤ), `(jacobi_sym_nat.one_left_even).mk_app [eb₁])
 | match_numeral_result.bit0 ea₁ := do -- `a` is even, result is `0`
 b ← eb₁.to_nat,
 (nc, phb₀) ← prove_ne nc eb₁ `(0 : ℕ) b 0, -- proof of `b ≠ 0`
 let er : expr := `(0 : ℤ),
 pure (zc, nc, er, `(jacobi_sym_nat.even_even).mk_app [ea₁, eb₁, phb₀])
 | match_numeral_result.bit1 ea₁ := do -- `a` is odd, reduce to `b / 2`
 (zc, nc, er, p) ← prove_jacobi_sym_nat zc nc ea eb₁,
 pure (zc, nc, er, `(jacobi_sym_nat.odd_even).mk_app [ea₁, eb₁, er, p])
 | _ := failed
 end
 | match_numeral_result.bit1 eb₁ := do -- `b` is odd
 a ← ea.to_nat,
 b ← eb.to_nat,
 if b ≤ a then do -- reduce to `jacobi_sym_nat (a % b) b`
 (nc, amb, phab) ← prove_div_mod nc ea eb tt, -- compute `a % b`
 (zc, nc, er, p) ← prove_jacobi_sym_odd zc nc amb eb, -- compute `jacobi_sym_nat (a % b) b`
 pure (zc, nc, er, `(jacobi_sym_nat.mod_left).mk_app [ea, eb, amb, er, phab, p])
 else
 prove_jacobi_sym_odd zc nc ea eb
 | _ := failed
 end

/-- This evaluates `r := jacobi_sym a b` and produces a proof term for the equality.
This is done by reducing to `r := jacobi_sym_nat (a % b) b`. -/
meta def prove_jacobi_sym : instance_cache → instance_cache → expr → expr
 → tactic (instance_cache × instance_cache × expr × expr)
| zc nc ea eb := do
 match match_numeral eb with -- deal with simple cases right away
 | match_numeral_result.zero := pure (zc, nc, `(1 : ℤ), `(jacobi_sym.zero_right).mk_app [ea])
 | match_numeral_result.one := pure (zc, nc, `(1 : ℤ), `(jacobi_sym.one_right).mk_app [ea])
 | _ := do -- Now `1 < b`. Compute `jacobi_sym_nat (a % b) b` instead.
 b ← eb.to_nat,
 (zc, eb') ← zc.of_int (b : ℤ),
 -- Get the proof that `(b : ℤ) = b'` (where `eb'` is the numeral representing `b'`).
 -- This is important to avoid inefficient matching between the two.
 (zc, nc, eb₁, pb') ← prove_nat_uncast zc nc eb',
 (zc, amb, phab) ← prove_div_mod zc ea eb' tt, -- compute `a % b`
 (zc, nc, amb', phab') ← prove_nat_uncast zc nc amb, -- `a % b` as a natural number
 (zc, nc, er, p) ← prove_jacobi_sym_nat zc nc amb' eb₁, -- compute `jacobi_sym_nat (a % b) b`
 pure (zc, nc, er,
 `(jacobi_sym.mod_left).mk_app [ea, eb₁, amb', amb, er, eb', pb', phab, phab', p])
 end

end norm_num

end evaluation

section tactic

/-!
### The `norm_num` plug-in
-/

namespace tactic
namespace norm_num

/-- This is the `norm_num` plug-in that evaluates Jacobi and Legendre symbols. -/
@[norm_num] meta def eval_jacobi_sym : expr → tactic (expr × expr)
| `(jacobi_sym %%ea %%eb) := do -- Jacobi symbol
 zc ← mk_instance_cache `(ℤ),
 nc ← mk_instance_cache `(ℕ),
 (prod.snd ∘ prod.snd) <$> norm_num.prove_jacobi_sym zc nc ea eb
| `(norm_num.jacobi_sym_nat %%ea %%eb) := do -- Jacobi symbol on natural numbers
 zc ← mk_instance_cache `(ℤ),
 nc ← mk_instance_cache `(ℕ),
 (prod.snd ∘ prod.snd) <$> norm_num.prove_jacobi_sym_nat zc nc ea eb
| `(@legendre_sym %%ep %%inst %%ea) := do -- Legendre symbol
 zc ← mk_instance_cache `(ℤ),
 nc ← mk_instance_cache `(ℕ),
 (zc, nc, er, pf) ← norm_num.prove_jacobi_sym zc nc ea ep,
 pure (er, `(norm_num.legendre_sym.to_jacobi_sym).mk_app [ep, inst, ea, er, pf])
| _ := failed

end norm_num
end tactic

end tactic

