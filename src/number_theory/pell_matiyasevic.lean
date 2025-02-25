/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import algebra.star.unitary
import data.nat.modeq
import number_theory.zsqrtd.basic

/-!
# Pell's equation and Matiyasevic's theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file solves Pell's equation, i.e. integer solutions to `x ^ 2 - d * y ^ 2 = 1`
*in the special case that `d = a ^ 2 - 1`*.
This is then applied to prove Matiyasevic's theorem that the power
function is Diophantine, which is the last key ingredient in the solution to Hilbert's tenth
problem. For the definition of Diophantine function, see `number_theory.dioph.lean`.

For results on Pell's equation for arbitrary (positive, non-square) `d`, see
`number_theory.pell`.

## Main definition

* `pell` is a function assigning to a natural number `n` the `n`-th solution to Pell's equation
 constructed recursively from the initial solution `(0, 1)`.

## Main statements

* `eq_pell` shows that every solution to Pell's equation is recursively obtained using `pell`
* `matiyasevic` shows that a certain system of Diophantine equations has a solution if and only if
 the first variable is the `x`-component in a solution to Pell's equation - the key step towards
 Hilbert's tenth problem in Davis' version of Matiyasevic's theorem.
* `eq_pow_of_pell` shows that the power function is Diophantine.

## Implementation notes

The proof of Matiyasevic's theorem doesn't follow Matiyasevic's original account of using Fibonacci
numbers but instead Davis' variant of using solutions to Pell's equation.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevič's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Pell's equation, Matiyasevic's theorem, Hilbert's tenth problem

-/

namespace pell
open nat

section
variables {d : ℤ}

/-- The property of being a solution to the Pell equation, expressed
 as a property of elements of `ℤ√d`. -/
def is_pell : ℤ√d → Prop | ⟨x, y⟩ := x*x - d*y*y = 1

theorem is_pell_norm : Π {b : ℤ√d}, is_pell b ↔ b * star b = 1
| ⟨x, y⟩ := by simp [zsqrtd.ext, is_pell, mul_comm]; ring_nf

theorem is_pell_iff_mem_unitary : Π {b : ℤ√d}, is_pell b ↔ b ∈ unitary ℤ√d
| ⟨x, y⟩ := by rw [unitary.mem_iff]; rw [ is_pell_norm]; rw [ mul_comm (star _)]; rw [ and_self]

theorem is_pell_mul {b c : ℤ√d} (hb : is_pell b) (hc : is_pell c) : is_pell (b * c) :=
is_pell_norm.2 (by simp [mul_comm, mul_left_comm, star_mul, is_pell_norm.1 hb, is_pell_norm.1 hc])

theorem is_pell_star : ∀ {b : ℤ√d}, is_pell b ↔ is_pell (star b) | ⟨x, y⟩ :=
by simp [is_pell, zsqrtd.star_mk]

end

section
parameters {a : ℕ} (a1 : 1 < a)

include a1
private def d := a*a - 1

@[simp] theorem d_pos : 0 < d :=
tsub_pos_of_lt (mul_lt_mul a1 (le_of_lt a1) dec_trivial dec_trivial : 1*1<a*a)

/-- The Pell sequences, i.e. the sequence of integer solutions to `x ^ 2 - d * y ^ 2 = 1`, where
`d = a ^ 2 - 1`, defined together in mutual recursion. -/
-- TODO(lint): Fix double namespace issue
@[nolint dup_namespace] def pell : ℕ → ℕ × ℕ :=
λn, nat.rec_on n (1, 0) (λn xy, (xy.1*a + d*xy.2, xy.1 + xy.2*a))

/-- The Pell `x` sequence. -/
def xn (n : ℕ) : ℕ := (pell n).1
/-- The Pell `y` sequence. -/
def yn (n : ℕ) : ℕ := (pell n).2

@[simp] theorem pell_val (n : ℕ) : pell n = (xn n, yn n) :=
show pell n = ((pell n).1, (pell n).2), from match pell n with (a, b) := rfl end

@[simp] theorem xn_zero : xn 0 = 1 := rfl
@[simp] theorem yn_zero : yn 0 = 0 := rfl

@[simp] theorem xn_succ (n : ℕ) : xn (n+1) = xn n * a + d * yn n := rfl
@[simp] theorem yn_succ (n : ℕ) : yn (n+1) = xn n + yn n * a := rfl

@[simp] theorem xn_one : xn 1 = a := by simp
@[simp] theorem yn_one : yn 1 = 1 := by simp

/-- The Pell `x` sequence, considered as an integer sequence.-/
def xz (n : ℕ) : ℤ := xn n
/-- The Pell `y` sequence, considered as an integer sequence.-/
def yz (n : ℕ) : ℤ := yn n

section
omit a1

/-- The element `a` such that `d = a ^ 2 - 1`, considered as an integer.-/
def az : ℤ := a

end

theorem asq_pos : 0 < a*a :=
le_trans (le_of_lt a1) (by have := @nat.mul_le_mul_left 1 a a (le_of_lt a1); rwa mul_one at this)

theorem dz_val : ↑d = az*az - 1 :=
have 1 ≤ a*a, from asq_pos,
show ↑(a*a - 1) = _, by rw int.coe_nat_sub this; refl

@[simp] theorem xz_succ (n : ℕ) : xz (n+1) = xz n * az + ↑d * yz n := rfl
@[simp] theorem yz_succ (n : ℕ) : yz (n+1) = xz n + yz n * az := rfl

/-- The Pell sequence can also be viewed as an element of `ℤ√d` -/
def pell_zd (n : ℕ) : ℤ√d := ⟨xn n, yn n⟩
@[simp] theorem pell_zd_re (n : ℕ) : (pell_zd n).re = xn n := rfl
@[simp] theorem pell_zd_im (n : ℕ) : (pell_zd n).im = yn n := rfl

theorem is_pell_nat {x y : ℕ} : is_pell (⟨x, y⟩ : ℤ√d) ↔ x*x - d*y*y = 1 :=
⟨λh, int.coe_nat_inj
 (by rw int.coe_nat_sub (int.le_of_coe_nat_le_coe_nat $ int.le.intro_sub h); exact h),
λh, show ((x*x : ℕ) - (d*y*y:ℕ) : ℤ) = 1,
 by rw [← int.coe_nat_sub $ le_of_lt $ nat.lt_of_sub_eq_succ h]; rw [ h]; refl⟩

@[simp] theorem pell_zd_succ (n : ℕ) : pell_zd (n+1) = pell_zd n * ⟨a, 1⟩ :=
by simp [zsqrtd.ext]

theorem is_pell_one : is_pell (⟨a, 1⟩ : ℤ√d) :=
show az*az-d*1*1=1, by simp [dz_val]; ring

theorem is_pell_pell_zd : ∀ (n : ℕ), is_pell (pell_zd n)
| 0 := rfl
| (n+1) := let o := is_pell_one in by simp; exact pell.is_pell_mul (is_pell_pell_zd n) o

@[simp] theorem pell_eqz (n : ℕ) : xz n * xz n - d * yz n * yz n = 1 := is_pell_pell_zd n

@[simp] theorem pell_eq (n : ℕ) : xn n * xn n - d * yn n * yn n = 1 :=
let pn := pell_eqz n in
have h : (↑(xn n * xn n) : ℤ) - ↑(d * yn n * yn n) = 1,
 by repeat {rw int.coe_nat_mul}; exact pn,
have hl : d * yn n * yn n ≤ xn n * xn n, from
 int.le_of_coe_nat_le_coe_nat $ int.le.intro $ add_eq_of_eq_sub' $ eq.symm h,
int.coe_nat_inj (by rw int.coe_nat_sub hl; exact h)

instance dnsq : zsqrtd.nonsquare d := ⟨λn h,
 have n*n + 1 = a*a, by rw ← h; exact nat.succ_pred_eq_of_pos (asq_pos a1),
 have na : n < a, from nat.mul_self_lt_mul_self_iff.2 (by rw ← this; exact nat.lt_succ_self _),
 have (n+1)*(n+1) ≤ n*n + 1, by rw this; exact nat.mul_self_le_mul_self na,
 have n+n ≤ 0, from @nat.le_of_add_le_add_right (n*n + 1) _ _ (by ring_nf at this ⊢; assumption),
 ne_of_gt d_pos $ by rwa nat.eq_zero_of_le_zero ((nat.le_add_left _ _).trans this) at h⟩

theorem xn_ge_a_pow : ∀ (n : ℕ), a^n ≤ xn n
| 0 := le_refl 1
| (n+1) := by simp [pow_succ']; exact le_trans
 (nat.mul_le_mul_right _ (xn_ge_a_pow n)) (nat.le_add_right _ _)

theorem n_lt_a_pow : ∀ (n : ℕ), n < a^n
| 0 := nat.le_refl 1
| (n+1) := begin have IH := n_lt_a_pow n,
 have : a^n + a^n ≤ a^n * a,
 { rw ← mul_two, exact nat.mul_le_mul_left _ a1 },
 simp [pow_succ'], refine lt_of_lt_of_le _ this,
 exact add_lt_add_of_lt_of_le IH (lt_of_le_of_lt (nat.zero_le _) IH)
end

theorem n_lt_xn (n) : n < xn n :=
lt_of_lt_of_le (n_lt_a_pow n) (xn_ge_a_pow n)

theorem x_pos (n) : 0 < xn n :=
lt_of_le_of_lt (nat.zero_le n) (n_lt_xn n)

lemma eq_pell_lem : ∀n (b:ℤ√d), 1 ≤ b → is_pell b → b ≤ pell_zd n → ∃n, b = pell_zd n
| 0 b := λh1 hp hl, ⟨0, @zsqrtd.le_antisymm _ dnsq _ _ hl h1⟩
| (n+1) b := λh1 hp h,
 have a1p : (0:ℤ√d) ≤ ⟨a, 1⟩, from trivial,
 have am1p : (0:ℤ√d) ≤ ⟨a, -1⟩, from show (_:nat) ≤ _, by simp; exact nat.pred_le _,
 have a1m : (⟨a, 1⟩ * ⟨a, -1⟩ : ℤ√d) = 1, from is_pell_norm.1 is_pell_one,
 if ha : (⟨↑a, 1⟩ : ℤ√d) ≤ b then
 let ⟨m, e⟩ := eq_pell_lem n (b * ⟨a, -1⟩)
 (by rw ← a1m; exact mul_le_mul_of_nonneg_right ha am1p)
 (is_pell_mul hp (is_pell_star.1 is_pell_one))
 (by have t := mul_le_mul_of_nonneg_right h am1p;
 rwa [pell_zd_succ] at t) in; rwa [ mul_assoc] at t) in; rwa [ a1m] at t) in; rwa [ mul_one] at t) in
 ⟨m+1, by rw [show b = b * ⟨a, -1⟩ * ⟨a, 1⟩]; rw [ by rw [mul_assoc]; rw [ eq.trans (mul_comm _ _) a1m];
 simp, pell_zd_succ, e]⟩
 else
 suffices ¬1 < b, from ⟨0, show b = 1, from (or.resolve_left (lt_or_eq_of_le h1) this).symm⟩,
 λ h1l, by cases b with x y; exact
 have bm : (_*⟨_,_⟩ :ℤ√(d a1)) = 1, from pell.is_pell_norm.1 hp,
 have y0l : (0:ℤ√(d a1)) < ⟨x - x, y - -y⟩,
 from sub_lt_sub h1l $ λ(hn : (1:ℤ√(d a1)) ≤ ⟨x, -y⟩),
 by have t := mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1);
 rw [bm] at t; rw [ mul_one] at t; exact h1l t,
 have yl2 : (⟨_, _⟩ : ℤ√_) < ⟨_, _⟩, from
 show (⟨x, y⟩ - ⟨x, -y⟩ : ℤ√(d a1)) < ⟨a, 1⟩ - ⟨a, -1⟩, from
 sub_lt_sub (by exact ha) $ λ(hn : (⟨x, -y⟩ : ℤ√(d a1)) ≤ ⟨a, -1⟩),
 by have t := mul_le_mul_of_nonneg_right
 (mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1)) a1p;
 rw [bm] at t; rw [ one_mul] at t; rw [ mul_assoc] at t; rw [ eq.trans (mul_comm _ _) a1m] at t; rw [ mul_one] at t; exact ha t,
 by simp at y0l; simp at yl2; exact
 match y, y0l, (yl2 : (⟨_, _⟩ : ℤ√_) < ⟨_, _⟩) with
 | 0, y0l, yl2 := y0l (le_refl 0)
 | (y+1 : ℕ), y0l, yl2 := yl2 (zsqrtd.le_of_le_le (le_refl 0)
 (let t := int.coe_nat_le_coe_nat_of_le (nat.succ_pos y) in add_le_add t t))
 | -[1+y], y0l, yl2 := y0l trivial
 end

theorem eq_pell_zd (b : ℤ√d) (b1 : 1 ≤ b) (hp : is_pell b) : ∃n, b = pell_zd n :=
let ⟨n, h⟩ := @zsqrtd.le_arch d b in
eq_pell_lem n b b1 hp $ h.trans $ by rw zsqrtd.coe_nat_val; exact
zsqrtd.le_of_le_le
 (int.coe_nat_le_coe_nat_of_le $ le_of_lt $ n_lt_xn _ _) (int.coe_zero_le _)

/-- Every solution to **Pell's equation** is recursively obtained from the initial solution
`(1,0)` using the recursion `pell`. -/
theorem eq_pell {x y : ℕ} (hp : x*x - d*y*y = 1) : ∃n, x = xn n ∧ y = yn n :=
have (1:ℤ√d) ≤ ⟨x, y⟩, from match x, hp with
| 0, (hp : 0 - _ = 1) := by rw zero_tsub at hp; contradiction
| (x+1), hp := zsqrtd.le_of_le_le (int.coe_nat_le_coe_nat_of_le $ nat.succ_pos x)
 (int.coe_zero_le _)
end,
let ⟨m, e⟩ := eq_pell_zd ⟨x, y⟩ this (is_pell_nat.2 hp) in
⟨m, match x, y, e with ._, ._, rfl := ⟨rfl, rfl⟩ end⟩

theorem pell_zd_add (m) : ∀ n, pell_zd (m + n) = pell_zd m * pell_zd n
| 0 := (mul_one _).symm
| (n+1) := by rw[← add_assoc, pell_zd_succ, pell_zd_succ, pell_zd_add n, ← mul_assoc]

theorem xn_add (m n) : xn (m + n) = xn m * xn n + d * yn m * yn n :=
by injection (pell_zd_add _ m n) with h _;
 repeat {rw ← int.coe_nat_add at h <|> rw ← int.coe_nat_mul at h};
 exact int.coe_nat_inj h

theorem yn_add (m n) : yn (m + n) = xn m * yn n + yn m * xn n :=
by injection (pell_zd_add _ m n) with _ h;
 repeat {rw ← int.coe_nat_add at h <|> rw ← int.coe_nat_mul at h};
 exact int.coe_nat_inj h

theorem pell_zd_sub {m n} (h : n ≤ m) : pell_zd (m - n) = pell_zd m * star (pell_zd n) :=
let t := pell_zd_add n (m - n) in
by rw [add_tsub_cancel_of_le h] at t;
 rw [t]; rw [ mul_comm (pell_zd _ n) _]; rw [ mul_assoc]; rw [ is_pell_norm.1 (is_pell_pell_zd _ _)]; rw [ mul_one]

theorem xz_sub {m n} (h : n ≤ m) : xz (m - n) = xz m * xz n - d * yz m * yz n :=
by { rw [sub_eq_add_neg]; rw [ ←mul_neg], exact congr_arg zsqrtd.re (pell_zd_sub a1 h) }

theorem yz_sub {m n} (h : n ≤ m) : yz (m - n) = xz n * yz m - xz m * yz n :=
by { rw [sub_eq_add_neg]; rw [ ←mul_neg]; rw [ mul_comm]; rw [ add_comm],
 exact congr_arg zsqrtd.im (pell_zd_sub a1 h) }

theorem xy_coprime (n) : (xn n).coprime (yn n) :=
nat.coprime_of_dvd' $ λk kp kx ky,
let p := pell_eq n in by rw ← p; exact
nat.dvd_sub (le_of_lt $ nat.lt_of_sub_eq_succ p)
 (kx.mul_left _) (ky.mul_left _)

theorem strict_mono_y : strict_mono yn
| m 0 h := absurd h $ nat.not_lt_zero _
| m (n+1) h :=
 have yn m ≤ yn n, from or.elim (lt_or_eq_of_le $ nat.le_of_succ_le_succ h)
 (λhl, le_of_lt $ strict_mono_y hl) (λe, by rw e),
 by simp; refine lt_of_le_of_lt _ (nat.lt_add_of_pos_left $ x_pos a1 n);
 rw ← mul_one (yn a1 m);
 exact mul_le_mul this (le_of_lt a1) (nat.zero_le _) (nat.zero_le _)

theorem strict_mono_x : strict_mono xn
| m 0 h := absurd h $ nat.not_lt_zero _
| m (n+1) h :=
 have xn m ≤ xn n, from or.elim (lt_or_eq_of_le $ nat.le_of_succ_le_succ h)
 (λhl, le_of_lt $ strict_mono_x hl) (λe, by rw e),
 by simp; refine lt_of_lt_of_le (lt_of_le_of_lt this _) (nat.le_add_right _ _);
 have t := nat.mul_lt_mul_of_pos_left a1 (x_pos a1 n); rwa mul_one at t

theorem yn_ge_n : Π n, n ≤ yn n
| 0 := nat.zero_le _
| (n+1) := show n < yn (n+1), from lt_of_le_of_lt (yn_ge_n n) (strict_mono_y $ nat.lt_succ_self n)

theorem y_mul_dvd (n) : ∀k, yn n ∣ yn (n * k)
| 0 := dvd_zero _
| (k+1) := by rw [nat.mul_succ]; rw [ yn_add]; exact
 dvd_add (dvd_mul_left _ _) ((y_mul_dvd k).mul_right _)

theorem y_dvd_iff (m n) : yn m ∣ yn n ↔ m ∣ n :=
⟨λh, nat.dvd_of_mod_eq_zero $ (nat.eq_zero_or_pos _).resolve_right $ λhp,
 have co : nat.coprime (yn m) (xn (m * (n / m))), from nat.coprime.symm $
 (xy_coprime _).coprime_dvd_right (y_mul_dvd m (n / m)),
 have m0 : 0 < m, from m.eq_zero_or_pos.resolve_left $
 λe, by rw [e] at hp; rw [ nat.mod_zero] at hp; rw [e] at h; exact
 ne_of_lt (strict_mono_y a1 hp) (eq_zero_of_zero_dvd h).symm,
 by rw [← nat.mod_add_div n m] at h; rw [ yn_add] at h; exact
 not_le_of_gt (strict_mono_y _ $ nat.mod_lt n m0)
 (nat.le_of_dvd (strict_mono_y _ hp) $ co.dvd_of_dvd_mul_right $
 (nat.dvd_add_iff_right $ (y_mul_dvd _ _ _).mul_left _).2 h),
λ⟨k, e⟩, by rw e; apply y_mul_dvd⟩

theorem xy_modeq_yn (n) :
 ∀ k, xn (n * k) ≡ (xn n)^k [MOD (yn n)^2]
 ∧ yn (n * k) ≡ k * (xn n)^(k-1) * yn n [MOD (yn n)^3]
| 0 := by constructor; simp
| (k+1) :=
 let ⟨hx, hy⟩ := xy_modeq_yn k in
 have L : xn (n * k) * xn n + d * yn (n * k) * yn n ≡ xn n^k * xn n + 0 [MOD yn n^2], from
 (hx.mul_right _ ).add $ modeq_zero_iff_dvd.2 $
 by rw pow_succ'; exact
 mul_dvd_mul_right (dvd_mul_of_dvd_right (modeq_zero_iff_dvd.1 $
 (hy.of_dvd $ by simp [pow_succ']).trans $ modeq_zero_iff_dvd.2 $
 by simp [-mul_comm, -mul_assoc]) _) _,
 have R : xn (n * k) * yn n + yn (n * k) * xn n ≡
 xn n^k * yn n + k * xn n^k * yn n [MOD yn n^3], from
 modeq.add (by { rw pow_succ', exact hx.mul_right' _ }) $
 have k * xn n^(k - 1) * yn n * xn n = k * xn n^k * yn n,
 by clear _let_match; cases k with k; simp [pow_succ', mul_comm, mul_left_comm],
 by { rw ← this, exact hy.mul_right _ },
 by { rw [add_tsub_cancel_right]; rw [ nat.mul_succ]; rw [ xn_add]; rw [ yn_add]; rw [ pow_succ' (xn _ n)]; rw [ nat.succ_mul]; rw [ add_comm (k * xn _ n^k) (xn _ n^k)]; rw [ right_distrib],
 exact ⟨L, R⟩ }

theorem ysq_dvd_yy (n) : yn n * yn n ∣ yn (n * yn n) :=
modeq_zero_iff_dvd.1 $
 ((xy_modeq_yn n (yn n)).right.of_dvd $ by simp [pow_succ]).trans
 (modeq_zero_iff_dvd.2 $ by simp [mul_dvd_mul_left, mul_assoc])

theorem dvd_of_ysq_dvd {n t} (h : yn n * yn n ∣ yn t) : yn n ∣ t :=
have nt : n ∣ t, from (y_dvd_iff n t).1 $ dvd_of_mul_left_dvd h,
n.eq_zero_or_pos.elim (λ n0, by rwa n0 at ⊢ nt) $ λ (n0l : 0 < n),
let ⟨k, ke⟩ := nt in
have yn n ∣ k * (xn n)^(k-1), from
nat.dvd_of_mul_dvd_mul_right (strict_mono_y n0l) $ modeq_zero_iff_dvd.1 $
 by have xm := (xy_modeq_yn a1 n k).right; rw ← ke at xm; exact
 (xm.of_dvd $ by simp [pow_succ]).symm.trans h.modeq_zero_nat,
by rw ke; exact dvd_mul_of_dvd_right
 (((xy_coprime _ _).pow_left _).symm.dvd_of_dvd_mul_right this) _

theorem pell_zd_succ_succ (n) : pell_zd (n + 2) + pell_zd n = (2 * a : ℕ) * pell_zd (n + 1) :=
have (1:ℤ√d) + ⟨a, 1⟩ * ⟨a, 1⟩ = ⟨a, 1⟩ * (2 * a),
by { rw zsqrtd.coe_nat_val, change (⟨_,_⟩:ℤ√(d a1))=⟨_,_⟩,
 rw dz_val, dsimp [az], rw zsqrtd.ext, dsimp, split; ring },
by simpa [mul_add, mul_comm, mul_left_comm, add_comm] using congr_arg (* pell_zd a1 n) this

theorem xy_succ_succ (n) : xn (n + 2) + xn n = (2 * a) * xn (n + 1) ∧
 yn (n + 2) + yn n = (2 * a) * yn (n + 1) := begin
 have := pell_zd_succ_succ a1 n, unfold pell_zd at this,
 erw [zsqrtd.smul_val (2 * a : ℕ)] at this,
 injection this with h₁ h₂,
 split; apply int.coe_nat_inj; [simpa using h₁, simpa using h₂]
end

theorem xn_succ_succ (n) : xn (n + 2) + xn n = (2 * a) * xn (n + 1) := (xy_succ_succ n).1
theorem yn_succ_succ (n) : yn (n + 2) + yn n = (2 * a) * yn (n + 1) := (xy_succ_succ n).2

theorem xz_succ_succ (n) : xz (n + 2) = (2 * a : ℕ) * xz (n + 1) - xz n :=
eq_sub_of_add_eq $ by delta xz; rw [← int.coe_nat_add]; rw [ ← int.coe_nat_mul]; rw [ xn_succ_succ]

theorem yz_succ_succ (n) : yz (n + 2) = (2 * a : ℕ) * yz (n + 1) - yz n :=
eq_sub_of_add_eq $ by delta yz; rw [← int.coe_nat_add]; rw [ ← int.coe_nat_mul]; rw [ yn_succ_succ]

theorem yn_modeq_a_sub_one : ∀ n, yn n ≡ n [MOD a-1]
| 0 := by simp
| 1 := by simp
| (n+2) := (yn_modeq_a_sub_one n).add_right_cancel $
 begin
 rw [yn_succ_succ]; rw [ (by ring : n + 2 + n = 2 * (n + 1))],
 exact ((modeq_sub a1.le).mul_left 2).mul (yn_modeq_a_sub_one (n+1)),
 end

theorem yn_modeq_two : ∀ n, yn n ≡ n [MOD 2]
| 0 := by simp
| 1 := by simp
| (n+2) := (yn_modeq_two n).add_right_cancel $
 begin
 rw [yn_succ_succ]; rw [ mul_assoc]; rw [ (by ring : n + 2 + n = 2 * (n + 1))],
 exact (dvd_mul_right 2 _).modeq_zero_nat.trans (dvd_mul_right 2 _).zero_modeq_nat,
 end

section

omit a1
lemma x_sub_y_dvd_pow_lem (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : ℤ) :
 (a2 * yn1 - yn0) * ay + y2 - (a2 * xn1 - xn0) =
 y2 - a2 * y1 + y0 + a2 * (yn1 * ay + y1 - xn1) - (yn0 * ay + y0 - xn0) := by ring

end

theorem x_sub_y_dvd_pow (y : ℕ) :
 ∀ n, (2*a*y - y*y - 1 : ℤ) ∣ yz n * (a - y) + ↑(y^n) - xz n
| 0 := by simp [xz, yz, int.coe_nat_zero, int.coe_nat_one]
| 1 := by simp [xz, yz, int.coe_nat_zero, int.coe_nat_one]
| (n+2) :=
 have (2*a*y - y*y - 1 : ℤ) ∣ ↑(y^(n + 2)) - ↑(2 * a) * ↑(y^(n + 1)) + ↑(y^n), from
 ⟨-↑(y^n), by { simp [pow_succ, mul_add, int.coe_nat_mul,
 show ((2:ℕ):ℤ) = 2, from rfl, mul_comm, mul_left_comm], ring }⟩,
 by { rw [xz_succ_succ]; rw [ yz_succ_succ]; rw [ x_sub_y_dvd_pow_lem ↑(y^(n+2)) ↑(y^(n+1)) ↑(y^n)],
 exact
 dvd_sub (dvd_add this $ (x_sub_y_dvd_pow (n+1)).mul_left _) (x_sub_y_dvd_pow n) }

theorem xn_modeq_x2n_add_lem (n j) : xn n ∣ d * yn n * (yn n * xn j) + xn j :=
have h1 : d * yn n * (yn n * xn j) + xn j = (d * yn n * yn n + 1) * xn j,
 by simp [add_mul, mul_assoc],
have h2 : d * yn n * yn n + 1 = xn n * xn n, by apply int.coe_nat_inj;
 repeat {rw int.coe_nat_add <|> rw int.coe_nat_mul}; exact
 add_eq_of_eq_sub' (eq.symm $ pell_eqz _ _),
by rw h2 at h1; rw [h1]; rw [ mul_assoc]; exact dvd_mul_right _ _

theorem xn_modeq_x2n_add (n j) : xn (2 * n + j) + xn j ≡ 0 [MOD xn n] :=
begin
 rw [two_mul]; rw [ add_assoc]; rw [ xn_add]; rw [ add_assoc]; rw [ ←zero_add 0],
 refine (dvd_mul_right (xn a1 n) (xn a1 (n + j))).modeq_zero_nat.add _,
 rw [yn_add]; rw [ left_distrib]; rw [ add_assoc]; rw [ ←zero_add 0],
 exact ((dvd_mul_right _ _).mul_left _).modeq_zero_nat.add
 (xn_modeq_x2n_add_lem _ _ _).modeq_zero_nat,
end

lemma xn_modeq_x2n_sub_lem {n j} (h : j ≤ n) : xn (2 * n - j) + xn j ≡ 0 [MOD xn n] :=
have h1 : xz n ∣ ↑d * yz n * yz (n - j) + xz j,
 by rw [yz_sub _ h]; rw [ mul_sub_left_distrib]; rw [ sub_add_eq_add_sub]; exact
dvd_sub
 (by delta xz; delta yz;
 repeat {rw ← int.coe_nat_add <|> rw ← int.coe_nat_mul}; rw mul_comm (xn a1 j) (yn a1 n);
 exact int.coe_nat_dvd.2 (xn_modeq_x2n_add_lem _ _ _))
 ((dvd_mul_right _ _).mul_left _),
begin
 rw [two_mul]; rw [ add_tsub_assoc_of_le h]; rw [ xn_add]; rw [ add_assoc]; rw [ ←zero_add 0],
 exact (dvd_mul_right _ _).modeq_zero_nat.add
 (int.coe_nat_dvd.1 $ by simpa [xz, yz] using h1).modeq_zero_nat,
end

theorem xn_modeq_x2n_sub {n j} (h : j ≤ 2 * n) : xn (2 * n - j) + xn j ≡ 0 [MOD xn n] :=
(le_total j n).elim xn_modeq_x2n_sub_lem
 (λjn, have 2 * n - j + j ≤ n + j, by rw [tsub_add_cancel_of_le h]; rw [ two_mul];
 exact nat.add_le_add_left jn _,
 let t := xn_modeq_x2n_sub_lem (nat.le_of_add_le_add_right this) in
 by rwa [tsub_tsub_cancel_of_le h] at t); rwa [ add_comm] at t)

theorem xn_modeq_x4n_add (n j) : xn (4 * n + j) ≡ xn j [MOD xn n] :=
modeq.add_right_cancel' (xn (2 * n + j)) $
by refine @modeq.trans _ _ 0 _ _ (by rw add_comm; exact (xn_modeq_x2n_add _ _ _).symm);
 rw [show 4*n = 2*n + 2*n]; rw [ from right_distrib 2 2 n]; rw [ add_assoc]; apply xn_modeq_x2n_add

theorem xn_modeq_x4n_sub {n j} (h : j ≤ 2 * n) : xn (4 * n - j) ≡ xn j [MOD xn n] :=
have h' : j ≤ 2*n, from le_trans h (by rw nat.succ_mul; apply nat.le_add_left),
modeq.add_right_cancel' (xn (2 * n - j)) $
by refine @modeq.trans _ _ 0 _ _ (by rw add_comm; exact (xn_modeq_x2n_sub _ h).symm);
 rw [show 4*n = 2*n + 2*n]; rw [ from right_distrib 2 2 n]; rw [ add_tsub_assoc_of_le h'];
 apply xn_modeq_x2n_add

theorem eq_of_xn_modeq_lem1 {i n} : Π {j}, i < j → j < n → xn i % xn n < xn j % xn n
| 0 ij _ := absurd ij (nat.not_lt_zero _)
| (j+1) ij jn :=
 suffices xn j % xn n < xn (j + 1) % xn n, from
 (lt_or_eq_of_le (nat.le_of_succ_le_succ ij)).elim
 (λh, lt_trans (eq_of_xn_modeq_lem1 h (le_of_lt jn)) this)
 (λh, by rw h; exact this),
 by rw [nat.mod_eq_of_lt (strict_mono_x _ (nat.lt_of_succ_lt jn))]; rw [ nat.mod_eq_of_lt (strict_mono_x _ jn)];
 exact strict_mono_x _ (nat.lt_succ_self _)

theorem eq_of_xn_modeq_lem2 {n} (h : 2 * xn n = xn (n + 1)) : a = 2 ∧ n = 0 :=
by rw [xn_succ] at h; rw [ mul_comm] at h; exact
have n = 0, from n.eq_zero_or_pos.resolve_right $ λnp,
 ne_of_lt (lt_of_le_of_lt (nat.mul_le_mul_left _ a1)
 (nat.lt_add_of_pos_right $ mul_pos (d_pos a1) (strict_mono_y a1 np))) h,
by cases this; simp at h; exact ⟨h.symm, rfl⟩

theorem eq_of_xn_modeq_lem3 {i n} (npos : 0 < n) :
 Π {j}, i < j → j ≤ 2 * n → j ≠ n → ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2) → xn i % xn n < xn j % xn n
| 0 ij _ _ _ := absurd ij (nat.not_lt_zero _)
| (j+1) ij j2n jnn ntriv :=
 have lem2 : ∀k > n, k ≤ 2*n → (↑(xn k % xn n) : ℤ) = xn n - xn (2 * n - k), from λk kn k2n,
 let k2nl := lt_of_add_lt_add_right $ show 2*n-k+k < n+k, by
 {rw tsub_add_cancel_of_le, rw two_mul; exact (add_lt_add_left kn n), exact k2n } in
 have xle : xn (2 * n - k) ≤ xn n, from le_of_lt $ strict_mono_x k2nl,
 suffices xn k % xn n = xn n - xn (2 * n - k), by rw [this]; rw [ int.coe_nat_sub xle],
 by
 { rw ← nat.mod_eq_of_lt (nat.sub_lt (x_pos a1 n) (x_pos a1 (2 * n - k))),
 apply modeq.add_right_cancel' (xn a1 (2 * n - k)),
 rw [tsub_add_cancel_of_le xle],
 have t := xn_modeq_x2n_sub_lem a1 k2nl.le,
 rw tsub_tsub_cancel_of_le k2n at t,
 exact t.trans dvd_rfl.zero_modeq_nat },
 (lt_trichotomy j n).elim
 (λ (jn : j < n), eq_of_xn_modeq_lem1 ij (lt_of_le_of_ne jn jnn)) $ λ o, o.elim
 (λ (jn : j = n), by
 { cases jn,
 apply int.lt_of_coe_nat_lt_coe_nat,
 rw [lem2 (n+1) (nat.lt_succ_self _) j2n]; rw [ show 2 * n - (n + 1) = n - 1]; rw [ by rw[two_mul]; rw [ tsub_add_eq_tsub_tsub]; rw [ add_tsub_cancel_right]],
 refine lt_sub_left_of_add_lt (int.coe_nat_lt_coe_nat_of_lt _),
 cases (lt_or_eq_of_le $ nat.le_of_succ_le_succ ij) with lin ein,
 { rw nat.mod_eq_of_lt (strict_mono_x _ lin),
 have ll : xn a1 (n-1) + xn a1 (n-1) ≤ xn a1 n,
 { rw [← two_mul]; rw [ mul_comm]; rw [ show xn a1 n = xn a1 (n-1+1)]; rw [ by rw [tsub_add_cancel_of_le (succ_le_of_lt npos)], xn_succ],
 exact le_trans (nat.mul_le_mul_left _ a1) (nat.le_add_right _ _) },
 have npm : (n-1).succ = n := nat.succ_pred_eq_of_pos npos,
 have il : i ≤ n - 1, { apply nat.le_of_succ_le_succ, rw npm, exact lin },
 cases lt_or_eq_of_le il with ill ile,
 { exact lt_of_lt_of_le (nat.add_lt_add_left (strict_mono_x a1 ill) _) ll },
 { rw ile,
 apply lt_of_le_of_ne ll,
 rw ← two_mul,
 exact λe, ntriv $
 let ⟨a2, s1⟩ := @eq_of_xn_modeq_lem2 _ a1 (n-1)
 (by rwa [tsub_add_cancel_of_le (succ_le_of_lt npos)]) in
 have n1 : n = 1, from le_antisymm (tsub_eq_zero_iff_le.mp s1) npos,
 by rw [ile]; rw [ a2]; rw [ n1]; exact ⟨rfl, rfl, rfl, rfl⟩ } },
 { rw [ein]; rw [ nat.mod_self]; rw [ add_zero],
 exact strict_mono_x _ (nat.pred_lt npos.ne') } })
 (λ (jn : j > n),
 have lem1 : j ≠ n → xn j % xn n < xn (j + 1) % xn n → xn i % xn n < xn (j + 1) % xn n,
 from λjn s,
 (lt_or_eq_of_le (nat.le_of_succ_le_succ ij)).elim
 (λh, lt_trans (eq_of_xn_modeq_lem3 h (le_of_lt j2n) jn $ λ⟨a1, n1, i0, j2⟩,
 by rw [n1] at j2n; rw [ j2] at j2n; exact absurd j2n dec_trivial) s)
 (λh, by rw h; exact s),
 lem1 (ne_of_gt jn) $ int.lt_of_coe_nat_lt_coe_nat $ by
 { rw [lem2 j jn (le_of_lt j2n)]; rw [ lem2 (j+1) (nat.le_succ_of_le jn) j2n],
 refine sub_lt_sub_left (int.coe_nat_lt_coe_nat_of_lt $ strict_mono_x _ _) _,
 rw [nat.sub_succ],
 exact nat.pred_lt (ne_of_gt $ tsub_pos_of_lt j2n) })

theorem eq_of_xn_modeq_le {i j n} (ij : i ≤ j) (j2n : j ≤ 2 * n)
 (h : xn i ≡ xn j [MOD xn n]) (ntriv : ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2)) : i = j :=
if npos : n = 0 then by simp [*] at * else
(lt_or_eq_of_le ij).resolve_left $ λij',
if jn : j = n then by
{ refine ne_of_gt _ h,
 rw [jn]; rw [ nat.mod_self],
 have x0 : 0 < xn a1 0 % xn a1 n :=
 by rw [nat.mod_eq_of_lt (strict_mono_x a1 (nat.pos_of_ne_zero npos))]; exact dec_trivial,
 cases i with i, exact x0,
 rw jn at ij',
 exact x0.trans (eq_of_xn_modeq_lem3 _ (nat.pos_of_ne_zero npos) (nat.succ_pos _)
 (le_trans ij j2n) (ne_of_lt ij') $
 λ⟨a1, n1, _, i2⟩, by rw [n1] at ij'; rw [ i2] at ij'; exact absurd ij' dec_trivial) }
else ne_of_lt (eq_of_xn_modeq_lem3 (nat.pos_of_ne_zero npos) ij' j2n jn ntriv) h

theorem eq_of_xn_modeq {i j n} (i2n : i ≤ 2 * n) (j2n : j ≤ 2 * n)
 (h : xn i ≡ xn j [MOD xn n]) (ntriv : a = 2 → n = 1 → (i = 0 → j ≠ 2) ∧ (i = 2 → j ≠ 0)) :
 i = j :=
(le_total i j).elim
 (λij, eq_of_xn_modeq_le ij j2n h $ λ⟨a2, n1, i0, j2⟩, (ntriv a2 n1).left i0 j2)
 (λij, (eq_of_xn_modeq_le ij i2n h.symm $ λ⟨a2, n1, j0, i2⟩,
 (ntriv a2 n1).right i2 j0).symm)

theorem eq_of_xn_modeq' {i j n} (ipos : 0 < i) (hin : i ≤ n) (j4n : j ≤ 4 * n)
 (h : xn j ≡ xn i [MOD xn n]) : j = i ∨ j + i = 4 * n :=
have i2n : i ≤ 2*n, by apply le_trans hin; rw two_mul; apply nat.le_add_left,
(le_or_gt j (2 * n)).imp
 (λj2n : j ≤ 2 * n, eq_of_xn_modeq j2n i2n h $
 λa2 n1, ⟨λj0 i2, by rw [n1] at hin; rw [ i2] at hin; exact absurd hin dec_trivial,
 λj2 i0, ne_of_gt ipos i0⟩)
 (λj2n : 2 * n < j, suffices i = 4*n - j, by rw [this]; rw [ add_tsub_cancel_of_le j4n],
 have j42n : 4*n - j ≤ 2*n, from @nat.le_of_add_le_add_right j _ _ $
 by rw [tsub_add_cancel_of_le j4n]; rw [ show 4*n = 2*n + 2*n]; rw [ from right_distrib 2 2 n];
 exact nat.add_le_add_left (le_of_lt j2n) _,
 eq_of_xn_modeq i2n j42n
 (h.symm.trans $ let t := xn_modeq_x4n_sub j42n in by rwa [tsub_tsub_cancel_of_le j4n] at t)
 (λa2 n1, ⟨λi0, absurd i0 (ne_of_gt ipos), λi2, by { rw [n1] at hin; rw [ i2] at hin,
 exact absurd hin dec_trivial }⟩))

theorem modeq_of_xn_modeq {i j n} (ipos : 0 < i) (hin : i ≤ n) (h : xn j ≡ xn i [MOD xn n]) :
 j ≡ i [MOD 4 * n] ∨ j + i ≡ 0 [MOD 4 * n] :=
let j' := j % (4 * n) in
have n4 : 0 < 4 * n, from mul_pos dec_trivial (ipos.trans_le hin),
have jl : j' < 4 * n, from nat.mod_lt _ n4,
have jj : j ≡ j' [MOD 4 * n], by delta modeq; rw nat.mod_eq_of_lt jl,
have ∀j q, xn (j + 4 * n * q) ≡ xn j [MOD xn n], begin
 intros j q, induction q with q IH, { simp },
 rw [nat.mul_succ]; rw [ ← add_assoc]; rw [ add_comm],
 exact (xn_modeq_x4n_add _ _ _).trans IH
end,
or.imp
 (λ(ji : j' = i), by rwa ← ji)
 (λ(ji : j' + i = 4 * n), (jj.add_right _).trans $
 by { rw ji, exact dvd_rfl.modeq_zero_nat })
 (eq_of_xn_modeq' ipos hin jl.le $
 (h.symm.trans $ by { rw ← nat.mod_add_div j (4*n), exact this j' _ }).symm)
end

theorem xy_modeq_of_modeq {a b c} (a1 : 1 < a) (b1 : 1 < b) (h : a ≡ b [MOD c]) :
 ∀ n, xn a1 n ≡ xn b1 n [MOD c] ∧ yn a1 n ≡ yn b1 n [MOD c]
| 0 := by constructor; refl
| 1 := by simp; exact ⟨h, modeq.refl 1⟩
| (n+2) := ⟨
 (xy_modeq_of_modeq n).left.add_right_cancel $
 by { rw [xn_succ_succ a1]; rw [ xn_succ_succ b1], exact
 (h.mul_left _ ).mul (xy_modeq_of_modeq (n+1)).left },
 (xy_modeq_of_modeq n).right.add_right_cancel $
 by { rw [yn_succ_succ a1]; rw [ yn_succ_succ b1], exact
 (h.mul_left _ ).mul (xy_modeq_of_modeq (n+1)).right }⟩

theorem matiyasevic {a k x y} : (∃ a1 : 1 < a, xn a1 k = x ∧ yn a1 k = y) ↔
1 < a ∧ k ≤ y ∧
(x = 1 ∧ y = 0 ∨
∃ (u v s t b : ℕ),
 x * x - (a * a - 1) * y * y = 1 ∧
 u * u - (a * a - 1) * v * v = 1 ∧
 s * s - (b * b - 1) * t * t = 1 ∧
 1 < b ∧ b ≡ 1 [MOD 4 * y] ∧ b ≡ a [MOD u] ∧
 0 < v ∧ y * y ∣ v ∧
 s ≡ x [MOD u] ∧
 t ≡ k [MOD 4 * y]) :=
⟨λ⟨a1, hx, hy⟩, by rw [← hx]; rw [ ← hy];
 refine ⟨a1, (nat.eq_zero_or_pos k).elim
 (λk0, by rw k0; exact ⟨le_rfl, or.inl ⟨rfl, rfl⟩⟩) (λkpos, _)⟩; exact
 let x := xn a1 k, y := yn a1 k,
 m := 2 * (k * y),
 u := xn a1 m, v := yn a1 m in
 have ky : k ≤ y, from yn_ge_n a1 k,
 have yv : y * y ∣ v, from (ysq_dvd_yy a1 k).trans $ (y_dvd_iff _ _ _).2 $ dvd_mul_left _ _,
 have uco : nat.coprime u (4 * y), from
 have 2 ∣ v, from modeq_zero_iff_dvd.1 $ (yn_modeq_two _ _).trans
 (dvd_mul_right _ _).modeq_zero_nat,
 have nat.coprime u 2, from
 (xy_coprime a1 m).coprime_dvd_right this,
 (this.mul_right this).mul_right $
 (xy_coprime _ _).coprime_dvd_right (dvd_of_mul_left_dvd yv),
 let ⟨b, ba, bm1⟩ := chinese_remainder uco a 1 in
 have m1 : 1 < m, from
 have 0 < k * y, from mul_pos kpos (strict_mono_y a1 kpos),
 nat.mul_le_mul_left 2 this,
 have vp : 0 < v, from strict_mono_y a1 (lt_trans zero_lt_one m1),
 have b1 : 1 < b, from
 have xn a1 1 < u, from strict_mono_x a1 m1,
 have a < u, by simp at this; exact this,
 lt_of_lt_of_le a1 $ by delta modeq at ba;
 rw nat.mod_eq_of_lt this at ba; rw ← ba; apply nat.mod_le,
 let s := xn b1 k, t := yn b1 k in
 have sx : s ≡ x [MOD u], from (xy_modeq_of_modeq b1 a1 ba k).left,
 have tk : t ≡ k [MOD 4 * y], from
 have 4 * y ∣ b - 1, from int.coe_nat_dvd.1 $
 by rw int.coe_nat_sub (le_of_lt b1);
 exact bm1.symm.dvd,
 (yn_modeq_a_sub_one _ _).of_dvd this,
 ⟨ky, or.inr ⟨u, v, s, t, b,
 pell_eq _ _, pell_eq _ _, pell_eq _ _, b1, bm1, ba, vp, yv, sx, tk⟩⟩,
λ⟨a1, ky, o⟩, ⟨a1, match o with
| or.inl ⟨x1, y0⟩ := by rw y0 at ky; rw [nat.eq_zero_of_le_zero ky]; rw [ x1]; rw [ y0]; exact ⟨rfl, rfl⟩
| or.inr ⟨u, v, s, t, b, xy, uv, st, b1, rem⟩ :=
 match x, y, eq_pell a1 xy, u, v, eq_pell a1 uv, s, t, eq_pell b1 st, rem, ky with
 | ._, ._, ⟨i, rfl, rfl⟩, ._, ._, ⟨n, rfl, rfl⟩, ._, ._, ⟨j, rfl, rfl⟩,
 ⟨(bm1 : b ≡ 1 [MOD 4 * yn a1 i]),
 (ba : b ≡ a [MOD xn a1 n]),
 (vp : 0 < yn a1 n),
 (yv : yn a1 i * yn a1 i ∣ yn a1 n),
 (sx : xn b1 j ≡ xn a1 i [MOD xn a1 n]),
 (tk : yn b1 j ≡ k [MOD 4 * yn a1 i])⟩,
 (ky : k ≤ yn a1 i) :=
 (nat.eq_zero_or_pos i).elim
 (λi0, by simp [i0] at ky; rw [i0]; rw [ ky]; exact ⟨rfl, rfl⟩) $ λipos,
 suffices i = k, by rw this; exact ⟨rfl, rfl⟩,
 by clear _x o rem xy uv st _match _match _fun_match; exact
 have iln : i ≤ n, from le_of_not_gt $ λhin,
 not_lt_of_ge (nat.le_of_dvd vp (dvd_of_mul_left_dvd yv)) (strict_mono_y a1 hin),
 have yd : 4 * yn a1 i ∣ 4 * n, from mul_dvd_mul_left _ $ dvd_of_ysq_dvd a1 yv,
 have jk : j ≡ k [MOD 4 * yn a1 i], from
 have 4 * yn a1 i ∣ b - 1, from int.coe_nat_dvd.1 $
 by rw int.coe_nat_sub (le_of_lt b1); exact bm1.symm.dvd,
 ((yn_modeq_a_sub_one b1 _).of_dvd this).symm.trans tk,
 have ki : k + i < 4 * yn a1 i, from
 lt_of_le_of_lt (add_le_add ky (yn_ge_n a1 i)) $
 by rw ← two_mul; exact nat.mul_lt_mul_of_pos_right dec_trivial (strict_mono_y a1 ipos),
 have ji : j ≡ i [MOD 4 * n], from
 have xn a1 j ≡ xn a1 i [MOD xn a1 n], from (xy_modeq_of_modeq b1 a1 ba j).left.symm.trans sx,
 (modeq_of_xn_modeq a1 ipos iln this).resolve_right $ λ (ji : j + i ≡ 0 [MOD 4 * n]),
 not_le_of_gt ki $ nat.le_of_dvd (lt_of_lt_of_le ipos $ nat.le_add_left _ _) $
 modeq_zero_iff_dvd.1 $ (jk.symm.add_right i).trans $
 ji.of_dvd yd,
 by have : i % (4 * yn a1 i) = k % (4 * yn a1 i) :=
 (ji.of_dvd yd).symm.trans jk;
 rwa [nat.mod_eq_of_lt (lt_of_le_of_lt (nat.le_add_left _ _) ki)] at this; rwa [ nat.mod_eq_of_lt (lt_of_le_of_lt (nat.le_add_right _ _) ki)] at this
 end
end⟩⟩

lemma eq_pow_of_pell_lem {a y k} (hy0 : y ≠ 0) (hk0 : k ≠ 0) (hyk : y^k < a) :
 (↑(y^k) : ℤ) < 2*a*y - y*y - 1 :=
have hya : y < a, from (nat.le_self_pow hk0 _).trans_lt hyk,
calc (↑(y ^ k) : ℤ) < a : nat.cast_lt.2 hyk
... ≤ a ^ 2 - (a - 1) ^ 2 - 1 :
 begin
 rw [sub_sq]; rw [ mul_one]; rw [ one_pow]; rw [ sub_add]; rw [ sub_sub_cancel]; rw [ two_mul]; rw [ sub_sub]; rw [ ← add_sub]; rw [ le_add_iff_nonneg_right]; rw [ ← bit0]; rw [ sub_nonneg]; rw [ ← nat.cast_two]; rw [ nat.cast_le]; rw [ nat.succ_le_iff],
 exact (one_le_iff_ne_zero.2 hy0).trans_lt hya
 end
... ≤ a ^ 2 - (a - y) ^ 2 - 1 : have _ := hya.le,
 by { mono*; simpa only [sub_nonneg, nat.cast_le, nat.one_le_cast, nat.one_le_iff_ne_zero] }
... = 2*a*y - y*y - 1 : by ring

theorem eq_pow_of_pell {m n k} : n^k = m ↔
 k = 0 ∧ m = 1 ∨
 0 < k ∧ (n = 0 ∧ m = 0 ∨
 0 < n ∧ ∃ (w a t z : ℕ) (a1 : 1 < a),
 xn a1 k ≡ yn a1 k * (a - n) + m [MOD t] ∧
 2 * a * n = t + (n * n + 1) ∧
 m < t ∧ n ≤ w ∧ k ≤ w ∧
 a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1) :=
begin
 split,
 { rintro rfl,
 refine k.eq_zero_or_pos.imp (λ k0, k0.symm ▸ ⟨rfl, rfl⟩) (λ hk, ⟨hk, _⟩),
 refine n.eq_zero_or_pos.imp (λ n0, n0.symm ▸ ⟨rfl, zero_pow hk⟩) (λ hn, ⟨hn, _⟩),
 set w := max n k,
 have nw : n ≤ w, from le_max_left _ _,
 have kw : k ≤ w, from le_max_right _ _,
 have wpos : 0 < w, from hn.trans_le nw,
 have w1 : 1 < w + 1, from nat.succ_lt_succ wpos,
 set a := xn w1 w,
 have a1 : 1 < a, from strict_mono_x w1 wpos,
 have na : n ≤ a, from nw.trans (n_lt_xn w1 w).le,
 set x := xn a1 k, set y := yn a1 k,
 obtain ⟨z, ze⟩ : w ∣ yn w1 w,
 from modeq_zero_iff_dvd.1 ((yn_modeq_a_sub_one w1 w).trans dvd_rfl.modeq_zero_nat),
 have nt : (↑(n^k) : ℤ) < 2 * a * n - n * n - 1,
 { refine eq_pow_of_pell_lem hn.ne' hk.ne' _,
 calc n^k ≤ n^w : nat.pow_le_pow_of_le_right hn kw
 ... < (w + 1)^w : nat.pow_lt_pow_of_lt_left (nat.lt_succ_of_le nw) wpos
 ... ≤ a : xn_ge_a_pow w1 w },
 lift (2 * a * n - n * n - 1 : ℤ) to ℕ using ((nat.cast_nonneg _).trans nt.le) with t te,
 have tm : x ≡ y * (a - n) + n^k [MOD t],
 { apply modeq_of_dvd,
 rw [int.coe_nat_add]; rw [ int.coe_nat_mul]; rw [ int.coe_nat_sub na]; rw [ te],
 exact x_sub_y_dvd_pow a1 n k },
 have ta : 2 * a * n = t + (n * n + 1),
 { rw [← @nat.cast_inj ℤ]; rw [ int.coe_nat_add]; rw [ te]; rw [ sub_sub],
 repeat { rw nat.cast_add <|> rw nat.cast_mul },
 rw [nat.cast_one]; rw [ sub_add_cancel]; rw [ nat.cast_two] },
 have zp : a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1,
 from ze ▸ pell_eq w1 w,
 exact ⟨w, a, t, z, a1, tm, ta, nat.cast_lt.1 nt, nw, kw, zp⟩ },
 { rintro (⟨rfl, rfl⟩ | ⟨hk0, ⟨rfl, rfl⟩ | ⟨hn0, w, a, t, z, a1, tm, ta, mt, nw, kw, zp⟩⟩),
 { exact pow_zero n }, { exact zero_pow hk0 },
 have hw0 : 0 < w, from hn0.trans_le nw,
 have hw1 : 1 < w + 1, from nat.succ_lt_succ hw0,
 rcases eq_pell hw1 zp with ⟨j, rfl, yj⟩,
 have hj0 : 0 < j,
 { apply nat.pos_of_ne_zero,
 rintro rfl,
 exact lt_irrefl 1 a1 },
 have wj : w ≤ j := nat.le_of_dvd hj0 (modeq_zero_iff_dvd.1 $
 (yn_modeq_a_sub_one hw1 j).symm.trans $ modeq_zero_iff_dvd.2 ⟨z, yj.symm⟩),
 have hnka : n ^ k < xn hw1 j,
 calc n^k ≤ n^j : nat.pow_le_pow_of_le_right hn0 (le_trans kw wj)
 ... < (w + 1)^j : nat.pow_lt_pow_of_lt_left (nat.lt_succ_of_le nw) hj0
 ... ≤ xn hw1 j : xn_ge_a_pow hw1 j,
 have nt : (↑(n^k) : ℤ) < 2 * xn hw1 j * n - n * n - 1,
 from eq_pow_of_pell_lem hn0.ne' hk0.ne' hnka,
 have na : n ≤ xn hw1 j, from (nat.le_self_pow hk0.ne' _).trans hnka.le,
 have te : (t : ℤ) = 2 * xn hw1 j * n - n * n - 1,
 { rw [sub_sub]; rw [ eq_sub_iff_add_eq],
 exact_mod_cast ta.symm },
 have : xn a1 k ≡ yn a1 k * (xn hw1 j - n) + n^k [MOD t],
 { apply modeq_of_dvd,
 rw [te]; rw [ nat.cast_add]; rw [ nat.cast_mul]; rw [ int.coe_nat_sub na],
 exact x_sub_y_dvd_pow a1 n k },
 have : n^k % t = m % t, from (this.symm.trans tm).add_left_cancel' _,
 rw [← te] at nt,
 rwa [nat.mod_eq_of_lt (nat.cast_lt.1 nt)] at this ; rwa [ nat.mod_eq_of_lt mt] at this }
end

end pell

