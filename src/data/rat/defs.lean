/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.rat.init
import data.int.cast.defs
import data.int.dvd.basic
import algebra.ring.regular
import data.nat.gcd.basic
import data.pnat.defs

/-!
# Basics for the Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `data.rat.basic` once the
`field` class has been defined.

## Main Definitions

- `rat.mk n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notations

- `/.` is infix notation for `rat.mk`.

-/

namespace rat

/-- Embed an integer as a rational number. You should use the coercion `coe : ℤ → ℚ` instead. -/
def of_int (n : ℤ) : ℚ :=
⟨n, 1, nat.one_pos, nat.coprime_one_right _⟩

instance : has_int_cast ℚ := ⟨of_int⟩

@[simp] lemma of_int_eq_cast (n : ℤ) : of_int n = n := rfl
@[simp, norm_cast] lemma coe_int_num (n : ℤ) : (n : ℚ).num = n := rfl
@[simp, norm_cast] lemma coe_int_denom (n : ℤ) : (n : ℚ).denom = 1 := rfl

instance : has_zero ℚ := ⟨(0 : ℤ)⟩
instance : has_one ℚ := ⟨(1 : ℤ)⟩
instance : inhabited ℚ := ⟨0⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ+` (not necessarily coprime) -/
def mk_pnat (n : ℤ) : ℕ+ → ℚ | ⟨d, dpos⟩ :=
let n' := n.nat_abs, g := n'.gcd d in
⟨n / g, d / g, begin
 apply (nat.le_div_iff_mul_le (nat.gcd_pos_of_pos_right _ dpos)).2,
 rw one_mul, exact nat.le_of_dvd dpos (nat.gcd_dvd_right _ _)
end, begin
 have : int.nat_abs (n / ↑g) = n' / g,
 { cases int.nat_abs_eq n with e e; rw e, { refl },
 rw [int.neg_div_of_dvd]; rw [ int.nat_abs_neg], { refl },
 exact int.coe_nat_dvd.2 (nat.gcd_dvd_left _ _) },
 rw this,
 exact nat.coprime_div_gcd_div_gcd (nat.gcd_pos_of_pos_right _ dpos)
end⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ`. In the case `d = 0`, we
 define `n / 0 = 0` by convention. -/
def mk_nat (n : ℤ) (d : ℕ) : ℚ :=
if d0 : d = 0 then 0 else mk_pnat n ⟨d, nat.pos_of_ne_zero d0⟩

/-- Form the quotient `n / d` where `n d : ℤ`. -/
def mk : ℤ → ℤ → ℚ
| n (d : ℕ) := mk_nat n d
| n -[1+ d] := mk_pnat (-n) d.succ_pnat

localized "infix (name := rat.mk) ` /. `:70 := rat.mk" in rat

theorem mk_pnat_eq (n d h) : mk_pnat n ⟨d, h⟩ = n /. d :=
by change n /. d with dite _ _ _; simp [ne_of_gt h]

theorem mk_nat_eq (n d) : mk_nat n d = n /. d := rfl

@[simp] theorem mk_zero (n) : n /. 0 = 0 := rfl

@[simp] theorem zero_mk_pnat (n) : mk_pnat 0 n = 0 :=
begin
 cases n with n npos,
 simp only [mk_pnat, int.nat_abs_zero, nat.div_self npos, nat.gcd_zero_left, int.zero_div],
 refl
end

@[simp] theorem zero_mk_nat (n) : mk_nat 0 n = 0 :=
by by_cases n = 0; simp [*, mk_nat]

@[simp] theorem zero_mk (n) : 0 /. n = 0 :=
by cases n; simp [mk]

private lemma gcd_abs_dvd_left {a b} : (nat.gcd (int.nat_abs a) b : ℤ) ∣ a :=
int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $ nat.gcd_dvd_left (int.nat_abs a) b

@[simp] theorem mk_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 :=
begin
 refine ⟨λ h, _, by { rintro rfl, simp }⟩,
 have : ∀ {a b}, mk_pnat a b = 0 → a = 0,
 { rintro a ⟨b, h⟩ e,
 injection e with e,
 apply int.eq_mul_of_div_eq_right gcd_abs_dvd_left e },
 cases b with b; simp only [mk, mk_nat, int.of_nat_eq_coe, dite_eq_left_iff] at h,
 { simp only [mt (congr_arg int.of_nat) b0, not_false_iff, forall_true_left] at h,
 exact this h },
 { apply neg_injective, simp [this h] }
end

theorem mk_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
(mk_eq_zero b0).not

theorem mk_eq : ∀ {a b c d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0),
 a /. b = c /. d ↔ a * d = c * b :=
suffices ∀ a b c d hb hd, mk_pnat a ⟨b, hb⟩ = mk_pnat c ⟨d, hd⟩ ↔ a * d = c * b,
begin
 intros, cases b with b b; simp [mk, mk_nat, nat.succ_pnat],
 simp [mt (congr_arg int.of_nat) hb],
 all_goals
 { cases d with d d; simp [mk, mk_nat, nat.succ_pnat],
 simp [mt (congr_arg int.of_nat) hd],
 all_goals { rw this, try {refl} } },
 { change a * ↑(d.succ) = -c * ↑b ↔ a * -(d.succ) = c * b,
 constructor; intro h; apply neg_injective; simpa [left_distrib, neg_add_eq_iff_eq_add,
 eq_neg_iff_add_eq_zero, neg_eq_iff_add_eq_zero] using h },
 { change -a * ↑d = c * b.succ ↔ a * d = c * -b.succ,
 constructor; intro h; apply neg_injective; simpa [left_distrib, eq_comm] using h },
 { change -a * d.succ = -c * b.succ ↔ a * -d.succ = c * -b.succ,
 simp [left_distrib, sub_eq_add_neg], cc }
end,
begin
 intros, simp [mk_pnat], constructor; intro h,
 { cases h with ha hb,
 have ha,
 { have dv := @gcd_abs_dvd_left,
 have := int.eq_mul_of_div_eq_right dv ha,
 rw ← int.mul_div_assoc _ dv at this,
 exact int.eq_mul_of_div_eq_left (dv.mul_left _) this.symm },
 have hb,
 { have dv := λ {a b}, nat.gcd_dvd_right (int.nat_abs a) b,
 have := nat.eq_mul_of_div_eq_right dv hb,
 rw ← nat.mul_div_assoc _ dv at this,
 exact nat.eq_mul_of_div_eq_left (dv.mul_left _) this.symm },
 have m0 : (a.nat_abs.gcd b * c.nat_abs.gcd d : ℤ) ≠ 0,
 { refine int.coe_nat_ne_zero.2 (ne_of_gt _),
 apply mul_pos; apply nat.gcd_pos_of_pos_right; assumption },
 apply mul_right_cancel₀ m0,
 simpa [mul_comm, mul_left_comm] using
 congr (congr_arg (*) ha.symm) (congr_arg coe hb) },
 { suffices : ∀ a c, a * d = c * b →
 a / a.gcd b = c / c.gcd d ∧ b / a.gcd b = d / c.gcd d,
 { cases this a.nat_abs c.nat_abs
 (by simpa [int.nat_abs_mul] using congr_arg int.nat_abs h) with h₁ h₂,
 have hs := congr_arg int.sign h,
 simp [int.sign_eq_one_of_pos (int.coe_nat_lt.2 hb),
 int.sign_eq_one_of_pos (int.coe_nat_lt.2 hd)] at hs,
 conv in a { rw ← int.sign_mul_nat_abs a },
 conv in c { rw ← int.sign_mul_nat_abs c },
 rw [int.mul_div_assoc]; rw [ int.mul_div_assoc],
 exact ⟨congr (congr_arg (*) hs) (congr_arg coe h₁), h₂⟩,
 all_goals { exact int.coe_nat_dvd.2 (nat.gcd_dvd_left _ _) } },
 intros a c h,
 suffices bd : b / a.gcd b = d / c.gcd d,
 { refine ⟨mul_left_cancel₀ hb.ne' _, bd⟩,
 rw [← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _)]; rw [ mul_comm]; rw [ nat.mul_div_assoc _ (nat.gcd_dvd_right _ _)]; rw [ bd]; rw [ ← nat.mul_div_assoc _ (nat.gcd_dvd_right _ _)]; rw [ h]; rw [ mul_comm]; rw [ nat.mul_div_assoc _ (nat.gcd_dvd_left _ _)] },
 suffices : ∀ {a c : ℕ} (b>0) (d>0),
 a * d = c * b → b / a.gcd b ≤ d / c.gcd d,
 { exact le_antisymm (this _ hb _ hd h) (this _ hd _ hb h.symm) },
 intros a c b hb d hd h,
 have gb0 := nat.gcd_pos_of_pos_right a hb,
 have gd0 := nat.gcd_pos_of_pos_right c hd,
 apply nat.le_of_dvd,
 apply (nat.le_div_iff_mul_le gd0).2,
 simp, apply nat.le_of_dvd hd (nat.gcd_dvd_right _ _),
 apply (nat.coprime_div_gcd_div_gcd gb0).symm.dvd_of_dvd_mul_left,
 refine ⟨c / c.gcd d, _⟩,
 rw [← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _)]; rw [ ← nat.mul_div_assoc _ (nat.gcd_dvd_right _ _)],
 apply congr_arg (/ c.gcd d),
 rw [mul_comm]; rw [ ← nat.mul_div_assoc _ (nat.gcd_dvd_left _ _)]; rw [ mul_comm]; rw [ h]; rw [ nat.mul_div_assoc _ (nat.gcd_dvd_right _ _)]; rw [ mul_comm] }
end

@[simp] theorem div_mk_div_cancel_left {a b c : ℤ} (c0 : c ≠ 0) :
 (a * c) /. (b * c) = a /. b :=
begin
 by_cases b0 : b = 0, { subst b0, simp },
 apply (mk_eq (mul_ne_zero b0 c0) b0).2, simp [mul_comm, mul_assoc]
end

@[simp] theorem num_denom : ∀ {a : ℚ}, a.num /. a.denom = a
| ⟨n, d, h, (c:_=1)⟩ := show mk_nat n d = _,
 by simp [mk_nat, ne_of_gt h, mk_pnat, c]

theorem num_denom' {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d := num_denom.symm

lemma coe_int_eq_mk (z : ℤ) : (z : ℚ) = z /. 1 := num_denom'

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_eliminator] def {u} num_denom_cases_on {C : ℚ → Sort u}
 : ∀ (a : ℚ) (H : ∀ n d, 0 < d → (int.nat_abs n).coprime d → C (n /. d)), C a
| ⟨n, d, h, c⟩ H := by rw num_denom'; exact H n d h c

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `d ≠ 0`. -/
@[elab_as_eliminator] def {u} num_denom_cases_on' {C : ℚ → Sort u}
 (a : ℚ) (H : ∀ (n:ℤ) (d:ℕ), d ≠ 0 → C (n /. d)) : C a :=
num_denom_cases_on a $ λ n d h c, H n d h.ne'

/-- Addition of rational numbers. Use `(+)` instead. -/
protected def add : ℚ → ℚ → ℚ
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := mk_pnat (n₁ * d₂ + n₂ * d₁) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : has_add ℚ := ⟨rat.add⟩

theorem lift_binop_eq (f : ℚ → ℚ → ℚ) (f₁ : ℤ → ℤ → ℤ → ℤ → ℤ) (f₂ : ℤ → ℤ → ℤ → ℤ → ℤ)
 (fv : ∀ {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂},
 f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
 (f0 : ∀ {n₁ d₁ n₂ d₂} (d₁0 : d₁ ≠ 0) (d₂0 : d₂ ≠ 0), f₂ n₁ d₁ n₂ d₂ ≠ 0)
 (a b c d : ℤ) (b0 : b ≠ 0) (d0 : d ≠ 0)
 (H : ∀ {n₁ d₁ n₂ d₂} (h₁ : a * d₁ = n₁ * b) (h₂ : c * d₂ = n₂ * d),
 f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
 f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d :=
begin
 generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
 generalize hc : c /. d = x, cases x with n₂ d₂ h₂ c₂, rw num_denom' at hc,
 rw fv,
 have d₁0 := ne_of_gt (int.coe_nat_lt.2 h₁),
 have d₂0 := ne_of_gt (int.coe_nat_lt.2 h₂),
 exact (mk_eq (f0 d₁0 d₂0) (f0 b0 d0)).2 (H ((mk_eq b0 d₁0).1 ha) ((mk_eq d0 d₂0).1 hc))
end

@[simp] theorem add_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
 a /. b + c /. d = (a * d + c * b) /. (b * d) :=
begin
 apply lift_binop_eq rat.add; intros; try {assumption},
 { apply mk_pnat_eq },
 { apply mul_ne_zero d₁0 d₂0 },
 calc (n₁ * d₂ + n₂ * d₁) * (b * d) =
 (n₁ * b) * d₂ * d + (n₂ * d) * (d₁ * b) : by simp [mul_add, mul_comm, mul_left_comm]
 ... = (a * d₁) * d₂ * d + (c * d₂) * (d₁ * b) : by rw [h₁]; rw [ h₂]
 ... = (a * d + c * b) * (d₁ * d₂) : by simp [mul_add, mul_comm, mul_left_comm]
end

/-- Negation of rational numbers. Use `-r` instead. -/
protected def neg (r : ℚ) : ℚ :=
⟨-r.num, r.denom, r.pos, by simp [r.cop]⟩

instance : has_neg ℚ := ⟨rat.neg⟩

@[simp] theorem neg_def {a b : ℤ} : -(a /. b) = -a /. b :=
begin
 by_cases b0 : b = 0, { subst b0, simp, refl },
 generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
 show rat.mk' _ _ _ _ = _, rw num_denom',
 have d0 := ne_of_gt (int.coe_nat_lt.2 h₁),
 apply (mk_eq d0 b0).2, have h₁ := (mk_eq b0 d0).1 ha,
 simp only [neg_mul, congr_arg has_neg.neg h₁]
end

@[simp] lemma mk_neg_denom (n d : ℤ) : n /. -d = -n /. d :=
begin
 by_cases hd : d = 0;
 simp [rat.mk_eq, hd]
end

/-- Multiplication of rational numbers. Use `(*)` instead. -/
protected def mul : ℚ → ℚ → ℚ
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := mk_pnat (n₁ * n₂) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : has_mul ℚ := ⟨rat.mul⟩

@[simp] theorem mul_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
 (a /. b) * (c /. d) = (a * c) /. (b * d) :=
begin
 apply lift_binop_eq rat.mul; intros; try {assumption},
 { apply mk_pnat_eq },
 { apply mul_ne_zero d₁0 d₂0 },
 cc
end

/-- Inverse rational number. Use `r⁻¹` instead. -/
protected def inv : ℚ → ℚ
| ⟨(n+1:ℕ), d, h, c⟩ := ⟨d, n+1, n.succ_pos, c.symm⟩
| ⟨0, d, h, c⟩ := 0
| ⟨-[1+ n], d, h, c⟩ := ⟨-d, n+1, n.succ_pos, nat.coprime.symm $ by simp; exact c⟩

instance : has_inv ℚ := ⟨rat.inv⟩
instance : has_div ℚ := ⟨λ a b, a * b⁻¹⟩

@[simp] theorem inv_def {a b : ℤ} : (a /. b)⁻¹ = b /. a :=
begin
 by_cases a0 : a = 0, { subst a0, simp, refl },
 by_cases b0 : b = 0, { subst b0, simp, refl },
 generalize ha : a /. b = x, cases x with n d h c, rw num_denom' at ha,
 refine eq.trans (_ : rat.inv ⟨n, d, h, c⟩ = d /. n) _,
 { cases n with n; [cases n with n, skip],
 { refl },
 { change int.of_nat n.succ with (n+1:ℕ),
 unfold rat.inv, rw num_denom' },
 { unfold rat.inv, rw num_denom', refl } },
 have n0 : n ≠ 0,
 { rintro rfl,
 rw [rat.zero_mk] at ha; rw [ mk_eq_zero b0] at ha,
 exact a0 ha },
 have d0 := ne_of_gt (int.coe_nat_lt.2 h),
 have ha := (mk_eq b0 d0).1 ha,
 apply (mk_eq n0 a0).2,
 cc
end

variables (a b c : ℚ)

protected theorem add_zero : a + 0 = a :=
num_denom_cases_on' a $ λ n d h,
by rw [← zero_mk d]; simp [h, -zero_mk]

protected theorem zero_add : 0 + a = a :=
num_denom_cases_on' a $ λ n d h,
by rw [← zero_mk d]; simp [h, -zero_mk]

protected theorem add_comm : a + b = b + a :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
by simp [h₁, h₂]; cc

protected theorem add_assoc : a + b + c = a + (b + c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero, mul_add, mul_comm, mul_left_comm, add_left_comm, add_assoc]

protected theorem add_left_neg : -a + a = 0 :=
num_denom_cases_on' a $ λ n d h,
by simp [h]

@[simp] lemma mk_zero_one : 0 /. 1 = 0 :=
show mk_pnat _ _ = _, by { rw mk_pnat, simp, refl }

@[simp] lemma mk_one_one : 1 /. 1 = 1 :=
show mk_pnat _ _ = _, by { rw mk_pnat, simp, refl }

@[simp] lemma mk_neg_one_one : (-1) /. 1 = -1 :=
show mk_pnat _ _ = _, by { rw mk_pnat, simp, refl }

protected theorem mul_one : a * 1 = a :=
num_denom_cases_on' a $ λ n d h,
by { rw ← mk_one_one, simp [h, -mk_one_one] }

protected theorem one_mul : 1 * a = a :=
num_denom_cases_on' a $ λ n d h,
by { rw ← mk_one_one, simp [h, -mk_one_one] }

protected theorem mul_comm : a * b = b * a :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
by simp [h₁, h₂, mul_comm]

protected theorem mul_assoc : a * b * c = a * (b * c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero, mul_comm, mul_left_comm]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero];
 refine (div_mk_div_cancel_left (int.coe_nat_ne_zero.2 h₃)).symm.trans _;
 simp [mul_add, mul_comm, mul_assoc, mul_left_comm]

protected theorem mul_add : a * (b + c) = a * b + a * c :=
by rw [rat.mul_comm]; rw [ rat.add_mul]; rw [ rat.mul_comm]; rw [ rat.mul_comm c a]

protected theorem zero_ne_one : 0 ≠ (1:ℚ) :=
by { rw [ne_comm]; rw [ ← mk_one_one]; rw [ mk_ne_zero one_ne_zero], exact one_ne_zero }

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
num_denom_cases_on' a $ λ n d h a0,
have n0 : n ≠ 0, from mt (by { rintro rfl, simp }) a0,
by simpa [h, n0, mul_comm] using @div_mk_div_cancel_left 1 1 _ n0

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
eq.trans (rat.mul_comm _ _) (rat.mul_inv_cancel _ h)

instance : decidable_eq ℚ := by tactic.mk_dec_eq_instance

/-! At this point in the import hierarchy we have not defined the `field` typeclass.
Instead we'll instantiate `comm_ring` and `comm_group_with_zero` at this point.
The `rat.field` instance and any field-specific lemmas can be found in `data.rat.basic`.
-/

instance : comm_ring ℚ :=
{ zero := 0,
 add := (+),
 neg := has_neg.neg,
 one := 1,
 mul := (*),
 zero_add := rat.zero_add,
 add_zero := rat.add_zero,
 add_comm := rat.add_comm,
 add_assoc := rat.add_assoc,
 add_left_neg := rat.add_left_neg,
 mul_one := rat.mul_one,
 one_mul := rat.one_mul,
 mul_comm := rat.mul_comm,
 mul_assoc := rat.mul_assoc,
 left_distrib := rat.mul_add,
 right_distrib := rat.add_mul,
 int_cast := coe,
 /- Important: We do not set `nat_cast := λ n, ((n : ℤ) : ℚ)` (even though it's defeq) as that
 makes `int.cast_coe_nat` and `coe_coe` loop in `simp`. -/
 nat_cast := λ n, of_int n,
 nat_cast_zero := rfl,
 nat_cast_succ := λ n, by simp only [of_int_eq_cast, coe_int_eq_mk,
 add_def one_ne_zero one_ne_zero, ← mk_one_one, nat.cast_add, nat.cast_one, mul_one] }

instance : comm_group_with_zero ℚ :=
{ zero := 0,
 one := 1,
 mul := (*),
 inv := has_inv.inv,
 div := (/),
 exists_pair_ne := ⟨0, 1, rat.zero_ne_one⟩,
 inv_zero := rfl,
 mul_inv_cancel := rat.mul_inv_cancel,
 mul_zero := mul_zero,
 zero_mul := zero_mul,
 .. rat.comm_ring }

instance : is_domain ℚ :=
no_zero_divisors.to_is_domain _

/- Extra instances to short-circuit type class resolution -/
-- TODO(Mario): this instance slows down data.real.basic
instance : nontrivial ℚ := by apply_instance
--instance : ring ℚ := by apply_instance
instance : comm_semiring ℚ := by apply_instance
instance : semiring ℚ := by apply_instance
instance : add_comm_group ℚ := by apply_instance
instance : add_group ℚ := by apply_instance
instance : add_comm_monoid ℚ := by apply_instance
instance : add_monoid ℚ := by apply_instance
instance : add_left_cancel_semigroup ℚ := by apply_instance
instance : add_right_cancel_semigroup ℚ := by apply_instance
instance : add_comm_semigroup ℚ := by apply_instance
instance : add_semigroup ℚ := by apply_instance
instance : comm_monoid ℚ := by apply_instance
instance : monoid ℚ := by apply_instance
instance : comm_semigroup ℚ := by apply_instance
instance : semigroup ℚ := by apply_instance

lemma denom_ne_zero (q : ℚ) : q.denom ≠ 0 :=
ne_of_gt q.pos

lemma eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.denom = q.num * p.denom :=
begin
 conv { to_lhs, rw [← @num_denom p]; rw [ ← @num_denom q] },
 apply rat.mk_eq;
 { rw [← nat.cast_zero]; rw [ ne]; rw [ int.coe_nat_eq_coe_nat_iff],
 apply denom_ne_zero, },
end


theorem sub_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
 a /. b - c /. d = (a * d - c * b) /. (b * d) :=
by simp [b0, d0, sub_eq_add_neg]

@[simp] lemma denom_neg_eq_denom (q : ℚ) : (-q).denom = q.denom := rfl

@[simp] lemma num_neg_eq_neg_num (q : ℚ) : (-q).num = -(q.num) := rfl

@[simp] lemma num_zero : rat.num 0 = 0 := rfl

@[simp] lemma denom_zero : rat.denom 0 = 1 := rfl

lemma zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 :=
have q = q.num /. q.denom, from num_denom.symm,
by simpa [hq]

lemma zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
⟨λ _, by simp *, zero_of_num_zero⟩

lemma num_ne_zero_of_ne_zero {q : ℚ} (h : q ≠ 0) : q.num ≠ 0 :=
assume : q.num = 0,
h $ zero_of_num_zero this

@[simp] lemma num_one : (1 : ℚ).num = 1 := rfl

@[simp] lemma denom_one : (1 : ℚ).denom = 1 := rfl

lemma mk_num_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 :=
assume : n = 0,
hq $ by simpa [this] using hqnd

lemma mk_denom_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 :=
assume : d = 0,
hq $ by simpa [this] using hqnd

lemma mk_ne_zero_of_ne_zero {n d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
(mk_ne_zero hd).mpr h

lemma mul_num_denom (q r : ℚ) : q * r = (q.num * r.num) /. ↑(q.denom * r.denom) :=
have hq' : (↑q.denom : ℤ) ≠ 0, by have := denom_ne_zero q; simpa,
have hr' : (↑r.denom : ℤ) ≠ 0, by have := denom_ne_zero r; simpa,
suffices (q.num /. ↑q.denom) * (r.num /. ↑r.denom) = (q.num * r.num) /. ↑(q.denom * r.denom),
 by simpa using this,
by simp [mul_def hq' hr', -num_denom]

lemma div_num_denom (q r : ℚ) : q / r = (q.num * r.denom) /. (q.denom * r.num) :=
if hr : r.num = 0 then
 have hr' : r = 0, from zero_of_num_zero hr,
 by simp *
else
 calc q / r = q * r⁻¹ : div_eq_mul_inv q r
 ... = (q.num /. q.denom) * (r.num /. r.denom)⁻¹ : by simp
 ... = (q.num /. q.denom) * (r.denom /. r.num) : by rw inv_def
 ... = (q.num * r.denom) /. (q.denom * r.num) : mul_def (by simpa using denom_ne_zero q) hr

section casts

protected lemma add_mk (a b c : ℤ) : (a + b) /. c = a /. c + b /. c :=
if h : c = 0 then by simp [h] else
by { rw [add_def h h]; rw [ mk_eq h (mul_ne_zero h h)], simp [add_mul, mul_assoc] }

theorem mk_eq_div (n d : ℤ) : n /. d = ((n : ℚ) / d) :=
begin
 by_cases d0 : d = 0, {simp [d0, div_zero]},
 simp [division_def, coe_int_eq_mk, mul_def one_ne_zero d0]
end

lemma mk_mul_mk_cancel {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : (n /. x) * (x /. d) = n /. d :=
begin
 by_cases hd : d = 0,
 { rw hd,
 simp},
 rw [mul_def hx hd]; rw [ mul_comm x]; rw [ div_mk_div_cancel_left hx],
end

lemma mk_div_mk_cancel_left {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : (n /. x) / (d /. x) = n /. d :=
by rw [div_eq_mul_inv]; rw [ inv_def]; rw [ mk_mul_mk_cancel hx]

lemma mk_div_mk_cancel_right {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : (x /. n) / (x /. d) = d /. n :=
by rw [div_eq_mul_inv]; rw [ inv_def]; rw [ mul_comm]; rw [ mk_mul_mk_cancel hx]

lemma coe_int_div_eq_mk {n d : ℤ} : (n : ℚ) / ↑d = n /. d :=
begin
 repeat {rw coe_int_eq_mk},
 exact mk_div_mk_cancel_left one_ne_zero n d,
end

@[simp]
theorem num_div_denom (r : ℚ) : (r.num / r.denom : ℚ) = r :=
by rw [← int.cast_coe_nat]; rw [ ← mk_eq_div]; rw [ num_denom]

lemma coe_int_num_of_denom_eq_one {q : ℚ} (hq : q.denom = 1) : ↑(q.num) = q :=
by { conv_rhs { rw [←(@num_denom q)]; rw [ hq] }, rw [coe_int_eq_mk], refl }

lemma denom_eq_one_iff (r : ℚ) : r.denom = 1 ↔ ↑r.num = r :=
⟨rat.coe_int_num_of_denom_eq_one, λ h, h ▸ rat.coe_int_denom r.num⟩

instance can_lift : can_lift ℚ ℤ coe (λ q, q.denom = 1) :=
⟨λ q hq, ⟨q.num, coe_int_num_of_denom_eq_one hq⟩⟩

theorem coe_nat_eq_mk (n : ℕ) : ↑n = n /. 1 :=
by rw [← int.cast_coe_nat]; rw [ coe_int_eq_mk]

@[simp, norm_cast] theorem coe_nat_num (n : ℕ) : (n : ℚ).num = n :=
by rw [← int.cast_coe_nat]; rw [ coe_int_num]

@[simp, norm_cast] theorem coe_nat_denom (n : ℕ) : (n : ℚ).denom = 1 :=
by rw [← int.cast_coe_nat]; rw [ coe_int_denom]

-- Will be subsumed by `int.coe_inj` after we have defined
-- `linear_ordered_field ℚ` (which implies characteristic zero).
lemma coe_int_inj (m n : ℤ) : (m : ℚ) = n ↔ m = n := ⟨congr_arg num, congr_arg _⟩

end casts

end rat

-- Guard against import creep.
assert_not_exists field

