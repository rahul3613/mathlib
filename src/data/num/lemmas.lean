/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.num.bitwise
import data.int.char_zero
import data.nat.gcd.basic
import data.nat.psub
import data.nat.size

/-!
# Properties of the binary representation of integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

local attribute [simp] add_assoc

namespace pos_num
variables {α : Type*}

@[simp, norm_cast] theorem cast_one [has_one α] [has_add α] :
 ((1 : pos_num) : α) = 1 := rfl
@[simp] theorem cast_one' [has_one α] [has_add α] : (pos_num.one : α) = 1 := rfl
@[simp, norm_cast] theorem cast_bit0 [has_one α] [has_add α] (n : pos_num) :
 (n.bit0 : α) = _root_.bit0 n := rfl
@[simp, norm_cast] theorem cast_bit1 [has_one α] [has_add α] (n : pos_num) :
 (n.bit1 : α) = _root_.bit1 n := rfl

@[simp, norm_cast] theorem cast_to_nat [add_monoid_with_one α] :
 ∀ n : pos_num, ((n : ℕ) : α) = n
| 1 := nat.cast_one
| (bit0 p) := (nat.cast_bit0 _).trans $ congr_arg _root_.bit0 p.cast_to_nat
| (bit1 p) := (nat.cast_bit1 _).trans $ congr_arg _root_.bit1 p.cast_to_nat

@[simp, norm_cast] theorem to_nat_to_int (n : pos_num) : ((n : ℕ) : ℤ) = n :=
cast_to_nat _

@[simp, norm_cast] theorem cast_to_int [add_group_with_one α] (n : pos_num) :
 ((n : ℤ) : α) = n :=
by rw [← to_nat_to_int]; rw [ int.cast_coe_nat]; rw [ cast_to_nat]

theorem succ_to_nat : ∀ n, (succ n : ℕ) = n + 1
| 1 := rfl
| (bit0 p) := rfl
| (bit1 p) := (congr_arg _root_.bit0 (succ_to_nat p)).trans $
 show ↑p + 1 + ↑p + 1 = ↑p + ↑p + 1 + 1, by simp [add_left_comm]

theorem one_add (n : pos_num) : 1 + n = succ n := by cases n; refl
theorem add_one (n : pos_num) : n + 1 = succ n := by cases n; refl

@[norm_cast]
theorem add_to_nat : ∀ m n, ((m + n : pos_num) : ℕ) = m + n
| 1 b := by rw [one_add b]; rw [ succ_to_nat]; rw [ add_comm]; refl
| a 1 := by rw [add_one a]; rw [ succ_to_nat]; refl
| (bit0 a) (bit0 b) := (congr_arg _root_.bit0 (add_to_nat a b)).trans $ add_add_add_comm _ _ _ _
| (bit0 a) (bit1 b) := (congr_arg _root_.bit1 (add_to_nat a b)).trans $
 show ((a + b) + (a + b) + 1 : ℕ) = (a + a) + (b + b + 1), by simp [add_left_comm]
| (bit1 a) (bit0 b) := (congr_arg _root_.bit1 (add_to_nat a b)).trans $
 show ((a + b) + (a + b) + 1 : ℕ) = (a + a + 1) + (b + b), by simp [add_comm, add_left_comm]
| (bit1 a) (bit1 b) :=
 show (succ (a + b) + succ (a + b) : ℕ) = (a + a + 1) + (b + b + 1),
 by rw [succ_to_nat]; rw [ add_to_nat]; simp [add_left_comm]

theorem add_succ : ∀ (m n : pos_num), m + succ n = succ (m + n)
| 1 b := by simp [one_add]
| (bit0 a) 1 := congr_arg bit0 (add_one a)
| (bit1 a) 1 := congr_arg bit1 (add_one a)
| (bit0 a) (bit0 b) := rfl
| (bit0 a) (bit1 b) := congr_arg bit0 (add_succ a b)
| (bit1 a) (bit0 b) := rfl
| (bit1 a) (bit1 b) := congr_arg bit1 (add_succ a b)

theorem bit0_of_bit0 : Π n, _root_.bit0 n = bit0 n
| 1 := rfl
| (bit0 p) := congr_arg bit0 (bit0_of_bit0 p)
| (bit1 p) := show bit0 (succ (_root_.bit0 p)) = _, by rw bit0_of_bit0; refl

theorem bit1_of_bit1 (n : pos_num) : _root_.bit1 n = bit1 n :=
show _root_.bit0 n + 1 = bit1 n, by rw [add_one]; rw [ bit0_of_bit0]; refl

@[norm_cast]
theorem mul_to_nat (m) : ∀ n, ((m * n : pos_num) : ℕ) = m * n
| 1 := (mul_one _).symm
| (bit0 p) := show (↑(m * p) + ↑(m * p) : ℕ) = ↑m * (p + p), by rw [mul_to_nat]; rw [ left_distrib]
| (bit1 p) := (add_to_nat (bit0 (m * p)) m).trans $
 show (↑(m * p) + ↑(m * p) + ↑m : ℕ) = ↑m * (p + p) + m, by rw [mul_to_nat]; rw [ left_distrib]

theorem to_nat_pos : ∀ n : pos_num, 0 < (n : ℕ)
| 1 := zero_lt_one
| (bit0 p) := let h := to_nat_pos p in add_pos h h
| (bit1 p) := nat.succ_pos _

theorem cmp_to_nat_lemma {m n : pos_num} : (m:ℕ) < n → (bit1 m : ℕ) < bit0 n :=
show (m:ℕ) < n → (m + m + 1 + 1 : ℕ) ≤ n + n,
by intro h; rw [nat.add_right_comm m m 1]; rw [ add_assoc]; exact add_le_add h h

theorem cmp_swap (m) : ∀n, (cmp m n).swap = cmp n m :=
by induction m with m IH m IH; intro n;
 cases n with n n; try {unfold cmp}; try {refl}; rw ←IH; cases cmp m n; refl

theorem cmp_to_nat : ∀ (m n), (ordering.cases_on (cmp m n) ((m:ℕ) < n) (m = n) ((n:ℕ) < m) : Prop)
| 1 1 := rfl
| (bit0 a) 1 := let h : (1:ℕ) ≤ a := to_nat_pos a in add_le_add h h
| (bit1 a) 1 := nat.succ_lt_succ $ to_nat_pos $ bit0 a
| 1 (bit0 b) := let h : (1:ℕ) ≤ b := to_nat_pos b in add_le_add h h
| 1 (bit1 b) := nat.succ_lt_succ $ to_nat_pos $ bit0 b
| (bit0 a) (bit0 b) := begin
 have := cmp_to_nat a b, revert this, cases cmp a b; dsimp; intro,
 { exact add_lt_add this this },
 { rw this },
 { exact add_lt_add this this }
 end
| (bit0 a) (bit1 b) := begin dsimp [cmp],
 have := cmp_to_nat a b, revert this, cases cmp a b; dsimp; intro,
 { exact nat.le_succ_of_le (add_lt_add this this) },
 { rw this, apply nat.lt_succ_self },
 { exact cmp_to_nat_lemma this }
 end
| (bit1 a) (bit0 b) := begin dsimp [cmp],
 have := cmp_to_nat a b, revert this, cases cmp a b; dsimp; intro,
 { exact cmp_to_nat_lemma this },
 { rw this, apply nat.lt_succ_self },
 { exact nat.le_succ_of_le (add_lt_add this this) },
 end
| (bit1 a) (bit1 b) := begin
 have := cmp_to_nat a b, revert this, cases cmp a b; dsimp; intro,
 { exact nat.succ_lt_succ (add_lt_add this this) },
 { rw this },
 { exact nat.succ_lt_succ (add_lt_add this this) }
 end

@[norm_cast]
theorem lt_to_nat {m n : pos_num} : (m:ℕ) < n ↔ m < n :=
show (m:ℕ) < n ↔ cmp m n = ordering.lt, from
match cmp m n, cmp_to_nat m n with
| ordering.lt, h := by simp at h; simp [h]
| ordering.eq, h := by simp at h; simp [h, lt_irrefl]; exact dec_trivial
| ordering.gt, h := by simp [not_lt_of_gt h]; exact dec_trivial
end

@[norm_cast]
theorem le_to_nat {m n : pos_num} : (m:ℕ) ≤ n ↔ m ≤ n :=
by rw ← not_lt; exact not_congr lt_to_nat

end pos_num

namespace num
variables {α : Type*}
open pos_num

theorem add_zero (n : num) : n + 0 = n := by cases n; refl
theorem zero_add (n : num) : 0 + n = n := by cases n; refl

theorem add_one : ∀ n : num, n + 1 = succ n
| 0 := rfl
| (pos p) := by cases p; refl

theorem add_succ : ∀ (m n : num), m + succ n = succ (m + n)
| 0 n := by simp [zero_add]
| (pos p) 0 := show pos (p + 1) = succ (pos p + 0),
 by rw [pos_num.add_one]; rw [ add_zero]; refl
| (pos p) (pos q) := congr_arg pos (pos_num.add_succ _ _)

theorem bit0_of_bit0 : ∀ n : num, bit0 n = n.bit0
| 0 := rfl
| (pos p) := congr_arg pos p.bit0_of_bit0

theorem bit1_of_bit1 : ∀ n : num, bit1 n = n.bit1
| 0 := rfl
| (pos p) := congr_arg pos p.bit1_of_bit1

@[simp] lemma of_nat'_zero : num.of_nat' 0 = 0 :=
by simp [num.of_nat']

lemma of_nat'_bit (b n) : of_nat' (nat.bit b n) = cond b num.bit1 num.bit0 (of_nat' n) :=
nat.binary_rec_eq rfl _ _

@[simp] lemma of_nat'_one : num.of_nat' 1 = 1 :=
by erw [of_nat'_bit tt 0]; erw [ cond]; erw [ of_nat'_zero]; refl

lemma bit1_succ : ∀ n : num, n.bit1.succ = n.succ.bit0
| 0 := rfl
| (pos n) := rfl

lemma of_nat'_succ : ∀ {n}, of_nat' (n + 1) = of_nat' n + 1 :=
nat.binary_rec (by simp; refl) $ λ b n ih,
begin
 cases b,
 { erw [of_nat'_bit tt n]; erw [ of_nat'_bit],
 simp only [← bit1_of_bit1, ← bit0_of_bit0, cond, _root_.bit1] },
 { erw [show n.bit tt + 1 = (n + 1).bit ff]; erw [ by simp [nat.bit]; erw [ _root_.bit1]; erw [ _root_.bit0]; cc,
 of_nat'_bit, of_nat'_bit, ih],
 simp only [cond, add_one, bit1_succ], },
end

@[simp] theorem add_of_nat' (m n) : num.of_nat' (m + n) = num.of_nat' m + num.of_nat' n :=
by induction n; simp [nat.add_zero, of_nat'_succ, add_zero, nat.add_succ, add_one, add_succ, *]

@[simp, norm_cast] theorem cast_zero [has_zero α] [has_one α] [has_add α] :
 ((0 : num) : α) = 0 := rfl

@[simp] theorem cast_zero' [has_zero α] [has_one α] [has_add α] :
 (num.zero : α) = 0 := rfl

@[simp, norm_cast] theorem cast_one [has_zero α] [has_one α] [has_add α] :
 ((1 : num) : α) = 1 := rfl

@[simp] theorem cast_pos [has_zero α] [has_one α] [has_add α]
 (n : pos_num) : (num.pos n : α) = n := rfl

theorem succ'_to_nat : ∀ n, (succ' n : ℕ) = n + 1
| 0 := (_root_.zero_add _).symm
| (pos p) := pos_num.succ_to_nat _

theorem succ_to_nat (n) : (succ n : ℕ) = n + 1 := succ'_to_nat n

@[simp, norm_cast] theorem cast_to_nat [add_monoid_with_one α] : ∀ n : num, ((n : ℕ) : α) = n
| 0 := nat.cast_zero
| (pos p) := p.cast_to_nat

@[norm_cast]
theorem add_to_nat : ∀ m n, ((m + n : num) : ℕ) = m + n
| 0 0 := rfl
| 0 (pos q) := (_root_.zero_add _).symm
| (pos p) 0 := rfl
| (pos p) (pos q) := pos_num.add_to_nat _ _

@[norm_cast]
theorem mul_to_nat : ∀ m n, ((m * n : num) : ℕ) = m * n
| 0 0 := rfl
| 0 (pos q) := (zero_mul _).symm
| (pos p) 0 := rfl
| (pos p) (pos q) := pos_num.mul_to_nat _ _

theorem cmp_to_nat : ∀ (m n), (ordering.cases_on (cmp m n) ((m:ℕ) < n) (m = n) ((n:ℕ) < m) : Prop)
| 0 0 := rfl
| 0 (pos b) := to_nat_pos _
| (pos a) 0 := to_nat_pos _
| (pos a) (pos b) :=
 by { have := pos_num.cmp_to_nat a b; revert this; dsimp [cmp];
 cases pos_num.cmp a b, exacts [id, congr_arg pos, id] }

@[norm_cast]
theorem lt_to_nat {m n : num} : (m:ℕ) < n ↔ m < n :=
show (m:ℕ) < n ↔ cmp m n = ordering.lt, from
match cmp m n, cmp_to_nat m n with
| ordering.lt, h := by simp at h; simp [h]
| ordering.eq, h := by simp at h; simp [h, lt_irrefl]; exact dec_trivial
| ordering.gt, h := by simp [not_lt_of_gt h]; exact dec_trivial
end

@[norm_cast]
theorem le_to_nat {m n : num} : (m:ℕ) ≤ n ↔ m ≤ n :=
by rw ← not_lt; exact not_congr lt_to_nat

end num

namespace pos_num

@[simp] theorem of_to_nat' : Π (n : pos_num), num.of_nat' (n : ℕ) = num.pos n
| 1 := by erw [@num.of_nat'_bit tt 0]; erw [ num.of_nat'_zero]; refl
| (bit0 p) := by erw [@num.of_nat'_bit ff]; erw [ of_to_nat']; refl
| (bit1 p) := by erw [@num.of_nat'_bit tt]; erw [ of_to_nat']; refl
end pos_num

namespace num

@[simp, norm_cast] theorem of_to_nat' : Π (n : num), num.of_nat' (n : ℕ) = n
| 0 := of_nat'_zero
| (pos p) := p.of_to_nat'

@[norm_cast] theorem to_nat_inj {m n : num} : (m : ℕ) = n ↔ m = n :=
⟨λ h, function.left_inverse.injective of_to_nat' h, congr_arg _⟩

/--
This tactic tries to turn an (in)equality about `num`s to one about `nat`s by rewriting.
```lean
example (n : num) (m : num) : n ≤ n + m :=
begin
 num.transfer_rw,
 exact nat.le_add_right _ _
end
```
-/
meta def transfer_rw : tactic unit :=
`[repeat {rw ← to_nat_inj <|> rw ← lt_to_nat <|> rw ← le_to_nat},
 repeat {rw add_to_nat <|> rw mul_to_nat <|> rw cast_one <|> rw cast_zero}]

/--
This tactic tries to prove (in)equalities about `num`s by transfering them to the `nat` world and
then trying to call `simp`.
```lean
example (n : num) (m : num) : n ≤ n + m := by num.transfer
```
-/
meta def transfer : tactic unit := `[intros, transfer_rw, try {simp}]

instance : add_monoid num :=
{ add := (+),
 zero := 0,
 zero_add := zero_add,
 add_zero := add_zero,
 add_assoc := by transfer }

instance : add_monoid_with_one num :=
{ nat_cast := num.of_nat',
 one := 1,
 nat_cast_zero := of_nat'_zero,
 nat_cast_succ := λ _, of_nat'_succ,
 .. num.add_monoid }

instance : comm_semiring num :=
by refine_struct
{ mul := (*),
 one := 1,
 add := (+),
 zero := 0,
 npow := @npow_rec num ⟨1⟩ ⟨(*)⟩,
 .. num.add_monoid, .. num.add_monoid_with_one };
try { intros, refl }; try { transfer };
simp [add_comm, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]

instance : ordered_cancel_add_comm_monoid num :=
{ lt := (<),
 lt_iff_le_not_le := by {intros a b, transfer_rw, apply lt_iff_le_not_le},
 le := (≤),
 le_refl := by transfer,
 le_trans := by {intros a b c, transfer_rw, apply le_trans},
 le_antisymm := by {intros a b, transfer_rw, apply le_antisymm},
 add_le_add_left := by {intros a b h c, revert h, transfer_rw,
 exact λ h, add_le_add_left h c},
 le_of_add_le_add_left := by {intros a b c, transfer_rw, apply le_of_add_le_add_left},
 ..num.comm_semiring }

instance : linear_ordered_semiring num :=
{ le_total := by {intros a b, transfer_rw, apply le_total},
 zero_le_one := dec_trivial,
 mul_lt_mul_of_pos_left := by {intros a b c, transfer_rw, apply mul_lt_mul_of_pos_left},
 mul_lt_mul_of_pos_right := by {intros a b c, transfer_rw, apply mul_lt_mul_of_pos_right},
 decidable_lt := num.decidable_lt,
 decidable_le := num.decidable_le,
 decidable_eq := num.decidable_eq,
 exists_pair_ne := ⟨0, 1, dec_trivial⟩,
 ..num.comm_semiring, ..num.ordered_cancel_add_comm_monoid }

@[simp, norm_cast] theorem add_of_nat (m n) : ((m + n : ℕ) : num) = m + n :=
add_of_nat' _ _

@[simp, norm_cast] theorem to_nat_to_int (n : num) : ((n : ℕ) : ℤ) = n :=
cast_to_nat _

@[simp, norm_cast] theorem cast_to_int {α} [add_group_with_one α] (n : num) : ((n : ℤ) : α) = n :=
by rw [← to_nat_to_int]; rw [ int.cast_coe_nat]; rw [ cast_to_nat]

theorem to_of_nat : Π (n : ℕ), ((n : num) : ℕ) = n
| 0 := by rw [nat.cast_zero]; rw [ cast_zero]
| (n+1) := by rw [nat.cast_succ]; rw [ add_one]; rw [ succ_to_nat]; rw [ to_of_nat]

@[simp, norm_cast]
theorem of_nat_cast {α} [add_monoid_with_one α] (n : ℕ) : ((n : num) : α) = n :=
by rw [← cast_to_nat]; rw [ to_of_nat]

@[simp, norm_cast] theorem of_nat_inj {m n : ℕ} : (m : num) = n ↔ m = n :=
⟨λ h, function.left_inverse.injective to_of_nat h, congr_arg _⟩

@[simp, norm_cast] theorem of_to_nat : Π (n : num), ((n : ℕ) : num) = n := of_to_nat'

@[norm_cast]
theorem dvd_to_nat (m n : num) : (m : ℕ) ∣ n ↔ m ∣ n :=
⟨λ ⟨k, e⟩, ⟨k, by rw [← of_to_nat n]; rw [ e]; simp⟩,
 λ ⟨k, e⟩, ⟨k, by simp [e, mul_to_nat]⟩⟩

end num

namespace pos_num
variables {α : Type*}
open num

@[simp, norm_cast] theorem of_to_nat : Π (n : pos_num), ((n : ℕ) : num) = num.pos n := of_to_nat'

@[norm_cast] theorem to_nat_inj {m n : pos_num} : (m : ℕ) = n ↔ m = n :=
⟨λ h, num.pos.inj $ by rw [← pos_num.of_to_nat]; rw [ ← pos_num.of_to_nat]; rw [ h],
 congr_arg _⟩

theorem pred'_to_nat : ∀ n, (pred' n : ℕ) = nat.pred n
| 1 := rfl
| (bit0 n) :=
 have nat.succ ↑(pred' n) = ↑n,
 by rw [pred'_to_nat n]; rw [ nat.succ_pred_eq_of_pos (to_nat_pos n)],
 match pred' n, this : ∀ k : num, nat.succ ↑k = ↑n →
 ↑(num.cases_on k 1 bit1 : pos_num) = nat.pred (_root_.bit0 n) with
 | 0, (h : ((1:num):ℕ) = n) := by rw ← to_nat_inj.1 h; refl
 | num.pos p, (h : nat.succ ↑p = n) :=
 by rw ← h; exact (nat.succ_add p p).symm
 end
| (bit1 n) := rfl

@[simp] theorem pred'_succ' (n) : pred' (succ' n) = n :=
num.to_nat_inj.1 $ by rw [pred'_to_nat]; rw [ succ'_to_nat]; rw [ nat.add_one]; rw [ nat.pred_succ]

@[simp] theorem succ'_pred' (n) : succ' (pred' n) = n :=
to_nat_inj.1 $ by rw [succ'_to_nat]; rw [ pred'_to_nat]; rw [ nat.add_one]; rw [ nat.succ_pred_eq_of_pos (to_nat_pos _)]

instance : has_dvd pos_num := ⟨λ m n, pos m ∣ pos n⟩

@[norm_cast] theorem dvd_to_nat {m n : pos_num} : (m:ℕ) ∣ n ↔ m ∣ n :=
num.dvd_to_nat (pos m) (pos n)

theorem size_to_nat : ∀ n, (size n : ℕ) = nat.size n
| 1 := nat.size_one.symm
| (bit0 n) := by rw [size]; rw [ succ_to_nat]; rw [ size_to_nat]; rw [ cast_bit0]; rw [ nat.size_bit0 $ ne_of_gt $ to_nat_pos n]
| (bit1 n) := by rw [size]; rw [ succ_to_nat]; rw [ size_to_nat]; rw [ cast_bit1]; rw [ nat.size_bit1]

theorem size_eq_nat_size : ∀ n, (size n : ℕ) = nat_size n
| 1 := rfl
| (bit0 n) := by rw [size]; rw [ succ_to_nat]; rw [ nat_size]; rw [ size_eq_nat_size]
| (bit1 n) := by rw [size]; rw [ succ_to_nat]; rw [ nat_size]; rw [ size_eq_nat_size]

theorem nat_size_to_nat (n) : nat_size n = nat.size n :=
by rw [← size_eq_nat_size]; rw [ size_to_nat]

theorem nat_size_pos (n) : 0 < nat_size n :=
by cases n; apply nat.succ_pos

/--
This tactic tries to turn an (in)equality about `pos_num`s to one about `nat`s by rewriting.
```lean
example (n : pos_num) (m : pos_num) : n ≤ n + m :=
begin
 pos_num.transfer_rw,
 exact nat.le_add_right _ _
end
```
-/
meta def transfer_rw : tactic unit :=
`[repeat {rw ← to_nat_inj <|> rw ← lt_to_nat <|> rw ← le_to_nat},
 repeat {rw add_to_nat <|> rw mul_to_nat <|> rw cast_one <|> rw cast_zero}]

/--
This tactic tries to prove (in)equalities about `pos_num`s by transferring them to the `nat` world
and then trying to call `simp`.
```lean
example (n : pos_num) (m : pos_num) : n ≤ n + m := by pos_num.transfer
```
-/
meta def transfer : tactic unit :=
`[intros, transfer_rw, try {simp [add_comm, add_left_comm, mul_comm, mul_left_comm]}]

instance : add_comm_semigroup pos_num :=
by refine {add := (+), ..}; transfer

instance : comm_monoid pos_num :=
by refine_struct {mul := (*), one := (1 : pos_num), npow := @npow_rec pos_num ⟨1⟩ ⟨(*)⟩};
try { intros, refl }; transfer

instance : distrib pos_num :=
by refine {add := (+), mul := (*), ..}; {transfer, simp [mul_add, mul_comm]}

instance : linear_order pos_num :=
{ lt := (<),
 lt_iff_le_not_le := by {intros a b, transfer_rw, apply lt_iff_le_not_le},
 le := (≤),
 le_refl := by transfer,
 le_trans := by {intros a b c, transfer_rw, apply le_trans},
 le_antisymm := by {intros a b, transfer_rw, apply le_antisymm},
 le_total := by {intros a b, transfer_rw, apply le_total},
 decidable_lt := by apply_instance,
 decidable_le := by apply_instance,
 decidable_eq := by apply_instance }

@[simp] theorem cast_to_num (n : pos_num) : ↑n = num.pos n :=
by rw [← cast_to_nat]; rw [ ← of_to_nat n]

@[simp, norm_cast]
theorem bit_to_nat (b n) : (bit b n : ℕ) = nat.bit b n :=
by cases b; refl

@[simp, norm_cast]
theorem cast_add [add_monoid_with_one α] (m n) : ((m + n : pos_num) : α) = m + n :=
by rw [← cast_to_nat]; rw [ add_to_nat]; rw [ nat.cast_add]; rw [ cast_to_nat]; rw [ cast_to_nat]

@[simp, norm_cast, priority 500]
theorem cast_succ [add_monoid_with_one α] (n : pos_num) : (succ n : α) = n + 1 :=
by rw [← add_one]; rw [ cast_add]; rw [ cast_one]

@[simp, norm_cast]
theorem cast_inj [add_monoid_with_one α] [char_zero α] {m n : pos_num} : (m:α) = n ↔ m = n :=
by rw [← cast_to_nat m]; rw [ ← cast_to_nat n]; rw [ nat.cast_inj]; rw [ to_nat_inj]

@[simp]
theorem one_le_cast [linear_ordered_semiring α] (n : pos_num) : (1 : α) ≤ n :=
by rw [← cast_to_nat]; rw [ ← nat.cast_one]; rw [ nat.cast_le]; apply to_nat_pos

@[simp]
theorem cast_pos [linear_ordered_semiring α] (n : pos_num) : 0 < (n : α) :=
lt_of_lt_of_le zero_lt_one (one_le_cast n)

@[simp, norm_cast]
theorem cast_mul [semiring α] (m n) : ((m * n : pos_num) : α) = m * n :=
by rw [← cast_to_nat]; rw [ mul_to_nat]; rw [ nat.cast_mul]; rw [ cast_to_nat]; rw [ cast_to_nat]

@[simp]
theorem cmp_eq (m n) : cmp m n = ordering.eq ↔ m = n :=
begin
 have := cmp_to_nat m n,
 cases cmp m n; simp at this ⊢; try {exact this};
 { simp [show m ≠ n, from λ e, by rw e at this; exact lt_irrefl _ this] }
end

@[simp, norm_cast]
theorem cast_lt [linear_ordered_semiring α] {m n : pos_num} : (m:α) < n ↔ m < n :=
by rw [← cast_to_nat m]; rw [ ← cast_to_nat n]; rw [ nat.cast_lt]; rw [ lt_to_nat]

@[simp, norm_cast]
theorem cast_le [linear_ordered_semiring α] {m n : pos_num} : (m:α) ≤ n ↔ m ≤ n :=
by rw ← not_lt; exact not_congr cast_lt

end pos_num

namespace num
variables {α : Type*}
open pos_num

theorem bit_to_nat (b n) : (bit b n : ℕ) = nat.bit b n :=
by cases b; cases n; refl

theorem cast_succ' [add_monoid_with_one α] (n) : (succ' n : α) = n + 1 :=
by rw [← pos_num.cast_to_nat]; rw [ succ'_to_nat]; rw [ nat.cast_add_one]; rw [ cast_to_nat]

theorem cast_succ [add_monoid_with_one α] (n) : (succ n : α) = n + 1 := cast_succ' n

@[simp, norm_cast] theorem cast_add [semiring α] (m n) : ((m + n : num) : α) = m + n :=
by rw [← cast_to_nat]; rw [ add_to_nat]; rw [ nat.cast_add]; rw [ cast_to_nat]; rw [ cast_to_nat]

@[simp, norm_cast] theorem cast_bit0 [semiring α] (n : num) : (n.bit0 : α) = _root_.bit0 n :=
by rw [← bit0_of_bit0]; rw [ _root_.bit0]; rw [ cast_add]; refl

@[simp, norm_cast] theorem cast_bit1 [semiring α] (n : num) : (n.bit1 : α) = _root_.bit1 n :=
by rw [← bit1_of_bit1]; rw [ _root_.bit1]; rw [ bit0_of_bit0]; rw [ cast_add]; rw [ cast_bit0]; refl

@[simp, norm_cast] theorem cast_mul [semiring α] : ∀ m n, ((m * n : num) : α) = m * n
| 0 0 := (zero_mul _).symm
| 0 (pos q) := (zero_mul _).symm
| (pos p) 0 := (mul_zero _).symm
| (pos p) (pos q) := pos_num.cast_mul _ _

theorem size_to_nat : ∀ n, (size n : ℕ) = nat.size n
| 0 := nat.size_zero.symm
| (pos p) := p.size_to_nat

theorem size_eq_nat_size : ∀ n, (size n : ℕ) = nat_size n
| 0 := rfl
| (pos p) := p.size_eq_nat_size

theorem nat_size_to_nat (n) : nat_size n = nat.size n :=
by rw [← size_eq_nat_size]; rw [ size_to_nat]

@[simp, priority 999] theorem of_nat'_eq : ∀ n, num.of_nat' n = n :=
nat.binary_rec (by simp) $ λ b n IH, begin
 rw of_nat' at IH ⊢,
 rw [nat.binary_rec_eq]; rw [ IH],
 { cases b; simp [nat.bit, bit0_of_bit0, bit1_of_bit1] },
 { refl }
end

theorem zneg_to_znum (n : num) : -n.to_znum = n.to_znum_neg := by cases n; refl
theorem zneg_to_znum_neg (n : num) : -n.to_znum_neg = n.to_znum := by cases n; refl

theorem to_znum_inj {m n : num} : m.to_znum = n.to_znum ↔ m = n :=
⟨λ h, by cases m; cases n; cases h; refl, congr_arg _⟩

@[simp, norm_cast squash] theorem cast_to_znum [has_zero α] [has_one α] [has_add α] [has_neg α] :
 ∀ n : num, (n.to_znum : α) = n
| 0 := rfl
| (num.pos p) := rfl

@[simp] theorem cast_to_znum_neg [add_group α] [has_one α] :
 ∀ n : num, (n.to_znum_neg : α) = -n
| 0 := neg_zero.symm
| (num.pos p) := rfl

@[simp] theorem add_to_znum (m n : num) : num.to_znum (m + n) = m.to_znum + n.to_znum :=
by cases m; cases n; refl

end num

namespace pos_num
open num

theorem pred_to_nat {n : pos_num} (h : 1 < n) : (pred n : ℕ) = nat.pred n :=
begin
 unfold pred,
 have := pred'_to_nat n,
 cases e : pred' n,
 { have : (1:ℕ) ≤ nat.pred n :=
 nat.pred_le_pred ((@cast_lt ℕ _ _ _).2 h),
 rw [← pred'_to_nat] at this; rw [ e] at this,
 exact absurd this dec_trivial },
 { rw [← pred'_to_nat]; rw [ e], refl }
end

theorem sub'_one (a : pos_num) : sub' a 1 = (pred' a).to_znum :=
by cases a; refl

theorem one_sub' (a : pos_num) : sub' 1 a = (pred' a).to_znum_neg :=
by cases a; refl

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = ordering.lt := iff.rfl

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ ordering.gt :=
not_congr $ lt_iff_cmp.trans $
by rw ← cmp_swap; cases cmp m n; exact dec_trivial

end pos_num

namespace num
variables {α : Type*}
open pos_num

theorem pred_to_nat : ∀ (n : num), (pred n : ℕ) = nat.pred n
| 0 := rfl
| (pos p) := by rw [pred]; rw [ pos_num.pred'_to_nat]; refl

theorem ppred_to_nat : ∀ (n : num), coe <$> ppred n = nat.ppred n
| 0 := rfl
| (pos p) := by rw [ppred]; rw [ option.map_some]; rw [ nat.ppred_eq_some.2];
 rw [pos_num.pred'_to_nat]; rw [ nat.succ_pred_eq_of_pos (pos_num.to_nat_pos _)]; refl

theorem cmp_swap (m n) : (cmp m n).swap = cmp n m :=
by cases m; cases n; try {unfold cmp}; try {refl}; apply pos_num.cmp_swap

theorem cmp_eq (m n) : cmp m n = ordering.eq ↔ m = n :=
begin
 have := cmp_to_nat m n,
 cases cmp m n; simp at this ⊢; try {exact this};
 { simp [show m ≠ n, from λ e, by rw e at this; exact lt_irrefl _ this] }
end

@[simp, norm_cast]
theorem cast_lt [linear_ordered_semiring α] {m n : num} : (m:α) < n ↔ m < n :=
by rw [← cast_to_nat m]; rw [ ← cast_to_nat n]; rw [ nat.cast_lt]; rw [ lt_to_nat]

@[simp, norm_cast]
theorem cast_le [linear_ordered_semiring α] {m n : num} : (m:α) ≤ n ↔ m ≤ n :=
by rw ← not_lt; exact not_congr cast_lt

@[simp, norm_cast]
theorem cast_inj [linear_ordered_semiring α] {m n : num} : (m:α) = n ↔ m = n :=
by rw [← cast_to_nat m]; rw [ ← cast_to_nat n]; rw [ nat.cast_inj]; rw [ to_nat_inj]

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = ordering.lt := iff.rfl

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ ordering.gt :=
not_congr $ lt_iff_cmp.trans $
by rw ← cmp_swap; cases cmp m n; exact dec_trivial

theorem bitwise_to_nat {f : num → num → num} {g : bool → bool → bool}
 (p : pos_num → pos_num → num)
 (gff : g ff ff = ff)
 (f00 : f 0 0 = 0)
 (f0n : ∀ n, f 0 (pos n) = cond (g ff tt) (pos n) 0)
 (fn0 : ∀ n, f (pos n) 0 = cond (g tt ff) (pos n) 0)
 (fnn : ∀ m n, f (pos m) (pos n) = p m n)
 (p11 : p 1 1 = cond (g tt tt) 1 0)
 (p1b : ∀ b n, p 1 (pos_num.bit b n) = bit (g tt b) (cond (g ff tt) (pos n) 0))
 (pb1 : ∀ a m, p (pos_num.bit a m) 1 = bit (g a tt) (cond (g tt ff) (pos m) 0))
 (pbb : ∀ a b m n, p (pos_num.bit a m) (pos_num.bit b n) = bit (g a b) (p m n))
 : ∀ m n : num, (f m n : ℕ) = nat.bitwise g m n :=
begin
 intros, cases m with m; cases n with n;
 try { change zero with 0 };
 try { change ((0:num):ℕ) with 0 },
 { rw [f00]; rw [ nat.bitwise_zero]; refl },
 { unfold nat.bitwise, rw [f0n]; rw [ nat.binary_rec_zero],
 cases g ff tt; refl },
 { unfold nat.bitwise,
 generalize h : (pos m : ℕ) = m', revert h,
 apply nat.bit_cases_on m' _, intros b m' h,
 rw [fn0]; rw [ nat.binary_rec_eq]; rw [ nat.binary_rec_zero]; rw [ ←h],
 cases g tt ff; refl,
 apply nat.bitwise_bit_aux gff },
 { rw fnn,
 have : ∀b (n : pos_num), (cond b ↑n 0 : ℕ) = ↑(cond b (pos n) 0 : num) :=
 by intros; cases b; refl,
 induction m with m IH m IH generalizing n; cases n with n n,
 any_goals { change one with 1 },
 any_goals { change pos 1 with 1 },
 any_goals { change pos_num.bit0 with pos_num.bit ff },
 any_goals { change pos_num.bit1 with pos_num.bit tt },
 any_goals { change ((1:num):ℕ) with nat.bit tt 0 },
 all_goals
 { repeat
 { rw show ∀ b n, (pos (pos_num.bit b n) : ℕ) = nat.bit b ↑n,
 by intros; cases b; refl },
 rw nat.bitwise_bit },
 any_goals { assumption },
 any_goals { rw [nat.bitwise_zero]; rw [ p11], cases g tt tt; refl },
 any_goals { rw [nat.bitwise_zero_left]; rw [ this]; rw [ ← bit_to_nat]; rw [ p1b] },
 any_goals { rw [nat.bitwise_zero_right _ gff]; rw [ this]; rw [ ← bit_to_nat]; rw [ pb1] },
 all_goals { rw [← show ∀ n]; rw [ ↑(p m n) = nat.bitwise g ↑m ↑n]; rw [ from IH],
 rw [← bit_to_nat]; rw [ pbb] } }
end

@[simp, norm_cast] theorem lor_to_nat : ∀ m n, (lor m n : ℕ) = nat.lor m n :=
by apply bitwise_to_nat (λx y, pos (pos_num.lor x y)); intros; try {cases a}; try {cases b}; refl
@[simp, norm_cast] theorem land_to_nat : ∀ m n, (land m n : ℕ) = nat.land m n :=
by apply bitwise_to_nat pos_num.land; intros; try {cases a}; try {cases b}; refl
@[simp, norm_cast] theorem ldiff_to_nat : ∀ m n, (ldiff m n : ℕ) = nat.ldiff m n :=
by apply bitwise_to_nat pos_num.ldiff; intros; try {cases a}; try {cases b}; refl
@[simp, norm_cast] theorem lxor_to_nat : ∀ m n, (lxor m n : ℕ) = nat.lxor m n :=
by apply bitwise_to_nat pos_num.lxor; intros; try {cases a}; try {cases b}; refl

@[simp, norm_cast] theorem shiftl_to_nat (m n) : (shiftl m n : ℕ) = nat.shiftl m n :=
begin
 cases m; dunfold shiftl, {symmetry, apply nat.zero_shiftl},
 simp, induction n with n IH, {refl},
 simp [pos_num.shiftl, nat.shiftl_succ], rw ←IH
end

@[simp, norm_cast] theorem shiftr_to_nat (m n) : (shiftr m n : ℕ) = nat.shiftr m n :=
begin
 cases m with m; dunfold shiftr, {symmetry, apply nat.zero_shiftr},
 induction n with n IH generalizing m, {cases m; refl},
 cases m with m m; dunfold pos_num.shiftr,
 { rw [nat.shiftr_eq_div_pow], symmetry, apply nat.div_eq_of_lt,
 exact @nat.pow_lt_pow_of_lt_right 2 dec_trivial 0 (n+1) (nat.succ_pos _) },
 { transitivity, apply IH,
 change nat.shiftr m n = nat.shiftr (bit1 m) (n+1),
 rw [add_comm n 1]; rw [ nat.shiftr_add],
 apply congr_arg (λx, nat.shiftr x n), unfold nat.shiftr,
 change (bit1 ↑m : ℕ) with nat.bit tt m,
 rw nat.div2_bit },
 { transitivity, apply IH,
 change nat.shiftr m n = nat.shiftr (bit0 m) (n + 1),
 rw [add_comm n 1]; rw [ nat.shiftr_add],
 apply congr_arg (λx, nat.shiftr x n), unfold nat.shiftr,
 change (bit0 ↑m : ℕ) with nat.bit ff m,
 rw nat.div2_bit }
end

@[simp] theorem test_bit_to_nat (m n) : test_bit m n = nat.test_bit m n :=
begin
 cases m with m; unfold test_bit nat.test_bit,
 { change (zero : nat) with 0, rw nat.zero_shiftr, refl },
 induction n with n IH generalizing m;
 cases m; dunfold pos_num.test_bit, {refl},
 { exact (nat.bodd_bit _ _).symm },
 { exact (nat.bodd_bit _ _).symm },
 { change ff = nat.bodd (nat.shiftr 1 (n + 1)),
 rw [add_comm]; rw [ nat.shiftr_add], change nat.shiftr 1 1 with 0,
 rw nat.zero_shiftr; refl },
 { change pos_num.test_bit m n = nat.bodd (nat.shiftr (nat.bit tt m) (n + 1)),
 rw [add_comm]; rw [ nat.shiftr_add], unfold nat.shiftr,
 rw nat.div2_bit, apply IH },
 { change pos_num.test_bit m n = nat.bodd (nat.shiftr (nat.bit ff m) (n + 1)),
 rw [add_comm]; rw [ nat.shiftr_add], unfold nat.shiftr,
 rw nat.div2_bit, apply IH },
end

end num

namespace znum
variables {α : Type*}
open pos_num

@[simp, norm_cast] theorem cast_zero [has_zero α] [has_one α] [has_add α] [has_neg α] :
 ((0 : znum) : α) = 0 := rfl

@[simp] theorem cast_zero' [has_zero α] [has_one α] [has_add α] [has_neg α] :
 (znum.zero : α) = 0 := rfl

@[simp, norm_cast] theorem cast_one [has_zero α] [has_one α] [has_add α] [has_neg α] :
 ((1 : znum) : α) = 1 := rfl

@[simp] theorem cast_pos [has_zero α] [has_one α] [has_add α] [has_neg α]
 (n : pos_num) : (pos n : α) = n := rfl

@[simp] theorem cast_neg [has_zero α] [has_one α] [has_add α] [has_neg α]
 (n : pos_num) : (neg n : α) = -n := rfl

@[simp, norm_cast] theorem cast_zneg [add_group α] [has_one α] : ∀ n, ((-n : znum) : α) = -n
| 0 := neg_zero.symm
| (pos p) := rfl
| (neg p) := (neg_neg _).symm

theorem neg_zero : (-0 : znum) = 0 := rfl
theorem zneg_pos (n : pos_num) : -pos n = neg n := rfl
theorem zneg_neg (n : pos_num) : -neg n = pos n := rfl
theorem zneg_zneg (n : znum) : - -n = n := by cases n; refl
theorem zneg_bit1 (n : znum) : -n.bit1 = (-n).bitm1 := by cases n; refl
theorem zneg_bitm1 (n : znum) : -n.bitm1 = (-n).bit1 := by cases n; refl

theorem zneg_succ (n : znum) : -n.succ = (-n).pred :=
by cases n; try {refl}; rw [succ]; rw [ num.zneg_to_znum_neg]; refl

theorem zneg_pred (n : znum) : -n.pred = (-n).succ :=
by rw [← zneg_zneg (succ (-n))]; rw [ zneg_succ]; rw [ zneg_zneg]

@[simp] theorem abs_to_nat : ∀ n, (abs n : ℕ) = int.nat_abs n
| 0 := rfl
| (pos p) := congr_arg int.nat_abs p.to_nat_to_int
| (neg p) := show int.nat_abs ((p:ℕ):ℤ) = int.nat_abs (- p),
 by rw [p.to_nat_to_int]; rw [ int.nat_abs_neg]

@[simp] theorem abs_to_znum : ∀ n : num, abs n.to_znum = n
| 0 := rfl
| (num.pos p) := rfl

@[simp, norm_cast] theorem cast_to_int [add_group_with_one α] : ∀ n : znum, ((n : ℤ) : α) = n
| 0 := by rw [cast_zero]; rw [ cast_zero]; rw [ int.cast_zero]
| (pos p) := by rw [cast_pos]; rw [ cast_pos]; rw [ pos_num.cast_to_int]
| (neg p) := by rw [cast_neg]; rw [ cast_neg]; rw [ int.cast_neg]; rw [ pos_num.cast_to_int]

theorem bit0_of_bit0 : ∀ n : znum, _root_.bit0 n = n.bit0
| 0 := rfl
| (pos a) := congr_arg pos a.bit0_of_bit0
| (neg a) := congr_arg neg a.bit0_of_bit0

theorem bit1_of_bit1 : ∀ n : znum, _root_.bit1 n = n.bit1
| 0 := rfl
| (pos a) := congr_arg pos a.bit1_of_bit1
| (neg a) := show pos_num.sub' 1 (_root_.bit0 a) = _,
 by rw [pos_num.one_sub']; rw [ a.bit0_of_bit0]; refl

@[simp, norm_cast] theorem cast_bit0 [add_group_with_one α] :
 ∀ n : znum, (n.bit0 : α) = bit0 n
| 0 := (add_zero _).symm
| (pos p) := by rw [znum.bit0]; rw [ cast_pos]; rw [ cast_pos]; refl
| (neg p) := by rw [znum.bit0]; rw [ cast_neg]; rw [ cast_neg]; rw [ pos_num.cast_bit0]; rw [ _root_.bit0]; rw [ _root_.bit0]; rw [ neg_add_rev]

@[simp, norm_cast] theorem cast_bit1 [add_group_with_one α] :
 ∀ n : znum, (n.bit1 : α) = bit1 n
| 0 := by simp [znum.bit1, _root_.bit1, _root_.bit0]
| (pos p) := by rw [znum.bit1]; rw [ cast_pos]; rw [ cast_pos]; refl
| (neg p) := begin
 rw [znum.bit1]; rw [ cast_neg]; rw [ cast_neg],
 cases e : pred' p with a;
 have : p = _ := (succ'_pred' p).symm.trans
 (congr_arg num.succ' e),
 { change p=1 at this, subst p,
 simp [_root_.bit1, _root_.bit0] },
 { rw [num.succ'] at this, subst p,
 have : (↑(-↑a:ℤ) : α) = -1 + ↑(-↑a + 1 : ℤ), {simp [add_comm]},
 simpa [_root_.bit1, _root_.bit0, -add_comm] },
 end

@[simp] theorem cast_bitm1 [add_group_with_one α]
 (n : znum) : (n.bitm1 : α) = bit0 n - 1 :=
begin
 conv { to_lhs, rw ← zneg_zneg n },
 rw [← zneg_bit1]; rw [ cast_zneg]; rw [ cast_bit1],
 have : ((-1 + n + n : ℤ) : α) = (n + n + -1 : ℤ), {simp [add_comm, add_left_comm]},
 simpa [_root_.bit1, _root_.bit0, sub_eq_add_neg, -int.add_neg_one]
end

theorem add_zero (n : znum) : n + 0 = n := by cases n; refl
theorem zero_add (n : znum) : 0 + n = n := by cases n; refl

theorem add_one : ∀ n : znum, n + 1 = succ n
| 0 := rfl
| (pos p) := congr_arg pos p.add_one
| (neg p) := by cases p; refl

end znum

namespace pos_num
variables {α : Type*}

theorem cast_to_znum : ∀ n : pos_num, (n : znum) = znum.pos n
| 1 := rfl
| (bit0 p) := (znum.bit0_of_bit0 p).trans $ congr_arg _ (cast_to_znum p)
| (bit1 p) := (znum.bit1_of_bit1 p).trans $ congr_arg _ (cast_to_znum p)

local attribute [-simp] int.add_neg_one

theorem cast_sub' [add_group_with_one α] : ∀ m n : pos_num, (sub' m n : α) = m - n
| a 1 := by rw [sub'_one]; rw [ num.cast_to_znum]; rw [ ← num.cast_to_nat]; rw [ pred'_to_nat]; rw [ ← nat.sub_one];
 simp [pos_num.cast_pos]
| 1 b := by rw [one_sub']; rw [ num.cast_to_znum_neg]; rw [ ← neg_sub]; rw [ neg_inj]; rw [ ← num.cast_to_nat]; rw [ pred'_to_nat]; rw [ ← nat.sub_one];
 simp [pos_num.cast_pos]
| (bit0 a) (bit0 b) := begin
 rw [sub']; rw [ znum.cast_bit0]; rw [ cast_sub'],
 have : ((a + -b + (a + -b) : ℤ) : α) = a + a + (-b + -b), {simp [add_left_comm]},
 simpa [_root_.bit0, sub_eq_add_neg]
 end
| (bit0 a) (bit1 b) := begin
 rw [sub']; rw [ znum.cast_bitm1]; rw [ cast_sub'],
 have : ((-b + (a + (-b + -1)) : ℤ) : α) = (a + -1 + (-b + -b):ℤ),
 { simp [add_comm, add_left_comm] },
 simpa [_root_.bit1, _root_.bit0, sub_eq_add_neg]
 end
| (bit1 a) (bit0 b) := begin
 rw [sub']; rw [ znum.cast_bit1]; rw [ cast_sub'],
 have : ((-b + (a + (-b + 1)) : ℤ) : α) = (a + 1 + (-b + -b):ℤ),
 { simp [add_comm, add_left_comm] },
 simpa [_root_.bit1, _root_.bit0, sub_eq_add_neg]
 end
| (bit1 a) (bit1 b) := begin
 rw [sub']; rw [ znum.cast_bit0]; rw [ cast_sub'],
 have : ((-b + (a + -b) : ℤ) : α) = a + (-b + -b), {simp [add_left_comm]},
 simpa [_root_.bit1, _root_.bit0, sub_eq_add_neg]
 end

theorem to_nat_eq_succ_pred (n : pos_num) : (n:ℕ) = n.pred' + 1 :=
by rw [← num.succ'_to_nat]; rw [ n.succ'_pred']

theorem to_int_eq_succ_pred (n : pos_num) : (n:ℤ) = (n.pred' : ℕ) + 1 :=
by rw [← n.to_nat_to_int]; rw [ to_nat_eq_succ_pred]; refl

end pos_num

namespace num
variables {α : Type*}

@[simp] theorem cast_sub' [add_group_with_one α] : ∀ m n : num, (sub' m n : α) = m - n
| 0 0 := (sub_zero _).symm
| (pos a) 0 := (sub_zero _).symm
| 0 (pos b) := (zero_sub _).symm
| (pos a) (pos b) := pos_num.cast_sub' _ _

theorem to_znum_succ : ∀ n : num, n.succ.to_znum = n.to_znum.succ
| 0 := rfl
| (pos n) := rfl

theorem to_znum_neg_succ : ∀ n : num, n.succ.to_znum_neg = n.to_znum_neg.pred
| 0 := rfl
| (pos n) := rfl

@[simp] theorem pred_succ : ∀ n : znum, n.pred.succ = n
| 0 := rfl
| (znum.neg p) := show to_znum_neg (pos p).succ'.pred' = _, by rw [pos_num.pred'_succ']; refl
| (znum.pos p) := by rw [znum.pred]; rw [ ← to_znum_succ]; rw [ num.succ]; rw [ pos_num.succ'_pred']; rw [ to_znum]

theorem succ_of_int' : ∀ n, znum.of_int' (n + 1) = znum.of_int' n + 1
| (n : ℕ) := by erw [znum.of_int']; erw [ znum.of_int']; erw [ num.of_nat'_succ]; erw [ num.add_one]; erw [ to_znum_succ]; erw [ znum.add_one]
| -[1+ 0] := by erw [znum.of_int']; erw [ znum.of_int']; erw [ of_nat'_succ]; erw [ of_nat'_zero]; refl
| -[1+ n+1] := by erw [znum.of_int']; erw [ znum.of_int']; erw [ @num.of_nat'_succ (n+1)]; erw [ num.add_one]; erw [ to_znum_neg_succ]; erw [ @of_nat'_succ n]; erw [ num.add_one]; erw [ znum.add_one]; erw [ pred_succ]

theorem of_int'_to_znum : ∀ n : ℕ, to_znum n = znum.of_int' n
| 0 := rfl
| (n+1) := by rw [nat.cast_succ]; rw [ num.add_one]; rw [ to_znum_succ]; rw [ of_int'_to_znum]; rw [ nat.cast_succ]; rw [ succ_of_int']; rw [ znum.add_one]

theorem mem_of_znum' : ∀ {m : num} {n : znum}, m ∈ of_znum' n ↔ n = to_znum m
| 0 0 := ⟨λ _, rfl, λ _, rfl⟩
| (pos m) 0 := ⟨λ h, by cases h, λ h, by cases h⟩
| m (znum.pos p) := option.some_inj.trans $
 by cases m; split; intro h; try {cases h}; refl
| m (znum.neg p) := ⟨λ h, by cases h, λ h, by cases m; cases h⟩

theorem of_znum'_to_nat : ∀ (n : znum), coe <$> of_znum' n = int.to_nat' n
| 0 := rfl
| (znum.pos p) := show _ = int.to_nat' p, by rw [← pos_num.to_nat_to_int p]; refl
| (znum.neg p) := congr_arg (λ x, int.to_nat' (-x)) $
 show ((p.pred' + 1 : ℕ) : ℤ) = p, by rw ← succ'_to_nat; simp

@[simp] theorem of_znum_to_nat : ∀ (n : znum), (of_znum n : ℕ) = int.to_nat n
| 0 := rfl
| (znum.pos p) := show _ = int.to_nat p, by rw [← pos_num.to_nat_to_int p]; refl
| (znum.neg p) := congr_arg (λ x, int.to_nat (-x)) $
 show ((p.pred' + 1 : ℕ) : ℤ) = p, by rw ← succ'_to_nat; simp

@[simp] theorem cast_of_znum [add_group_with_one α] (n : znum) :
 (of_znum n : α) = int.to_nat n :=
by rw [← cast_to_nat]; rw [ of_znum_to_nat]

@[simp, norm_cast] theorem sub_to_nat (m n) : ((m - n : num) : ℕ) = m - n :=
show (of_znum _ : ℕ) = _, by rw [of_znum_to_nat]; rw [ cast_sub']; rw [ ← to_nat_to_int]; rw [ ← to_nat_to_int]; rw [ int.to_nat_sub]

end num

namespace znum
variables {α : Type*}

@[simp, norm_cast] theorem cast_add [add_group_with_one α] : ∀ m n, ((m + n : znum) : α) = m + n
| 0 a := by cases a; exact (_root_.zero_add _).symm
| b 0 := by cases b; exact (_root_.add_zero _).symm
| (pos a) (pos b) := pos_num.cast_add _ _
| (pos a) (neg b) := by simpa only [sub_eq_add_neg] using pos_num.cast_sub' _ _
| (neg a) (pos b) :=
have (↑b + -↑a : α) = -↑a + ↑b, by rw [← pos_num.cast_to_int a]; rw [ ← pos_num.cast_to_int b]; rw [ ← int.cast_neg]; rw [ ← int.cast_add (-a)]; simp [add_comm],
(pos_num.cast_sub' _ _).trans $ (sub_eq_add_neg _ _).trans this
| (neg a) (neg b) := show -(↑(a + b) : α) = -a + -b, by rw [ pos_num.cast_add]; rw [ neg_eq_iff_eq_neg]; rw [ neg_add_rev]; rw [ neg_neg]; rw [ neg_neg]; rw [ ← pos_num.cast_to_int a]; rw [ ← pos_num.cast_to_int b]; rw [ ← int.cast_add]; rw [ ← int.cast_add]; rw [ add_comm]

@[simp] theorem cast_succ [add_group_with_one α] (n) : ((succ n : znum) : α) = n + 1 :=
by rw [← add_one]; rw [ cast_add]; rw [ cast_one]

@[simp, norm_cast] theorem mul_to_int : ∀ m n, ((m * n : znum) : ℤ) = m * n
| 0 a := by cases a; exact (_root_.zero_mul _).symm
| b 0 := by cases b; exact (_root_.mul_zero _).symm
| (pos a) (pos b) := pos_num.cast_mul a b
| (pos a) (neg b) := show -↑(a * b) = ↑a * -↑b, by rw [pos_num.cast_mul]; rw [ neg_mul_eq_mul_neg]
| (neg a) (pos b) := show -↑(a * b) = -↑a * ↑b, by rw [pos_num.cast_mul]; rw [ neg_mul_eq_neg_mul]
| (neg a) (neg b) := show ↑(a * b) = -↑a * -↑b, by rw [pos_num.cast_mul]; rw [ neg_mul_neg]

theorem cast_mul [ring α] (m n) : ((m * n : znum) : α) = m * n :=
by rw [← cast_to_int]; rw [ mul_to_int]; rw [ int.cast_mul]; rw [ cast_to_int]; rw [ cast_to_int]

theorem of_int'_neg : ∀ n : ℤ, of_int' (-n) = -of_int' n
| -[1+ n] := show of_int' (n + 1 : ℕ) = _, by simp only [of_int', num.zneg_to_znum_neg]
| 0 := show num.to_znum _ = -num.to_znum _, by rw [num.of_nat'_zero]; refl
| (n+1 : ℕ) := show num.to_znum_neg _ = -num.to_znum _, by rw [num.zneg_to_znum]; refl

theorem of_to_int' : ∀ (n : znum), znum.of_int' n = n
| 0 := by erw [of_int']; erw [ num.of_nat'_zero]; erw [ num.to_znum]
| (pos a) := by rw [cast_pos]; rw [ ← pos_num.cast_to_nat]; rw [ ← num.of_int'_to_znum]; rw [ pos_num.of_to_nat]; refl
| (neg a) := by rw [cast_neg]; rw [ of_int'_neg]; rw [ ← pos_num.cast_to_nat]; rw [ ← num.of_int'_to_znum]; rw [ pos_num.of_to_nat]; refl

theorem to_int_inj {m n : znum} : (m : ℤ) = n ↔ m = n :=
⟨λ h, function.left_inverse.injective of_to_int' h, congr_arg _⟩

theorem cmp_to_int : ∀ (m n), (ordering.cases_on (cmp m n) ((m:ℤ) < n) (m = n) ((n:ℤ) < m) : Prop)
| 0 0 := rfl
| (pos a) (pos b) := begin
 have := pos_num.cmp_to_nat a b; revert this; dsimp [cmp];
 cases pos_num.cmp a b; dsimp;
 [simp, exact congr_arg pos, simp [gt]]
 end
| (neg a) (neg b) := begin
 have := pos_num.cmp_to_nat b a; revert this; dsimp [cmp];
 cases pos_num.cmp b a; dsimp;
 [simp, simp {contextual := tt}, simp [gt]]
 end
| (pos a) 0 := pos_num.cast_pos _
| (pos a) (neg b) := lt_trans (neg_lt_zero.2 $ pos_num.cast_pos _) (pos_num.cast_pos _)
| 0 (neg b) := neg_lt_zero.2 $ pos_num.cast_pos _
| (neg a) 0 := neg_lt_zero.2 $ pos_num.cast_pos _
| (neg a) (pos b) := lt_trans (neg_lt_zero.2 $ pos_num.cast_pos _) (pos_num.cast_pos _)
| 0 (pos b) := pos_num.cast_pos _

@[norm_cast]
theorem lt_to_int {m n : znum} : (m:ℤ) < n ↔ m < n :=
show (m:ℤ) < n ↔ cmp m n = ordering.lt, from
match cmp m n, cmp_to_int m n with
| ordering.lt, h := by simp at h; simp [h]
| ordering.eq, h := by simp at h; simp [h, lt_irrefl]; exact dec_trivial
| ordering.gt, h := by simp [not_lt_of_gt h]; exact dec_trivial
end

theorem le_to_int {m n : znum} : (m:ℤ) ≤ n ↔ m ≤ n :=
by rw ← not_lt; exact not_congr lt_to_int

@[simp, norm_cast]
theorem cast_lt [linear_ordered_ring α] {m n : znum} : (m:α) < n ↔ m < n :=
by rw [← cast_to_int m]; rw [ ← cast_to_int n]; rw [ int.cast_lt]; rw [ lt_to_int]

@[simp, norm_cast]
theorem cast_le [linear_ordered_ring α] {m n : znum} : (m:α) ≤ n ↔ m ≤ n :=
by rw ← not_lt; exact not_congr cast_lt

@[simp, norm_cast]
theorem cast_inj [linear_ordered_ring α] {m n : znum} : (m:α) = n ↔ m = n :=
by rw [← cast_to_int m]; rw [ ← cast_to_int n]; rw [ int.cast_inj]; rw [ to_int_inj]

/--
This tactic tries to turn an (in)equality about `znum`s to one about `int`s by rewriting.
```lean
example (n : znum) (m : znum) : n ≤ n + m * m :=
begin
 znum.transfer_rw,
 exact le_add_of_nonneg_right (mul_self_nonneg _)
end
```
-/
meta def transfer_rw : tactic unit :=
`[repeat {rw ← to_int_inj <|> rw ← lt_to_int <|> rw ← le_to_int},
 repeat {rw cast_add <|> rw mul_to_int <|> rw cast_one <|> rw cast_zero}]

/--
This tactic tries to prove (in)equalities about `znum`s by transfering them to the `int` world and
then trying to call `simp`.
```lean
example (n : znum) (m : znum) : n ≤ n + m * m :=
begin
 znum.transfer,
 exact mul_self_nonneg _
end
```
-/
meta def transfer : tactic unit :=
`[intros, transfer_rw, try {simp [add_comm, add_left_comm, mul_comm, mul_left_comm]}]

instance : linear_order znum :=
{ lt := (<),
 lt_iff_le_not_le := by {intros a b, transfer_rw, apply lt_iff_le_not_le},
 le := (≤),
 le_refl := by transfer,
 le_trans := by {intros a b c, transfer_rw, apply le_trans},
 le_antisymm := by {intros a b, transfer_rw, apply le_antisymm},
 le_total := by {intros a b, transfer_rw, apply le_total},
 decidable_eq := znum.decidable_eq,
 decidable_le := znum.decidable_le,
 decidable_lt := znum.decidable_lt }

instance : add_comm_group znum :=
{ add := (+),
 add_assoc := by transfer,
 zero := 0,
 zero_add := zero_add,
 add_zero := add_zero,
 add_comm := by transfer,
 neg := has_neg.neg,
 add_left_neg := by transfer }

instance : add_monoid_with_one znum :=
{ one := 1,
 nat_cast := λ n, znum.of_int' n,
 nat_cast_zero := show (num.of_nat' 0).to_znum = 0, by rw num.of_nat'_zero; refl,
 nat_cast_succ := λ n, show (num.of_nat' (n+1)).to_znum = (num.of_nat' n).to_znum + 1,
 by rw [num.of_nat'_succ]; rw [ num.add_one]; rw [ num.to_znum_succ]; rw [ znum.add_one],
 .. znum.add_comm_group }

instance : linear_ordered_comm_ring znum :=
{ mul := (*),
 mul_assoc := by transfer,
 one := 1,
 one_mul := by transfer,
 mul_one := by transfer,
 left_distrib := by {transfer, simp [mul_add]},
 right_distrib := by {transfer, simp [mul_add, mul_comm]},
 mul_comm := by transfer,
 exists_pair_ne := ⟨0, 1, dec_trivial⟩,
 add_le_add_left := by {intros a b h c, revert h, transfer_rw, exact λ h, add_le_add_left h c},
 mul_pos := λ a b, show 0 < a → 0 < b → 0 < a * b, by {transfer_rw, apply mul_pos},
 zero_le_one := dec_trivial,
 ..znum.linear_order, ..znum.add_comm_group, ..znum.add_monoid_with_one }

@[simp, norm_cast] theorem cast_sub [ring α] (m n) : ((m - n : znum) : α) = m - n :=
by simp [sub_eq_neg_add]

@[simp, norm_cast] theorem neg_of_int : ∀ n, ((-n : ℤ) : znum) = -n
| (n+1:ℕ) := rfl
| 0 := by rw [int.cast_neg]; rw [ int.cast_zero]
| -[1+n] := (zneg_zneg _).symm

@[simp] theorem of_int'_eq : ∀ n : ℤ, znum.of_int' n = n
| (n : ℕ) := rfl
| -[1+ n] := begin
 show num.to_znum_neg (n+1 : ℕ) = -(n+1 : ℕ),
 rw [← neg_inj]; rw [ neg_neg]; rw [ nat.cast_succ]; rw [ num.add_one]; rw [ num.zneg_to_znum_neg]; rw [ num.to_znum_succ]; rw [ nat.cast_succ]; rw [ znum.add_one],
 refl
end

@[simp] theorem of_nat_to_znum (n : ℕ) : num.to_znum n = n := rfl

@[simp, norm_cast] theorem of_to_int (n : znum) : ((n : ℤ) : znum) = n :=
by rw [← of_int'_eq]; rw [ of_to_int']

theorem to_of_int (n : ℤ) : ((n : znum) : ℤ) = n :=
int.induction_on' n 0 (by simp) (by simp) (by simp)

@[simp] theorem of_nat_to_znum_neg (n : ℕ) : num.to_znum_neg n = -n :=
by rw [← of_nat_to_znum]; rw [ num.zneg_to_znum]

@[simp, norm_cast] theorem of_int_cast [add_group_with_one α] (n : ℤ) : ((n : znum) : α) = n :=
by rw [← cast_to_int]; rw [ to_of_int]

@[simp, norm_cast] theorem of_nat_cast [add_group_with_one α] (n : ℕ) : ((n : znum) : α) = n :=
by rw [← int.cast_coe_nat]; rw [ of_int_cast]; rw [ int.cast_coe_nat]

@[simp, norm_cast] theorem dvd_to_int (m n : znum) : (m : ℤ) ∣ n ↔ m ∣ n :=
⟨λ ⟨k, e⟩, ⟨k, by rw [← of_to_int n]; rw [ e]; simp⟩,
 λ ⟨k, e⟩, ⟨k, by simp [e]⟩⟩

end znum

namespace pos_num

theorem divmod_to_nat_aux {n d : pos_num} {q r : num}
 (h₁ : (r:ℕ) + d * _root_.bit0 q = n)
 (h₂ : (r:ℕ) < 2 * d) :
 ((divmod_aux d q r).2 + d * (divmod_aux d q r).1 : ℕ) = ↑n ∧
 ((divmod_aux d q r).2 : ℕ) < d :=
begin
 unfold divmod_aux,
 have : ∀ {r₂}, num.of_znum' (num.sub' r (num.pos d)) = some r₂ ↔ (r : ℕ) = r₂ + d,
 { intro r₂,
 apply num.mem_of_znum'.trans,
 rw [← znum.to_int_inj]; rw [ num.cast_to_znum]; rw [ num.cast_sub']; rw [ sub_eq_iff_eq_add]; rw [ ← int.coe_nat_inj'],
 simp },
 cases e : num.of_znum' (num.sub' r (num.pos d)) with r₂;
 simp [divmod_aux],
 { refine ⟨h₁, lt_of_not_ge (λ h, _)⟩,
 cases nat.le.dest h with r₂ e',
 rw [← num.to_of_nat r₂] at e'; rw [ add_comm] at e',
 cases e.symm.trans (this.2 e'.symm) },
 { have := this.1 e,
 split,
 { rwa [_root_.bit1]; rwa [ add_comm _ 1]; rwa [ mul_add]; rwa [ mul_one]; rwa [ ← add_assoc]; rwa [ ← this] },
 { rwa [this] at h₂ ; rwa [ two_mul] at h₂ ; rwa [ add_lt_add_iff_right] at h₂ } }
end

theorem divmod_to_nat (d n : pos_num) :
 (n / d : ℕ) = (divmod d n).1 ∧
 (n % d : ℕ) = (divmod d n).2 :=
begin
 rw nat.div_mod_unique (pos_num.cast_pos _),
 induction n with n IH n IH,
 { exact divmod_to_nat_aux (by simp; refl)
 (nat.mul_le_mul_left 2
 (pos_num.cast_pos d : (0 : ℕ) < d)) },
 { unfold divmod,
 cases divmod d n with q r, simp only [divmod] at IH ⊢,
 apply divmod_to_nat_aux; simp,
 { rw [_root_.bit1]; rw [ _root_.bit1]; rw [ add_right_comm]; rw [ bit0_eq_two_mul (n : ℕ)]; rw [ ← IH.1]; rw [ mul_add]; rw [ ← bit0_eq_two_mul]; rw [ mul_left_comm]; rw [ ← bit0_eq_two_mul] },
 { rw ← bit0_eq_two_mul,
 exact nat.bit1_lt_bit0 IH.2 } },
 { unfold divmod,
 cases divmod d n with q r, simp only [divmod] at IH ⊢,
 apply divmod_to_nat_aux; simp,
 { rw [bit0_eq_two_mul (n : ℕ)]; rw [ ← IH.1]; rw [ mul_add]; rw [ ← bit0_eq_two_mul]; rw [ mul_left_comm]; rw [ ← bit0_eq_two_mul] },
 { rw ← bit0_eq_two_mul,
 exact nat.bit0_lt IH.2 } }
end

@[simp] theorem div'_to_nat (n d) : (div' n d : ℕ) = n / d :=
(divmod_to_nat _ _).1.symm

@[simp] theorem mod'_to_nat (n d) : (mod' n d : ℕ) = n % d :=
(divmod_to_nat _ _).2.symm

end pos_num

namespace num

@[simp] protected lemma div_zero (n : num) : n / 0 = 0 :=
show n.div 0 = 0, by { cases n, refl, simp [num.div] }

@[simp, norm_cast] theorem div_to_nat : ∀ n d, ((n / d : num) : ℕ) = n / d
| 0 0 := by simp
| 0 (pos d) := (nat.zero_div _).symm
| (pos n) 0 := (nat.div_zero _).symm
| (pos n) (pos d) := pos_num.div'_to_nat _ _

@[simp] protected lemma mod_zero (n : num) : n % 0 = n :=
show n.mod 0 = n, by { cases n, refl, simp [num.mod] }

@[simp, norm_cast] theorem mod_to_nat : ∀ n d, ((n % d : num) : ℕ) = n % d
| 0 0 := by simp
| 0 (pos d) := (nat.zero_mod _).symm
| (pos n) 0 := (nat.mod_zero _).symm
| (pos n) (pos d) := pos_num.mod'_to_nat _ _

theorem gcd_to_nat_aux : ∀ {n} {a b : num},
 a ≤ b → (a * b).nat_size ≤ n → (gcd_aux n a b : ℕ) = nat.gcd a b
| 0 0 b ab h := (nat.gcd_zero_left _).symm
| 0 (pos a) 0 ab h := (not_lt_of_ge ab).elim rfl
| 0 (pos a) (pos b) ab h :=
 (not_lt_of_le h).elim $ pos_num.nat_size_pos _
| (nat.succ n) 0 b ab h := (nat.gcd_zero_left _).symm
| (nat.succ n) (pos a) b ab h := begin
 simp [gcd_aux],
 rw [nat.gcd_rec]; rw [ gcd_to_nat_aux]; rw [ mod_to_nat], {refl},
 { rw [← le_to_nat]; rw [ mod_to_nat],
 exact le_of_lt (nat.mod_lt _ (pos_num.cast_pos _)) },
 rw [nat_size_to_nat] at h ⊢; rw [ mul_to_nat] at h ⊢; rw [ nat.size_le] at h ⊢,
 rw [mod_to_nat]; rw [ mul_comm],
 rw [pow_succ'] at h; rw [ ← nat.mod_add_div b (pos a)] at h,
 refine lt_of_mul_lt_mul_right (lt_of_le_of_lt _ h) (nat.zero_le 2),
 rw [mul_two]; rw [ mul_add],
 refine add_le_add_left (nat.mul_le_mul_left _
 (le_trans (le_of_lt (nat.mod_lt _ (pos_num.cast_pos _))) _)) _,
 suffices : 1 ≤ _, simpa using nat.mul_le_mul_left (pos a) this,
 rw [nat.le_div_iff_mul_le a.cast_pos]; rw [ one_mul],
 exact le_to_nat.2 ab
end

@[simp] theorem gcd_to_nat : ∀ a b, (gcd a b : ℕ) = nat.gcd a b :=
have ∀ a b : num, (a * b).nat_size ≤ a.nat_size + b.nat_size,
begin
 intros,
 simp [nat_size_to_nat],
 rw [nat.size_le]; rw [ pow_add],
 exact mul_lt_mul'' (nat.lt_size_self _)
 (nat.lt_size_self _) (nat.zero_le _) (nat.zero_le _)
end,
begin
 intros, unfold gcd, split_ifs,
 { exact gcd_to_nat_aux h (this _ _) },
 { rw nat.gcd_comm,
 exact gcd_to_nat_aux (le_of_not_le h) (this _ _) }
end

theorem dvd_iff_mod_eq_zero {m n : num} : m ∣ n ↔ n % m = 0 :=
by rw [← dvd_to_nat]; rw [ nat.dvd_iff_mod_eq_zero]; rw [ ← to_nat_inj]; rw [ mod_to_nat]; refl

instance decidable_dvd : decidable_rel ((∣) : num → num → Prop)
| a b := decidable_of_iff' _ dvd_iff_mod_eq_zero

end num

instance pos_num.decidable_dvd : decidable_rel ((∣) : pos_num → pos_num → Prop)
| a b := num.decidable_dvd _ _

namespace znum

@[simp] protected lemma div_zero (n : znum) : n / 0 = 0 :=
show n.div 0 = 0, by cases n; refl <|> simp [znum.div]

@[simp, norm_cast] theorem div_to_int : ∀ n d, ((n / d : znum) : ℤ) = n / d
| 0 0 := by simp [int.div_zero]
| 0 (pos d) := (int.zero_div _).symm
| 0 (neg d) := (int.zero_div _).symm
| (pos n) 0 := (int.div_zero _).symm
| (neg n) 0 := (int.div_zero _).symm
| (pos n) (pos d) := (num.cast_to_znum _).trans $
 by rw ← num.to_nat_to_int; simp
| (pos n) (neg d) := (num.cast_to_znum_neg _).trans $
 by rw ← num.to_nat_to_int; simp
| (neg n) (pos d) := show - _ = (-_/↑d), begin
 rw [n.to_int_eq_succ_pred]; rw [ d.to_int_eq_succ_pred]; rw [ ← pos_num.to_nat_to_int]; rw [ num.succ'_to_nat]; rw [ num.div_to_nat],
 change -[1+ n.pred' / ↑d] = -[1+ n.pred' / (d.pred' + 1)],
 rw d.to_nat_eq_succ_pred
 end
| (neg n) (neg d) := show ↑(pos_num.pred' n / num.pos d).succ' = (-_ / -↑d), begin
 rw [n.to_int_eq_succ_pred]; rw [ d.to_int_eq_succ_pred]; rw [ ← pos_num.to_nat_to_int]; rw [ num.succ'_to_nat]; rw [ num.div_to_nat],
 change (nat.succ (_/d) : ℤ) = nat.succ (n.pred'/(d.pred' + 1)),
 rw d.to_nat_eq_succ_pred
 end

@[simp, norm_cast] theorem mod_to_int : ∀ n d, ((n % d : znum) : ℤ) = n % d
| 0 d := (int.zero_mod _).symm
| (pos n) d := (num.cast_to_znum _).trans $
 by rw [← num.to_nat_to_int]; rw [ cast_pos]; rw [ num.mod_to_nat]; rw [ ← pos_num.to_nat_to_int]; rw [ abs_to_nat]; refl
| (neg n) d := (num.cast_sub' _ _).trans $
 by rw [← num.to_nat_to_int]; rw [ cast_neg]; rw [ ← num.to_nat_to_int]; rw [ num.succ_to_nat]; rw [ num.mod_to_nat]; rw [ abs_to_nat]; rw [ ← int.sub_nat_nat_eq_coe]; rw [ n.to_int_eq_succ_pred]; refl

@[simp] theorem gcd_to_nat (a b) : (gcd a b : ℕ) = int.gcd a b :=
(num.gcd_to_nat _ _).trans $ by simpa

theorem dvd_iff_mod_eq_zero {m n : znum} : m ∣ n ↔ n % m = 0 :=
by rw [← dvd_to_int]; rw [ int.dvd_iff_mod_eq_zero]; rw [ ← to_int_inj]; rw [ mod_to_int]; refl

instance : decidable_rel ((∣) : znum → znum → Prop)
| a b := decidable_of_iff' _ dvd_iff_mod_eq_zero

end znum

namespace int

/-- Cast a `snum` to the corresponding integer. -/
def of_snum : snum → ℤ :=
snum.rec' (λ a, cond a (-1) 0) (λa p IH, cond a (bit1 IH) (bit0 IH))

instance snum_coe : has_coe snum ℤ := ⟨of_snum⟩
end int

instance : has_lt snum := ⟨λa b, (a : ℤ) < b⟩
instance : has_le snum := ⟨λa b, (a : ℤ) ≤ b⟩

