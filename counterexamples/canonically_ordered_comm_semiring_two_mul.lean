/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.zmod.basic
import ring_theory.subsemiring.basic
import algebra.order.monoid.basic
/-!

A `canonically_ordered_comm_semiring` with two different elements `a` and `b` such that
`a ≠ b` and `2 * a = 2 * b`. Thus, multiplication by a fixed non-zero element of a canonically
ordered semiring need not be injective. In particular, multiplying by a strictly positive element
need not be strictly monotone.

Recall that a `canonically_ordered_comm_semiring` is a commutative semiring with a partial ordering
that is "canonical" in the sense that the inequality `a ≤ b` holds if and only if there is a `c`
such that `a + c = b`. There are several compatibility conditions among addition/multiplication
and the order relation. The point of the counterexample is to show that monotonicity of
multiplication cannot be strengthened to **strict** monotonicity.

Reference:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/canonically_ordered.20pathology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace counterexample

namespace from_Bhavik

/-- Bhavik Mehta's example. There are only the initial definitions, but no proofs. The Type
`K` is a canonically ordered commutative semiring with the property that `2 * (1/2) ≤ 2 * 1`, even
though it is not true that `1/2 ≤ 1`, since `1/2` and `1` are not comparable. -/
@[derive [comm_semiring]]
def K : Type := subsemiring.closure ({1.5} : set ℚ)

instance : has_coe K ℚ := ⟨λ x, x.1⟩

instance inhabited_K : inhabited K := ⟨0⟩

instance : preorder K :=
{ le := λ x y, x = y ∨ (x : ℚ) + 1 ≤ (y : ℚ),
 le_refl := λ x, or.inl rfl,
 le_trans := λ x y z xy yz,
 begin
 rcases xy with (rfl | _), { apply yz },
 rcases yz with (rfl | _), { right, apply xy },
 right,
 exact xy.trans (le_trans ((le_add_iff_nonneg_right _).mpr zero_le_one) yz)
 end }

end from_Bhavik

lemma mem_zmod_2 (a : zmod 2) : a = 0 ∨ a = 1 :=
begin
 rcases a with ⟨_|_, _|_|_|_⟩,
 { exact or.inl rfl },
 { exact or.inr rfl },
end

lemma add_self_zmod_2 (a : zmod 2) : a + a = 0 :=
begin
 rcases mem_zmod_2 a with rfl | rfl;
 refl,
end

namespace Nxzmod_2

variables {a b : ℕ × zmod 2}

/-- The preorder relation on `ℕ × ℤ/2ℤ` where we only compare the first coordinate,
except that we leave incomparable each pair of elements with the same first component.
For instance, `∀ α, β ∈ ℤ/2ℤ`, the inequality `(1,α) ≤ (2,β)` holds,
whereas, `∀ n ∈ ℤ`, the elements `(n,0)` and `(n,1)` are incomparable. -/
instance preN2 : partial_order (ℕ × zmod 2) :=
{ le := λ x y, x = y ∨ x.1 < y.1,
 le_refl := λ a, or.inl rfl,
 le_trans := λ x y z xy yz,
 begin
 rcases xy with (rfl | _),
 { exact yz },
 { rcases yz with (rfl | _),
 { exact or.inr xy},
 { exact or.inr (xy.trans yz) } }
 end,
 le_antisymm := begin
 intros a b ab ba,
 cases ab with ab ab,
 { exact ab },
 { cases ba with ba ba,
 { exact ba.symm },
 { exact (nat.lt_asymm ab ba).elim } }
 end }

instance csrN2 : comm_semiring (ℕ × zmod 2) := by apply_instance

instance csrN2_1 : add_cancel_comm_monoid (ℕ × zmod 2) :=
{ add_left_cancel := λ a b c h, (add_right_inj a).mp h,
 ..Nxzmod_2.csrN2 }

/-- A strict inequality forces the first components to be different. -/
@[simp] lemma lt_def : a < b ↔ a.1 < b.1 :=
begin
 refine ⟨λ h, _, λ h, _⟩,
 { rcases h with ⟨(rfl | a1), h1⟩,
 { exact ((not_or_distrib.mp h1).1).elim rfl },
 { exact a1 } },
 refine ⟨or.inr h, not_or_distrib.mpr ⟨λ k, _, not_lt.mpr h.le⟩⟩,
 rw k at h,
 exact nat.lt_asymm h h
end

lemma add_left_cancel : ∀ (a b c : ℕ × zmod 2), a + b = a + c → b = c :=
λ a b c h, (add_right_inj a).mp h

lemma add_le_add_left : ∀ (a b : ℕ × zmod 2), a ≤ b → ∀ (c : ℕ × zmod 2), c + a ≤ c + b :=
begin
 rintros a b (rfl | ab) c,
 { refl },
 { exact or.inr (by simpa) }
end

lemma le_of_add_le_add_left : ∀ (a b c : ℕ × zmod 2), a + b ≤ a + c → b ≤ c :=
begin
 rintros a b c (bc | bc),
 { exact le_of_eq ((add_right_inj a).mp bc) },
 { exact or.inr (by simpa using bc) }
end

instance : zero_le_one_class (ℕ × zmod 2) := ⟨dec_trivial⟩

lemma mul_lt_mul_of_pos_left : ∀ (a b c : ℕ × zmod 2), a < b → 0 < c → c * a < c * b :=
λ a b c ab c0, lt_def.mpr ((mul_lt_mul_left (lt_def.mp c0)).mpr (lt_def.mp ab))

lemma mul_lt_mul_of_pos_right : ∀ (a b c : ℕ × zmod 2), a < b → 0 < c → a * c < b * c :=
λ a b c ab c0, lt_def.mpr ((mul_lt_mul_right (lt_def.mp c0)).mpr (lt_def.mp ab))

instance socsN2 : strict_ordered_comm_semiring (ℕ × zmod 2) :=
{ add_le_add_left := add_le_add_left,
 le_of_add_le_add_left := le_of_add_le_add_left,
 zero_le_one := zero_le_one,
 mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left,
 mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right,
 ..Nxzmod_2.csrN2_1,
 ..(infer_instance : partial_order (ℕ × zmod 2)),
 ..(infer_instance : comm_semiring (ℕ × zmod 2)),
 ..pullback_nonzero prod.fst prod.fst_zero prod.fst_one }

end Nxzmod_2

namespace ex_L

open Nxzmod_2 subtype

/-- Initially, `L` was defined as the subsemiring closure of `(1,0)`. -/
def L : Type := { l : (ℕ × zmod 2) // l ≠ (0, 1) }

lemma add_L {a b : ℕ × zmod 2} (ha : a ≠ (0, 1)) (hb : b ≠ (0, 1)) :
 a + b ≠ (0, 1) :=
begin
 rcases a with ⟨a, a2⟩,
 rcases b with ⟨b, b2⟩,
 cases b,
 { rcases mem_zmod_2 b2 with rfl | rfl,
 { simp [ha] },
 { simpa only } },
 { simp [(a + b).succ_ne_zero] }
end

lemma mul_L {a b : ℕ × zmod 2} (ha : a ≠ (0, 1)) (hb : b ≠ (0, 1)) :
 a * b ≠ (0, 1) :=
begin
 rcases a with ⟨a, a2⟩,
 rcases b with ⟨b, b2⟩,
 cases b,
 { rcases mem_zmod_2 b2 with rfl | rfl;
 rcases mem_zmod_2 a2 with rfl | rfl;
 -- while this looks like a non-terminal `simp`, it (almost) isn't: there is only one goal where
 -- it does not finish the proof and on that goal it asks to prove `false`
 simp,
 exact hb rfl },
 cases a,
 { rcases mem_zmod_2 b2 with rfl | rfl;
 rcases mem_zmod_2 a2 with rfl | rfl;
 -- while this looks like a non-terminal `simp`, it (almost) isn't: there is only one goal where
 -- it does not finish the proof and on that goal it asks to prove `false`
 simp,
 exact ha rfl },
 { simp [mul_ne_zero _ _, nat.succ_ne_zero _] }
end

/-- The subsemiring corresponding to the elements of `L`, used to transfer instances. -/
def L_subsemiring : subsemiring (ℕ × zmod 2) :=
{ carrier := { l | l ≠ (0, 1) },
 zero_mem' := dec_trivial,
 one_mem' := dec_trivial,
 add_mem' := λ _ _, add_L,
 mul_mem' := λ _ _, mul_L }

instance : ordered_comm_semiring L :=
L_subsemiring.to_ordered_comm_semiring

instance inhabited : inhabited L := ⟨1⟩

lemma bot_le : ∀ (a : L), 0 ≤ a :=
begin
 rintros ⟨⟨an, a2⟩, ha⟩,
 cases an,
 { rcases mem_zmod_2 a2 with (rfl | rfl),
 { refl, },
 { exact (ha rfl).elim } },
 { refine or.inr _,
 exact nat.succ_pos _ }
end

instance order_bot : order_bot L := ⟨0, bot_le⟩

lemma exists_add_of_le : ∀ a b : L, a ≤ b → ∃ c, b = a + c :=
begin
 rintro a ⟨b, _⟩ (⟨rfl, rfl⟩ | h),
 { exact ⟨0, (add_zero _).symm⟩ },
 { exact ⟨⟨b - a.1, λ H, (tsub_pos_of_lt h).ne' (prod.mk.inj_iff.1 H).1⟩,
 subtype.ext $ prod.ext (add_tsub_cancel_of_le h.le).symm (add_sub_cancel'_right _ _).symm⟩ }
end

lemma le_self_add : ∀ a b : L, a ≤ a + b :=
begin
 rintro a ⟨⟨bn, b2⟩, hb⟩,
 obtain rfl | h := nat.eq_zero_or_pos bn,
 { obtain rfl | rfl := mem_zmod_2 b2,
 { exact or.inl (prod.ext (add_zero _).symm (add_zero _).symm) },
 { exact (hb rfl).elim } },
 { exact or.inr ((lt_add_iff_pos_right _).mpr h) }
end

lemma eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (a b : L), a * b = 0 → a = 0 ∨ b = 0 :=
begin
 rintros ⟨⟨a, a2⟩, ha⟩ ⟨⟨b, b2⟩, hb⟩ ab1,
 injection ab1 with ab,
 injection ab with abn ab2,
 rw mul_eq_zero at abn,
 rcases abn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
 { refine or.inl _,
 rcases mem_zmod_2 a2 with rfl | rfl,
 { refl },
 { exact (ha rfl).elim } },
 { refine or.inr _,
 rcases mem_zmod_2 b2 with rfl | rfl,
 { refl },
 { exact (hb rfl).elim } }
end

instance can : canonically_ordered_comm_semiring L :=
{ exists_add_of_le := exists_add_of_le,
 le_self_add := le_self_add,
 eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
 ..(infer_instance : order_bot L),
 ..(infer_instance : ordered_comm_semiring L) }

/--
The elements `(1,0)` and `(1,1)` of `L` are different, but their doubles coincide.
-/
example : ∃ a b : L, a ≠ b ∧ 2 * a = 2 * b :=
begin
 refine ⟨⟨(1,0), by simp⟩, 1, λ (h : (⟨(1, 0), _⟩ : L) = ⟨⟨1, 1⟩, _⟩), _, rfl⟩,
 obtain (F : (0 : zmod 2) = 1) := congr_arg (λ j : L, j.1.2) h,
 cases F,
end

end ex_L

end counterexample

