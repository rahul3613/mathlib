/-
Copyright (c) 2022 Yaël Dillies, George Shakan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, George Shakan
-/
import combinatorics.double_counting
import data.finset.pointwise
import data.rat.nnrat

/-!
# The Plünnecke-Ruzsa inequality

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves Ruzsa's triangle inequality, the Plünnecke-Petridis lemma, and the Plünnecke-Ruzsa
inequality.

## Main declarations

* `finset.card_sub_mul_le_card_sub_mul_card_sub`: Ruzsa's triangle inequality, difference version.
* `finset.card_add_mul_le_card_add_mul_card_add`: Ruzsa's triangle inequality, sum version.
* `finset.pluennecke_petridis`: The Plünnecke-Petridis lemma.
* `finset.card_smul_div_smul_le`: The Plünnecke-Ruzsa inequality.

## References

* [Giorgis Petridis, *The Plünnecke-Ruzsa inequality: an overview*][petridis2014]
* [Terrence Tao, Van Vu, *Additive Combinatorics][tao-vu]
-/

open nat
open_locale nnrat pointwise

namespace finset
variables {α : Type*} [comm_group α] [decidable_eq α] {A B C : finset α}

/-- **Ruzsa's triangle inequality**. Division version. -/
@[to_additive card_sub_mul_le_card_sub_mul_card_sub
"**Ruzsa's triangle inequality**. Subtraction version."]
lemma card_div_mul_le_card_div_mul_card_div (A B C : finset α) :
  (A / C).card * B.card ≤ (A / B).card * (B / C).card :=
begin
  rw [←card_product (A / B), ←mul_one ((finset.product _ _).card)],
  refine card_mul_le_card_mul (λ b ac, ac.1 * ac.2 = b) (λ x hx, _)
    (λ x hx, card_le_one_iff.2 $ λ u v hu hv,
      ((mem_bipartite_below _).1 hu).2.symm.trans ((mem_bipartite_below _).1 hv).2),
  obtain ⟨a, c, ha, hc, rfl⟩ := mem_div.1 hx,
  refine card_le_card_of_inj_on (λ b, (a / b, b / c)) (λ b hb, _) (λ b₁ _ b₂ _ h, _),
  { rw mem_bipartite_above,
    exact ⟨mk_mem_product (div_mem_div ha hb) (div_mem_div hb hc), div_mul_div_cancel' _ _ _⟩ },
  { exact div_right_injective (prod.ext_iff.1 h).1 }
end

/-- **Ruzsa's triangle inequality**. Div-mul-mul version. -/
@[to_additive card_sub_mul_le_card_add_mul_card_add
"**Ruzsa's triangle inequality**. Sub-add-add version."]
lemma card_div_mul_le_card_mul_mul_card_mul (A B C : finset α) :
  (A / C).card * B.card ≤ (A * B).card * (B * C).card :=
begin
  rw [←div_inv_eq_mul, ←card_inv B, ←card_inv (B * C), mul_inv, ←div_eq_mul_inv],
  exact card_div_mul_le_card_div_mul_card_div _ _ _,
end

/-- **Ruzsa's triangle inequality**. Mul-div-div version. -/
@[to_additive card_add_mul_le_card_sub_mul_card_add
"**Ruzsa's triangle inequality**. Add-sub-sub version."]
lemma card_mul_mul_le_card_div_mul_card_mul (A B C : finset α) :
  (A * C).card * B.card ≤ (A / B).card * (B * C).card :=
by { rw [←div_inv_eq_mul, ←div_inv_eq_mul B], exact card_div_mul_le_card_div_mul_card_div _ _ _ }

/-- **Ruzsa's triangle inequality**. Mul-mul-div version. -/
@[to_additive card_add_mul_le_card_add_mul_card_sub
"**Ruzsa's triangle inequality**. Add-add-sub version."]
lemma card_mul_mul_le_card_mul_mul_card_div (A B C : finset α) :
  (A * C).card * B.card ≤ (A * B).card * (B / C).card :=
by { rw [←div_inv_eq_mul, div_eq_mul_inv B], exact card_div_mul_le_card_mul_mul_card_mul _ _ _ }

@[to_additive]
lemma mul_pluennecke_petridis (C : finset α)
  (hA : ∀ A' ⊆ A, (A * B).card * A'.card ≤ (A' * B).card * A.card) :
  (A * B * C).card * A.card ≤ (A * B).card * (A * C).card :=
begin
  induction C using finset.induction_on with x C hc ih,
  { simp },
  set A' := A ∩ (A * C / {x}) with hA',
  set C' := insert x C with hC',
  have h₀ : A' * {x} = (A * {x}) ∩ (A * C),
  { rw [hA', inter_mul_singleton, (is_unit_singleton x).div_mul_cancel] },
  have h₁ : A * B * C' = (A * B * C) ∪ (A * B * {x}) \ (A' * B * {x}),
  { rw [hC', insert_eq, union_comm, mul_union],
    refine (sup_sdiff_eq_sup _).symm,
    rw [mul_right_comm, mul_right_comm A, h₀],
    exact mul_subset_mul_right (inter_subset_right _ _) },
  have h₂ : A' * B * {x} ⊆ A * B * {x} :=
    mul_subset_mul_right (mul_subset_mul_right $ inter_subset_left _ _),
  have h₃ : (A * B * C').card ≤ (A * B * C).card + (A * B).card - (A' * B).card,
  { rw h₁,
    refine (card_union_le _ _).trans_eq _,
    rw [card_sdiff h₂, ←add_tsub_assoc_of_le (card_le_of_subset h₂), card_mul_singleton,
      card_mul_singleton] },
  refine (mul_le_mul_right' h₃ _).trans _,
  rw [tsub_mul, add_mul],
  refine (tsub_le_tsub (add_le_add_right ih _) $ hA _ $ inter_subset_left _ _).trans_eq _,
  rw [←mul_add, ←mul_tsub, ←hA', insert_eq, mul_union, ←card_mul_singleton A x,
    ←card_mul_singleton A' x, add_comm (card _), h₀,
    eq_tsub_of_add_eq (card_union_add_card_inter _ _)],
end

/-! ### Sum triangle inequality -/

-- Auxiliary lemma for Ruzsa's triangle sum inequality, and the Plünnecke-Ruzsa inequality.
@[to_additive]
private lemma mul_aux (hA : A.nonempty) (hAB : A ⊆ B)
  (h : ∀ A' ∈ B.powerset.erase ∅, ((A * C).card : ℚ≥0) / ↑(A.card) ≤ ((A' * C).card) / ↑(A'.card)) :
  ∀ A' ⊆ A, (A * C).card * A'.card ≤ (A' * C).card * A.card :=
begin
  rintro A' hAA',
  obtain rfl | hA' := A'.eq_empty_or_nonempty,
  { simp },
  have hA₀ : (0 : ℚ≥0) < A.card := cast_pos.2 hA.card_pos,
  have hA₀' : (0 : ℚ≥0) < A'.card := cast_pos.2 hA'.card_pos,
  exact_mod_cast (div_le_div_iff hA₀ hA₀').1 (h _ $ mem_erase_of_ne_of_mem hA'.ne_empty $
    mem_powerset.2 $ hAA'.trans hAB),
end

/-- **Ruzsa's triangle inequality**. Multiplication version. -/
@[to_additive card_add_mul_card_le_card_add_mul_card_add
"**Ruzsa's triangle inequality**. Addition version."]
lemma card_mul_mul_card_le_card_mul_mul_card_mul (A B C : finset α) :
  (A * C).card * B.card ≤ (A * B).card * (B * C).card :=
begin
  obtain rfl | hB := B.eq_empty_or_nonempty,
  { simp },
  have hB' : B ∈ B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _),
  obtain ⟨U, hU, hUA⟩ := exists_min_image (B.powerset.erase ∅) (λ U, (U * A).card/U.card : _ → ℚ≥0)
    ⟨B, hB'⟩,
  rw [mem_erase, mem_powerset, ←nonempty_iff_ne_empty] at hU,
  refine cast_le.1 (_ : (_ : ℚ≥0) ≤ _),
  push_cast,
  refine (le_div_iff $ by exact cast_pos.2 hB.card_pos).1 _,
  rw [mul_div_right_comm, mul_comm _ B],
  refine (cast_le.2 $ card_le_card_mul_left _ hU.1).trans _,
  refine le_trans _ (mul_le_mul (hUA _ hB') (cast_le.2 $ card_le_of_subset $
    mul_subset_mul_right hU.2) (zero_le _) $ zero_le _),
  rw [←mul_div_right_comm, ←mul_assoc],
  refine (le_div_iff $ by exact cast_pos.2 hU.1.card_pos).2 _,
  exact_mod_cast mul_pluennecke_petridis C (mul_aux hU.1 hU.2 hUA),
end

/-- **Ruzsa's triangle inequality**. Add-sub-sub version. -/
lemma card_mul_mul_le_card_div_mul_card_div (A B C : finset α) :
  (A * C).card * B.card ≤ (A / B).card * (B / C).card :=
begin
  rw [div_eq_mul_inv, ←card_inv B, ←card_inv (B / C), inv_div', div_inv_eq_mul],
  exact card_mul_mul_card_le_card_mul_mul_card_mul _ _ _,
end

/-- **Ruzsa's triangle inequality**. Sub-add-sub version. -/
lemma card_div_mul_le_card_mul_mul_card_div (A B C : finset α) :
  (A / C).card * B.card ≤ (A * B).card * (B / C).card :=
by { rw [div_eq_mul_inv, div_eq_mul_inv], exact card_mul_mul_card_le_card_mul_mul_card_mul _ _ _ }

/-- **Ruzsa's triangle inequality**. Sub-sub-add version. -/
lemma card_div_mul_le_card_div_mul_card_mul (A B C : finset α) :
  (A / C).card * B.card ≤ (A / B).card * (B * C).card :=
by { rw [←div_inv_eq_mul, div_eq_mul_inv], exact card_mul_mul_le_card_div_mul_card_div _ _ _ }


lemma card_add_nsmul_le {α : Type*} [add_comm_group α] [decidable_eq α] {A B : finset α}
  (hAB : ∀ A' ⊆ A, (A + B).card * A'.card ≤ (A' + B).card * A.card) (n : ℕ) :
  ((A + n • B).card : ℚ≥0) ≤ ((A + B).card / A.card) ^ n * A.card :=
begin
  obtain rfl | hA := A.eq_empty_or_nonempty,
  { simp },
  induction n with n ih,
  { simp },
  rw [succ_nsmul, ←add_assoc, pow_succ, mul_assoc, ←mul_div_right_comm, le_div_iff, ←cast_mul],
  swap, exact (cast_pos.2 hA.card_pos),
  refine (cast_le.2 $ add_pluennecke_petridis _ hAB).trans _,
  rw cast_mul,
  exact mul_le_mul_of_nonneg_left ih (zero_le _),
end

@[to_additive]
lemma card_mul_pow_le (hAB : ∀ A' ⊆ A, (A * B).card * A'.card ≤ (A' * B).card * A.card) (n : ℕ) :
  ((A * B ^ n).card : ℚ≥0) ≤ ((A * B).card / A.card) ^ n * A.card :=
begin
  obtain rfl | hA := A.eq_empty_or_nonempty,
  { simp },
  induction n with n ih,
  { simp },
  rw [pow_succ, ←mul_assoc, pow_succ, @mul_assoc ℚ≥0, ←mul_div_right_comm, le_div_iff, ←cast_mul],
  swap, exact (cast_pos.2 hA.card_pos),
  refine (cast_le.2 $ mul_pluennecke_petridis _ hAB).trans _,
  rw cast_mul,
  exact mul_le_mul_of_nonneg_left ih (zero_le _),
end

/-- The **Plünnecke-Ruzsa inequality**. Multiplication version. Note that this is genuinely harder
than the division version because we cannot use a double counting argument. -/
@[to_additive "The **Plünnecke-Ruzsa inequality**. Addition version. Note that this is genuinely
harder than the subtraction version because we cannot use a double counting argument."]
lemma card_pow_div_pow_le (hA : A.nonempty) (B : finset α) (m n : ℕ) :
  ((B ^ m / B ^ n).card : ℚ≥0) ≤ ((A * B).card / A.card) ^ (m + n) * A.card :=
begin
  have hA' : A ∈ A.powerset.erase ∅ := mem_erase_of_ne_of_mem hA.ne_empty (mem_powerset_self _),
  obtain ⟨C, hC, hCA⟩ := exists_min_image (A.powerset.erase ∅) (λ C, (C * B).card/C.card : _ → ℚ≥0)
    ⟨A, hA'⟩,
  rw [mem_erase, mem_powerset, ←nonempty_iff_ne_empty] at hC,
  refine (mul_le_mul_right $ cast_pos.2 hC.1.card_pos).1 _,
  norm_cast,
  refine (cast_le.2 $ card_div_mul_le_card_mul_mul_card_mul _ _ _).trans _,
  push_cast,
  rw mul_comm _ C,
  refine (mul_le_mul (card_mul_pow_le (mul_aux hC.1 hC.2 hCA) _)
    (card_mul_pow_le (mul_aux hC.1 hC.2 hCA) _) (zero_le _) $ zero_le _).trans _,
  rw [mul_mul_mul_comm, ←pow_add, ←mul_assoc],
  exact mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_of_le_left (zero_le _) (hCA _ hA') _)
    (cast_le.2 $ card_le_of_subset hC.2) (zero_le _) $ zero_le _) (zero_le _),
end

/-- The **Plünnecke-Ruzsa inequality**. Subtraction version. -/
@[to_additive "The **Plünnecke-Ruzsa inequality**. Subtraction version."]
lemma card_pow_div_pow_le' (hA : A.nonempty) (B : finset α) (m n : ℕ) :
  ((B ^ m / B ^ n).card : ℚ≥0) ≤ ((A / B).card / A.card) ^ (m + n) * A.card :=
begin
  rw [←card_inv, inv_div', ←inv_pow, ←inv_pow, div_eq_mul_inv A],
  exact card_pow_div_pow_le hA _ _ _,
end

/-- Special case of the **Plünnecke-Ruzsa inequality**. Multiplication version. -/
@[to_additive "Special case of the **Plünnecke-Ruzsa inequality**. Addition version."]
lemma card_pow_le (hA : A.nonempty) (B : finset α) (n : ℕ) :
  ((B ^ n).card : ℚ≥0) ≤ ((A * B).card / A.card) ^ n * A.card :=
by simpa only [pow_zero, div_one] using card_pow_div_pow_le hA _ _ 0

/-- Special case of the **Plünnecke-Ruzsa inequality**. Division version. -/
@[to_additive "Special case of the **Plünnecke-Ruzsa inequality**. Subtraction version."]
lemma card_pow_le' (hA : A.nonempty) (B : finset α) (n : ℕ) :
  ((B ^ n).card : ℚ≥0) ≤ ((A / B).card / A.card) ^ n * A.card :=
by simpa only [pow_zero, div_one] using card_pow_div_pow_le' hA _ _ 0

end finset
