/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sigma.lex
import order.bounded_order

/-!
# Orders on a sigma type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines two orders on a sigma type:
* The disjoint sum of orders. `a` is less `b` iff `a` and `b` are in the same summand and `a` is
  less than `b` there.
* The lexicographical order. `a` is less than `b` if its summand is strictly less than the summand
  of `b` or they are in the same summand and `a` is less than `b` there.

We make the disjoint sum of orders the default set of instances. The lexicographic order goes on a
type synonym.

## Notation

* `Σₗ i, α i`: Sigma type equipped with the lexicographic order. Type synonym of `Σ i, α i`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.psigma.order`: Lexicographic order on `Σₗ' i, α i`. Basically a twin of this file.
* `data.prod.lex`: Lexicographic order on `α × β`.

## TODO

Upgrade `equiv.sigma_congr_left`, `equiv.sigma_congr`, `equiv.sigma_assoc`,
`equiv.sigma_prod_of_equiv`, `equiv.sigma_equiv_prod`, ... to order isomorphisms.
-/

namespace sigma
variables {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders on `sigma` -/

/-- Disjoint sum of orders. `⟨i, a⟩ ≤ ⟨j, b⟩` iff `i = j` and `a ≤ b`. -/
inductive le [Π i, has_le (α i)] : Π a b : Σ i, α i, Prop
| fiber (i : ι) (a b : α i) : a ≤ b → le ⟨i, a⟩ ⟨i, b⟩

/-- Disjoint sum of orders. `⟨i, a⟩ < ⟨j, b⟩` iff `i = j` and `a < b`. -/
inductive lt [Π i, has_lt (α i)] : Π a b : Σ i, α i, Prop
| fiber (i : ι) (a b : α i) : a < b → lt ⟨i, a⟩ ⟨i, b⟩

instance [Π i, has_le (α i)] : has_le (Σ i, α i) := ⟨le⟩
instance [Π i, has_lt (α i)] : has_lt (Σ i, α i) := ⟨lt⟩

@[simp] lemma mk_le_mk_iff [Π i, has_le (α i)] {i : ι} {a b : α i} :
  (⟨i, a⟩ : sigma α) ≤ ⟨i, b⟩ ↔ a ≤ b :=
⟨λ ⟨_, _, _, h⟩, h, le.fiber _ _ _⟩

@[simp] lemma mk_lt_mk_iff [Π i, has_lt (α i)] {i : ι} {a b : α i} :
  (⟨i, a⟩ : sigma α) < ⟨i, b⟩ ↔ a < b :=
⟨λ ⟨_, _, _, h⟩, h, lt.fiber _ _ _⟩

lemma le_def [Π i, has_le (α i)] {a b : Σ i, α i} : a ≤ b ↔ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2 :=
begin
  split,
  { rintro ⟨i, a, b, h⟩,
    exact ⟨rfl, h⟩ },
  { obtain ⟨i, a⟩ := a,
    obtain ⟨j, b⟩ := b,
    rintro ⟨(rfl : i = j), h⟩,
    exact le.fiber _ _ _ h }
end

lemma lt_def [Π i, has_lt (α i)] {a b : Σ i, α i} : a < b ↔ ∃ h : a.1 = b.1, h.rec a.2 < b.2 :=
begin
  split,
  { rintro ⟨i, a, b, h⟩,
    exact ⟨rfl, h⟩ },
  { obtain ⟨i, a⟩ := a,
    obtain ⟨j, b⟩ := b,
    rintro ⟨(rfl : i = j), h⟩,
    exact lt.fiber _ _ _ h }
end

instance [Π i, preorder (α i)] : preorder (Σ i, α i) :=
{ le_refl := λ ⟨i, a⟩, le.fiber i a a le_rfl,
  le_trans := begin
    rintro _ _ _ ⟨i, a, b, hab⟩ ⟨_, _, c, hbc⟩,
    exact le.fiber i a c (hab.trans hbc),
  end,
  lt_iff_le_not_le := λ _ _, begin
    split,
    { rintro ⟨i, a, b, hab⟩,
      rwa [mk_le_mk_iff, mk_le_mk_iff, ←lt_iff_le_not_le] },
    { rintro ⟨⟨i, a, b, hab⟩, h⟩,
      rw mk_le_mk_iff at h,
      exact mk_lt_mk_iff.2 (hab.lt_of_not_le h) }
  end,
  .. sigma.has_le,
  .. sigma.has_lt }

instance [Π i, partial_order (α i)] : partial_order (Σ i, α i) :=
{ le_antisymm := begin
    rintro _ _ ⟨i, a, b, hab⟩ ⟨_, _, _, hba⟩,
    exact ext rfl (heq_of_eq $ hab.antisymm hba),
  end,
  .. sigma.preorder }

instance [Π i, preorder (α i)] [Π i, densely_ordered (α i)] : densely_ordered (Σ i, α i) :=
⟨begin
  rintro ⟨i, a⟩ ⟨_, _⟩ ⟨_, _, b, h⟩,
  obtain ⟨c, ha, hb⟩ := exists_between h,
  exact ⟨⟨i, c⟩, lt.fiber i a c ha, lt.fiber i c b hb⟩,
end⟩

/-! ### Lexicographical order on `sigma` -/

namespace lex

notation `Σₗ` binders `, ` r:(scoped p, _root_.lex (sigma p)) := r

/-- The lexicographical `≤` on a sigma type. -/
instance has_le [has_lt ι] [Π i, has_le (α i)] : has_le (Σₗ i, α i) := ⟨lex (<) (λ i, (≤))⟩

/-- The lexicographical `<` on a sigma type. -/
instance has_lt [has_lt ι] [Π i, has_lt (α i)] : has_lt (Σₗ i, α i) := ⟨lex (<) (λ i, (<))⟩

lemma le_def [has_lt ι] [Π i, has_le (α i)] {a b : Σₗ i, α i} :
  a ≤ b ↔ a.1 < b.1 ∨ ∃ (h : a.1 = b.1), h.rec a.2 ≤ b.2 := sigma.lex_iff

lemma lt_def [has_lt ι] [Π i, has_lt (α i)] {a b : Σₗ i, α i} :
  a < b ↔ a.1 < b.1 ∨ ∃ (h : a.1 = b.1), h.rec a.2 < b.2 := sigma.lex_iff

/-- The lexicographical preorder on a sigma type. -/
instance preorder [preorder ι] [Π i, preorder (α i)] : preorder (Σₗ i, α i) :=
{ le_refl := λ ⟨i, a⟩, lex.right a a le_rfl,
  le_trans := λ _ _ _, trans_of (lex (<) $ λ _, (≤)),
  lt_iff_le_not_le := begin
    refine λ a b, ⟨λ hab, ⟨hab.mono_right (λ i a b, le_of_lt), _⟩, _⟩,
    { rintro (⟨b, a, hji⟩ | ⟨b, a, hba⟩);
        obtain (⟨_, _, hij⟩ | ⟨_, _, hab⟩) := hab,
      { exact hij.not_lt hji },
      { exact lt_irrefl _ hji },
      { exact lt_irrefl _ hij },
      { exact hab.not_le hba } },
    { rintro ⟨⟨a, b, hij⟩ | ⟨a, b, hab⟩, hba⟩,
      { exact lex.left _ _ hij },
      { exact lex.right _ _ (hab.lt_of_not_le $ λ h, hba $ lex.right _ _ h) } }
  end,
  .. lex.has_le,
  .. lex.has_lt }

/-- The lexicographical partial order on a sigma type. -/
instance partial_order [preorder ι] [Π i, partial_order (α i)] :
  partial_order (Σₗ i, α i) :=
{ le_antisymm := λ _ _, antisymm_of (lex (<) $ λ _, (≤)),
  .. lex.preorder }

/-- The lexicographical linear order on a sigma type. -/
instance linear_order [linear_order ι] [Π i, linear_order (α i)] :
  linear_order (Σₗ i, α i) :=
{ le_total := total_of (lex (<) $ λ _, (≤)),
  decidable_eq := sigma.decidable_eq,
  decidable_le := lex.decidable _ _,
  .. lex.partial_order }

/-- The lexicographical linear order on a sigma type. -/
instance order_bot [partial_order ι] [order_bot ι] [Π i, preorder (α i)] [order_bot (α ⊥)] :
  order_bot (Σₗ i, α i) :=
{ bot := ⟨⊥, ⊥⟩,
  bot_le := λ ⟨a, b⟩, begin
    obtain rfl | ha := eq_bot_or_bot_lt a,
    { exact lex.right _ _ bot_le },
    { exact lex.left _ _ ha }
  end }

/-- The lexicographical linear order on a sigma type. -/
instance order_top [partial_order ι] [order_top ι] [Π i, preorder (α i)] [order_top (α ⊤)] :
  order_top (Σₗ i, α i) :=
{ top := ⟨⊤, ⊤⟩,
  le_top := λ ⟨a, b⟩, begin
    obtain rfl | ha := eq_top_or_lt_top a,
    { exact lex.right _ _ le_top },
    { exact lex.left _ _ ha }
  end }

/-- The lexicographical linear order on a sigma type. -/
instance bounded_order [partial_order ι] [bounded_order ι] [Π i, preorder (α i)]
  [order_bot (α ⊥)] [order_top (α ⊤)] :
  bounded_order (Σₗ i, α i) :=
{ .. lex.order_bot, .. lex.order_top }

instance densely_ordered [preorder ι] [densely_ordered ι] [Π i, nonempty (α i)]
  [Π i, preorder (α i)] [Π i, densely_ordered (α i)] :
  densely_ordered (Σₗ i, α i) :=
⟨begin
  rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩),
  { obtain ⟨k, hi, hj⟩ := exists_between h,
    obtain ⟨c⟩ : nonempty (α k) := infer_instance,
    exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩ },
  { obtain ⟨c, ha, hb⟩ := exists_between h,
    exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩ }
end⟩

instance densely_ordered_of_no_max_order [preorder ι] [Π i, preorder (α i)]
  [Π i, densely_ordered (α i)] [Π i, no_max_order (α i)] :
  densely_ordered (Σₗ i, α i) :=
⟨begin
  rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩),
  { obtain ⟨c, ha⟩ := exists_gt a,
    exact ⟨⟨i, c⟩, right _ _ ha, left _ _ h⟩ },
  { obtain ⟨c, ha, hb⟩ := exists_between h,
    exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩ }
end⟩

instance densely_ordered_of_no_min_order [preorder ι] [Π i, preorder (α i)]
  [Π i, densely_ordered (α i)] [Π i, no_min_order (α i)] :
  densely_ordered (Σₗ i, α i) :=
⟨begin
  rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩),
  { obtain ⟨c, hb⟩ := exists_lt b,
    exact ⟨⟨j, c⟩, left _ _ h, right _ _ hb⟩ },
  { obtain ⟨c, ha, hb⟩ := exists_between h,
    exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩ }
end⟩

instance no_max_order_of_nonempty [preorder ι] [Π i, preorder (α i)] [no_max_order ι]
  [Π i, nonempty (α i)] :
  no_max_order (Σₗ i, α i) :=
⟨begin
  rintro ⟨i, a⟩,
  obtain ⟨j, h⟩ := exists_gt i,
  obtain ⟨b⟩ : nonempty (α j) := infer_instance,
  exact ⟨⟨j, b⟩, left _ _ h⟩
end⟩

instance no_min_order_of_nonempty [preorder ι] [Π i, preorder (α i)] [no_max_order ι]
  [Π i, nonempty (α i)] :
  no_max_order (Σₗ i, α i) :=
⟨begin
  rintro ⟨i, a⟩,
  obtain ⟨j, h⟩ := exists_gt i,
  obtain ⟨b⟩ : nonempty (α j) := infer_instance,
  exact ⟨⟨j, b⟩, left _ _ h⟩
end⟩

instance no_max_order [preorder ι] [Π i, preorder (α i)] [Π i, no_max_order (α i)] :
  no_max_order (Σₗ i, α i) :=
⟨by { rintro ⟨i, a⟩, obtain ⟨b, h⟩ := exists_gt a, exact ⟨⟨i, b⟩, right _ _ h⟩ }⟩

instance no_min_order [preorder ι] [Π i, preorder (α i)] [Π i, no_min_order (α i)] :
  no_min_order (Σₗ i, α i) :=
⟨by { rintro ⟨i, a⟩, obtain ⟨b, h⟩ := exists_lt a, exact ⟨⟨i, b⟩, right _ _ h⟩ }⟩

end lex
end sigma
