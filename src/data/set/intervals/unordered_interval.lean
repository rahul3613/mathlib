/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import order.bounds.basic
import data.set.intervals.basic

/-!
# Intervals without endpoints ordering

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In any lattice `α`, we define `uIcc a b` to be `Icc (a ⊓ b) (a ⊔ b)`, which in a linear order is the
set of elements lying between `a` and `b`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `uIcc a b` is the same as `segment ℝ a b`.

In a product or pi type, `uIcc a b` is the smallest box containing `a` and `b`. For example,
`uIcc (1, -1) (-1, 1) = Icc (-1, -1) (1, 1)` is the square of vertices `(1, -1)`, `(-1, -1)`,
`(-1, 1)`, `(1, 1)`.

In `finset α` (seen as a hypercube of dimension `fintype.card α`), `uIcc a b` is the smallest
subcube containing both `a` and `b`.

## Notation

We use the localized notation `[a, b]` for `uIcc a b`. One can open the locale `interval` to
make the notation available.

-/

open function order_dual (to_dual of_dual)

variables {α β : Type*}

namespace set
section lattice
variables [lattice α] [lattice β] {a a₁ a₂ b b₁ b₂ c x : α}

/-- `uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` included.
Note that we define it more generally in a lattice as `set.Icc (a ⊓ b) (a ⊔ b)`. In a product type,
`uIcc` corresponds to the bounding box of the two elements. -/
def uIcc (a b : α) : set α := Icc (a ⊓ b) (a ⊔ b)

localized "notation (name := set.uIcc) `[`a `, ` b `]` := set.uIcc a b" in interval

@[simp] lemma dual_uIcc (a b : α) : [to_dual a, to_dual b] = of_dual ⁻¹' [a, b] := dual_Icc

@[simp] lemma uIcc_of_le (h : a ≤ b) : [a, b] = Icc a b :=
by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp] lemma uIcc_of_ge (h : b ≤ a) : [a, b] = Icc b a :=
by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]

lemma uIcc_comm (a b : α) : [a, b] = [b, a] := by simp_rw [uIcc, inf_comm, sup_comm]

lemma uIcc_of_lt (h : a < b) : [a, b] = Icc a b := uIcc_of_le h.le
lemma uIcc_of_gt (h : b < a) : [a, b] = Icc b a := uIcc_of_ge h.le

@[simp] lemma uIcc_self : [a, a] = {a} := by simp [uIcc]

@[simp] lemma nonempty_uIcc : [a, b].nonempty := nonempty_Icc.2 inf_le_sup

lemma Icc_subset_uIcc : Icc a b ⊆ [a, b] := Icc_subset_Icc inf_le_left le_sup_right
lemma Icc_subset_uIcc' : Icc b a ⊆ [a, b] := Icc_subset_Icc inf_le_right le_sup_left

@[simp] lemma left_mem_uIcc : a ∈ [a, b] := ⟨inf_le_left, le_sup_left⟩
@[simp] lemma right_mem_uIcc : b ∈ [a, b] := ⟨inf_le_right, le_sup_right⟩

lemma mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [a, b] := Icc_subset_uIcc ⟨ha, hb⟩
lemma mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [a, b] := Icc_subset_uIcc' ⟨hb, ha⟩

lemma uIcc_subset_uIcc (h₁ : a₁ ∈ [a₂, b₂]) (h₂ : b₁ ∈ [a₂, b₂]) : [a₁, b₁] ⊆ [a₂, b₂] :=
Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2)

lemma uIcc_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) : [a₁, b₁] ⊆ Icc a₂ b₂ :=
Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

lemma uIcc_subset_uIcc_iff_mem : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₁ ∈ [a₂, b₂] ∧ b₁ ∈ [a₂, b₂] :=
iff.intro (λh, ⟨h left_mem_uIcc, h right_mem_uIcc⟩) (λ h, uIcc_subset_uIcc h.1 h.2)

lemma uIcc_subset_uIcc_iff_le' : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
Icc_subset_Icc_iff inf_le_sup

lemma uIcc_subset_uIcc_right (h : x ∈ [a, b]) : [x, b] ⊆ [a, b] := uIcc_subset_uIcc h right_mem_uIcc
lemma uIcc_subset_uIcc_left (h : x ∈ [a, b]) : [a, x] ⊆ [a, b] := uIcc_subset_uIcc left_mem_uIcc h

lemma bdd_below_bdd_above_iff_subset_uIcc (s : set α) :
  bdd_below s ∧ bdd_above s ↔ ∃ a b, s ⊆ [a, b] :=
bdd_below_bdd_above_iff_subset_Icc.trans
  ⟨λ ⟨a, b, h⟩, ⟨a, b, λ x hx, Icc_subset_uIcc (h hx)⟩, λ ⟨a, b, h⟩, ⟨_, _, h⟩⟩

section prod

@[simp] lemma uIcc_prod_uIcc (a₁ a₂ : α) (b₁ b₂ : β) :
  [a₁, a₂] ×ˢ [b₁, b₂] = [(a₁, b₁), (a₂, b₂)] :=
Icc_prod_Icc _ _ _ _

lemma uIcc_prod_eq (a b : α × β) : [a, b] = [a.1, b.1] ×ˢ [a.2, b.2] := by simp

end prod

end lattice

open_locale interval

section distrib_lattice
variables [distrib_lattice α] {a a₁ a₂ b b₁ b₂ c x : α}

lemma eq_of_mem_uIcc_of_mem_uIcc (ha : a ∈ [b, c]) (hb : b ∈ [a, c]) : a = b :=
eq_of_inf_eq_sup_eq (inf_congr_right ha.1 hb.1) $ sup_congr_right ha.2 hb.2

lemma eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [a, c] → c ∈ [a, b] → b = c :=
by simpa only [uIcc_comm a] using eq_of_mem_uIcc_of_mem_uIcc

lemma uIcc_injective_right (a : α) : injective (λ b, uIcc b a) :=
λ b c h, by { rw ext_iff at h,
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc) }

lemma uIcc_injective_left (a : α) : injective (uIcc a) :=
by simpa only [uIcc_comm] using uIcc_injective_right a

end distrib_lattice

section linear_order
variables [linear_order α]

section lattice
variables [lattice β] {f : α → β} {s : set α} {a b : α}

lemma _root_.monotone_on.image_uIcc_subset (hf : monotone_on f (uIcc a b)) :
  f '' uIcc a b ⊆ uIcc (f a) (f b) :=
hf.image_Icc_subset.trans $
  by rw [hf.map_sup left_mem_uIcc right_mem_uIcc, hf.map_inf left_mem_uIcc right_mem_uIcc, uIcc]

lemma _root_.antitone_on.image_uIcc_subset (hf : antitone_on f (uIcc a b)) :
  f '' uIcc a b ⊆ uIcc (f a) (f b) :=
hf.image_Icc_subset.trans $
  by rw [hf.map_sup left_mem_uIcc right_mem_uIcc, hf.map_inf left_mem_uIcc right_mem_uIcc, uIcc]

lemma _root_.monotone.image_uIcc_subset (hf : monotone f) : f '' uIcc a b ⊆ uIcc (f a) (f b) :=
(hf.monotone_on _).image_uIcc_subset

lemma _root_.antitone.image_uIcc_subset (hf : antitone f) : f '' uIcc a b ⊆ uIcc (f a) (f b) :=
(hf.antitone_on _).image_uIcc_subset

end lattice

variables [linear_order β] {f : α → β} {s : set α} {a a₁ a₂ b b₁ b₂ c d x : α}

lemma Icc_min_max : Icc (min a b) (max a b) = [a, b] := rfl

lemma uIcc_of_not_le (h : ¬ a ≤ b) : [a, b] = Icc b a := uIcc_of_gt $ lt_of_not_ge h
lemma uIcc_of_not_ge (h : ¬ b ≤ a) : [a, b] = Icc a b := uIcc_of_lt $ lt_of_not_ge h

lemma uIcc_eq_union : [a, b] = Icc a b ∪ Icc b a := by rw [Icc_union_Icc', max_comm]; refl

lemma mem_uIcc : a ∈ [b, c] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]

lemma not_mem_uIcc_of_lt (ha : c < a) (hb : c < b) : c ∉ [a, b] :=
not_mem_Icc_of_lt $ lt_min_iff.mpr ⟨ha, hb⟩

lemma not_mem_uIcc_of_gt (ha : a < c) (hb : b < c) : c ∉ [a, b] :=
not_mem_Icc_of_gt $ max_lt_iff.mpr ⟨ha, hb⟩

lemma uIcc_subset_uIcc_iff_le :
  [a₁, b₁] ⊆ [a₂, b₂] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
uIcc_subset_uIcc_iff_le'

/-- A sort of triangle inequality. -/
lemma uIcc_subset_uIcc_union_uIcc : [a, c] ⊆ [a, b] ∪ [b, c] :=
λ x, by simp only [mem_uIcc, mem_union]; cases le_total a c; cases le_total x b; tauto

lemma monotone_or_antitone_iff_uIcc :
  monotone f ∨ antitone f ↔ ∀ a b c, c ∈ [a, b] → f c ∈ [f a, f b] :=
begin
  split,
  { rintro (hf | hf) a b c; simp_rw [←Icc_min_max, ←hf.map_min, ←hf.map_max],
    exacts [λ hc, ⟨hf hc.1, hf hc.2⟩, λ hc, ⟨hf hc.2, hf hc.1⟩] },
  contrapose!,
  rw not_monotone_not_antitone_iff_exists_le_le,
  rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩,
  { exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, λ h, h.2.not_lt $ max_lt hfab hfcb⟩ },
  { exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, λ h, h.1.not_lt $ lt_min hfba hfbc⟩ }
end

lemma monotone_on_or_antitone_on_iff_uIcc :
  monotone_on f s ∨ antitone_on f s ↔ ∀ a b c ∈ s, c ∈ [a, b] → f c ∈ [f a, f b] :=
by simp [monotone_on_iff_monotone, antitone_on_iff_antitone, monotone_or_antitone_iff_uIcc,
  mem_uIcc]

/-- The open-closed interval with unordered bounds. -/
def uIoc : α → α → set α := λ a b, Ioc (min a b) (max a b)

-- Below is a capital iota
localized "notation `Ι` := set.uIoc" in interval

@[simp] lemma uIoc_of_le (h : a ≤ b) : Ι a b = Ioc a b := by simp [uIoc, h]
@[simp] lemma uIoc_of_lt (h : b < a) : Ι a b = Ioc b a := by simp [uIoc, h.le]

lemma uIoc_eq_union : Ι a b = Ioc a b ∪ Ioc b a := by cases le_total a b; simp [uIoc, *]

lemma mem_uIoc : a ∈ Ι b c ↔ b < a ∧ a ≤ c ∨ c < a ∧ a ≤ b :=
by simp only [uIoc_eq_union, mem_union, mem_Ioc]

lemma not_mem_uIoc : a ∉ Ι b c ↔ a ≤ b ∧ a ≤ c ∨ c < a ∧ b < a :=
by { simp only [uIoc_eq_union, mem_union, mem_Ioc, not_lt, ←not_le], tauto }

@[simp] lemma left_mem_uIoc : a ∈ Ι a b ↔ b < a := by simp [mem_uIoc]
@[simp] lemma right_mem_uIoc : b ∈ Ι a b ↔ a < b := by simp [mem_uIoc]

lemma forall_uIoc_iff  {P : α → Prop} :
  (∀ x ∈ Ι a b, P x) ↔ (∀ x ∈ Ioc a b, P x) ∧ (∀ x ∈ Ioc b a, P x) :=
by simp only [uIoc_eq_union, mem_union, or_imp_distrib, forall_and_distrib]

lemma uIoc_subset_uIoc_of_uIcc_subset_uIcc (h : [a, b] ⊆ [c, d]) : Ι a b ⊆ Ι c d :=
Ioc_subset_Ioc (uIcc_subset_uIcc_iff_le.1 h).1 (uIcc_subset_uIcc_iff_le.1 h).2

lemma uIoc_swap (a b : α) : Ι a b = Ι b a := by simp only [uIoc, min_comm a b, max_comm a b]

lemma Ioc_subset_uIoc : Ioc a b ⊆ Ι a b := Ioc_subset_Ioc (min_le_left _ _) (le_max_right _ _)
lemma Ioc_subset_uIoc' : Ioc a b ⊆ Ι b a := Ioc_subset_Ioc (min_le_right _ _) (le_max_left _ _)

lemma eq_of_mem_uIoc_of_mem_uIoc : a ∈ Ι b c → b ∈ Ι a c → a = b :=
by simp_rw mem_uIoc; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩); apply le_antisymm;
  assumption <|> exact le_of_lt ‹_› <|> exact le_trans ‹_› (le_of_lt ‹_›)

lemma eq_of_mem_uIoc_of_mem_uIoc' : b ∈ Ι a c → c ∈ Ι a b → b = c :=
by simpa only [uIoc_swap a] using eq_of_mem_uIoc_of_mem_uIoc

lemma eq_of_not_mem_uIoc_of_not_mem_uIoc (ha : a ≤ c) (hb : b ≤ c) :
  a ∉ Ι b c → b ∉ Ι a c → a = b :=
by simp_rw not_mem_uIoc; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩); apply le_antisymm;
    assumption <|> exact le_of_lt ‹_› <|> cases not_le_of_lt ‹_› ‹_›

lemma uIoc_injective_right (a : α) : injective (λ b, Ι b a) :=
begin
  rintro b c h,
  rw ext_iff at h,
  obtain ha | ha := le_or_lt b a,
  { have hb := (h b).not,
    simp only [ha, left_mem_uIoc, not_lt, true_iff, not_mem_uIoc, ←not_le, and_true,
      not_true, false_and, not_false_iff, true_iff, or_false] at hb,
    refine hb.eq_of_not_lt (λ hc, _),
    simpa [ha, and_iff_right hc, ←@not_le _ _ _ a, -not_le] using h c },
  { refine eq_of_mem_uIoc_of_mem_uIoc ((h _).1 $ left_mem_uIoc.2 ha)
      ((h _).2 $ left_mem_uIoc.2 $ ha.trans_le _),
    simpa [ha, ha.not_le, mem_uIoc] using h b }
end

lemma uIoc_injective_left (a : α) : injective (Ι a) :=
by simpa only [uIoc_swap] using uIoc_injective_right a

end linear_order
end set
