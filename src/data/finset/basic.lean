/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import data.multiset.finset_ops
import tactic.apply
import tactic.nth_rewrite
import tactic.monotonicity

/-!
# Finite sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Terms of type `finset α` are one way of talking about finite subsets of `α` in mathlib.
Below, `finset α` is defined as a structure with 2 fields:

 1. `val` is a `multiset α` of elements;
 2. `nodup` is a proof that `val` has no duplicates.

Finsets in Lean are constructive in that they have an underlying `list` that enumerates their
elements. In particular, any function that uses the data of the underlying list cannot depend on its
ordering. This is handled on the `multiset` level by multiset API, so in most cases one needn't
worry about it explicitly.

Finsets give a basic foundation for defining finite sums and products over types:

 1. `∑ i in (s : finset α), f i`;
 2. `∏ i in (s : finset α), f i`.

Lean refers to these operations as `big_operator`s.
More information can be found in `algebra.big_operators.basic`.

Finsets are directly used to define fintypes in Lean.
A `fintype α` instance for a type `α` consists of
a universal `finset α` containing every term of `α`, called `univ`. See `data.fintype.basic`.
There is also `univ'`, the noncomputable partner to `univ`,
which is defined to be `α` as a finset if `α` is finite,
and the empty finset otherwise. See `data.fintype.basic`.

`finset.card`, the size of a finset is defined in `data.finset.card`. This is then used to define
`fintype.card`, the size of a type.

## Main declarations

### Main definitions

* `finset`: Defines a type for the finite subsets of `α`.
 Constructing a `finset` requires two pieces of data: `val`, a `multiset α` of elements,
 and `nodup`, a proof that `val` has no duplicates.
* `finset.has_mem`: Defines membership `a ∈ (s : finset α)`.
* `finset.has_coe`: Provides a coercion `s : finset α` to `s : set α`.
* `finset.has_coe_to_sort`: Coerce `s : finset α` to the type of all `x ∈ s`.
* `finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `finset α`,
 it suffices to prove it for the empty finset, and to show that if it holds for some `finset α`,
 then it holds for the finset obtained by inserting a new element.
* `finset.choose`: Given a proof `h` of existence and uniqueness of a certain element
 satisfying a predicate, `choose s h` returns the element of `s` satisfying that predicate.

### Finset constructions

* `singleton`: Denoted by `{a}`; the finset consisting of one element.
* `finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.
* `finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ... , n - 1} ⊆ ℕ`.
 This convention is consistent with other languages and normalizes `card (range n) = n`.
 Beware, `n` is not in `range n`.
* `finset.attach`: Given `s : finset α`, `attach s` forms a finset of elements of the subtype
 `{a // a ∈ s}`; in other words, it attaches elements to a proof of membership in the set.

### Finsets from functions

* `finset.filter`: Given a predicate `p : α → Prop`, `s.filter p` is
 the finset consisting of those elements in `s` satisfying the predicate `p`.

### The lattice structure on subsets of finsets

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`order.lattice`. For the lattice structure on finsets, `⊥` is called `bot` with `⊥ = ∅` and `⊤` is
called `top` with `⊤ = univ`.

* `finset.has_subset`: Lots of API about lattices, otherwise behaves exactly as one would expect.
* `finset.has_union`: Defines `s ∪ t` (or `s ⊔ t`) as the union of `s` and `t`.
 See `finset.sup`/`finset.bUnion` for finite unions.
* `finset.has_inter`: Defines `s ∩ t` (or `s ⊓ t`) as the intersection of `s` and `t`.
 See `finset.inf` for finite intersections.
* `finset.disj_union`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
 `s.disj_union t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`; this does
 not require decidable equality on the type `α`.

### Operations on two or more finsets

* `insert` and `finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
 returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
 This does not require decidable equality on the type `α`.
* `finset.has_union`: see "The lattice structure on subsets of finsets"
* `finset.has_inter`: see "The lattice structure on subsets of finsets"
* `finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.
* `finset.has_sdiff`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `finset.product`: Given finsets of `α` and `β`, defines finsets of `α × β`.
 For arbitrary dependent products, see `data.finset.pi`.
* `finset.bUnion`: Finite unions of finsets; given an indexing function `f : α → finset β` and a
 `s : finset α`, `s.bUnion f` is the union of all finsets of the form `f a` for `a ∈ s`.
* `finset.bInter`: TODO: Implemement finite intersections.

### Maps constructed using finsets

* `finset.piecewise`: Given two functions `f`, `g`, `s.piecewise f g` is a function which is equal
 to `f` on `s` and `g` on the complement.

### Predicates on finsets

* `disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
 intersection is empty.
* `finset.nonempty`: A finset is nonempty if it has elements.
 This is equivalent to saying `s ≠ ∅`. TODO: Decide on the simp normal form.

### Equivalences between finsets

* The `data.equiv` files describe a general type of equivalence, so look in there for any lemmas.
 There is some API for rewriting sums and products from `s` to `t` given that `s ≃ t`.
 TODO: examples

## Tags

finite sets, finset

-/

open multiset subtype nat function

universes u

variables {α : Type*} {β : Type*} {γ : Type*}

/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
 as a multiset (a list up to permutation) which has no duplicate elements. -/
structure finset (α : Type*) :=
(val : multiset α)
(nodup : nodup val)

instance multiset.can_lift_finset {α} :
 can_lift (multiset α) (finset α) finset.val multiset.nodup :=
⟨λ m hm, ⟨⟨m, hm⟩, rfl⟩⟩

namespace finset

theorem eq_of_veq : ∀ {s t : finset α}, s.1 = t.1 → s = t
| ⟨s, _⟩ ⟨t, _⟩ rfl := rfl

theorem val_injective : injective (val : finset α → multiset α) := λ _ _, eq_of_veq

@[simp] theorem val_inj {s t : finset α} : s.1 = t.1 ↔ s = t := val_injective.eq_iff

@[simp] theorem dedup_eq_self [decidable_eq α] (s : finset α) : dedup s.1 = s.1 :=
s.2.dedup

instance has_decidable_eq [decidable_eq α] : decidable_eq (finset α)
| s₁ s₂ := decidable_of_iff _ val_inj

/-! ### membership -/

instance : has_mem α (finset α) := ⟨λ a s, a ∈ s.1⟩

theorem mem_def {a : α} {s : finset α} : a ∈ s ↔ a ∈ s.1 := iff.rfl
@[simp] lemma mem_val {a : α} {s : finset α} : a ∈ s.1 ↔ a ∈ s := iff.rfl

@[simp] theorem mem_mk {a : α} {s nd} : a ∈ @finset.mk α s nd ↔ a ∈ s := iff.rfl

instance decidable_mem [h : decidable_eq α] (a : α) (s : finset α) : decidable (a ∈ s) :=
multiset.decidable_mem _ _

/-! ### set coercion -/

/-- Convert a finset to a set in the natural way. -/
instance : has_coe_t (finset α) (set α) := ⟨λ s, {x | x ∈ s}⟩

@[simp, norm_cast] lemma mem_coe {a : α} {s : finset α} : a ∈ (s : set α) ↔ a ∈ s := iff.rfl

@[simp] lemma set_of_mem {α} {s : finset α} : {a | a ∈ s} = s := rfl

@[simp] lemma coe_mem {s : finset α} (x : (s : set α)) : ↑x ∈ s := x.2

@[simp] lemma mk_coe {s : finset α} (x : (s : set α)) {h} :
 (⟨x, h⟩ : (s : set α)) = x :=
subtype.coe_eta _ _

instance decidable_mem' [decidable_eq α] (a : α) (s : finset α) :
 decidable (a ∈ (s : set α)) := s.decidable_mem _

/-! ### extensionality -/
theorem ext_iff {s₁ s₂ : finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
val_inj.symm.trans $ s₁.nodup.ext s₂.nodup

@[ext]
theorem ext {s₁ s₂ : finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
ext_iff.2

@[simp, norm_cast] theorem coe_inj {s₁ s₂ : finset α} : (s₁ : set α) = s₂ ↔ s₁ = s₂ :=
set.ext_iff.trans ext_iff.symm

lemma coe_injective {α} : injective (coe : finset α → set α) :=
λ s t, coe_inj.1

/-! ### type coercion -/

/-- Coercion from a finset to the corresponding subtype. -/
instance {α : Type u} : has_coe_to_sort (finset α) (Type u) := ⟨λ s, {x // x ∈ s}⟩

@[simp] protected lemma forall_coe {α : Type*} (s : finset α) (p : s → Prop) :
 (∀ (x : s), p x) ↔ ∀ (x : α) (h : x ∈ s), p ⟨x, h⟩ := subtype.forall

@[simp] protected lemma exists_coe {α : Type*} (s : finset α) (p : s → Prop) :
 (∃ (x : s), p x) ↔ ∃ (x : α) (h : x ∈ s), p ⟨x, h⟩ := subtype.exists

instance pi_finset_coe.can_lift (ι : Type*) (α : Π i : ι, Type*) [ne : Π i, nonempty (α i)]
 (s : finset ι) :
 can_lift (Π i : s, α i) (Π i, α i) (λ f i, f i) (λ _, true) :=
pi_subtype.can_lift ι α (∈ s)

instance pi_finset_coe.can_lift' (ι α : Type*) [ne : nonempty α] (s : finset ι) :
 can_lift (s → α) (ι → α) (λ f i, f i) (λ _, true) :=
pi_finset_coe.can_lift ι (λ _, α) s

instance finset_coe.can_lift (s : finset α) : can_lift α s coe (λ a, a ∈ s) :=
{ prf := λ a ha, ⟨⟨a, ha⟩, rfl⟩ }

@[simp, norm_cast] lemma coe_sort_coe (s : finset α) :
 ((s : set α) : Sort*) = s := rfl

/-! ### Subset and strict subset relations -/

section subset
variables {s t : finset α}

instance : has_subset (finset α) := ⟨λ s t, ∀ ⦃a⦄, a ∈ s → a ∈ t⟩
instance : has_ssubset (finset α) := ⟨λ s t, s ⊆ t ∧ ¬ t ⊆ s⟩

instance : partial_order (finset α) :=
{ le := (⊆),
 lt := (⊂),
 le_refl := λ s a, id,
 le_trans := λ s t u hst htu a ha, htu $ hst ha,
 le_antisymm := λ s t hst hts, ext $ λ a, ⟨@hst _, @hts _⟩ }

instance : is_refl (finset α) (⊆) := has_le.le.is_refl
instance : is_trans (finset α) (⊆) := has_le.le.is_trans
instance : is_antisymm (finset α) (⊆) := has_le.le.is_antisymm
instance : is_irrefl (finset α) (⊂) := has_lt.lt.is_irrefl
instance : is_trans (finset α) (⊂) := has_lt.lt.is_trans
instance : is_asymm (finset α) (⊂) := has_lt.lt.is_asymm
instance : is_nonstrict_strict_order (finset α) (⊆) (⊂) := ⟨λ _ _, iff.rfl⟩

lemma subset_def : s ⊆ t ↔ s.1 ⊆ t.1 := iff.rfl
lemma ssubset_def : s ⊂ t ↔ s ⊆ t ∧ ¬ t ⊆ s := iff.rfl

@[simp] theorem subset.refl (s : finset α) : s ⊆ s := subset.refl _
protected lemma subset.rfl {s :finset α} : s ⊆ s := subset.refl _

protected theorem subset_of_eq {s t : finset α} (h : s = t) : s ⊆ t := h ▸ subset.refl _

theorem subset.trans {s₁ s₂ s₃ : finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := subset.trans

theorem superset.trans {s₁ s₂ s₃ : finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ :=
λ h' h, subset.trans h h'

theorem mem_of_subset {s₁ s₂ : finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ := mem_of_subset

lemma not_mem_mono {s t : finset α} (h : s ⊆ t) {a : α} : a ∉ t → a ∉ s := mt $ @h _

theorem subset.antisymm {s₁ s₂ : finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
ext $ λ a, ⟨@H₁ a, @H₂ a⟩

theorem subset_iff {s₁ s₂ : finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ := iff.rfl

@[simp, norm_cast] theorem coe_subset {s₁ s₂ : finset α} :
 (s₁ : set α) ⊆ s₂ ↔ s₁ ⊆ s₂ := iff.rfl

@[simp] theorem val_le_iff {s₁ s₂ : finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ := le_iff_subset s₁.2

theorem subset.antisymm_iff {s₁ s₂ : finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
le_antisymm_iff

lemma not_subset : ¬ s ⊆ t ↔ ∃ x ∈ s, x ∉ t := by simp only [←coe_subset, set.not_subset, mem_coe]

@[simp] theorem le_eq_subset : ((≤) : finset α → finset α → Prop) = (⊆) := rfl
@[simp] theorem lt_eq_subset : ((<) : finset α → finset α → Prop) = (⊂) := rfl

theorem le_iff_subset {s₁ s₂ : finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ := iff.rfl
theorem lt_iff_ssubset {s₁ s₂ : finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ := iff.rfl

@[simp, norm_cast] lemma coe_ssubset {s₁ s₂ : finset α} : (s₁ : set α) ⊂ s₂ ↔ s₁ ⊂ s₂ :=
show (s₁ : set α) ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁,
 by simp only [set.ssubset_def, finset.coe_subset]

@[simp] theorem val_lt_iff {s₁ s₂ : finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
and_congr val_le_iff $ not_congr val_le_iff

lemma ssubset_iff_subset_ne {s t : finset α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
@lt_iff_le_and_ne _ _ s t

theorem ssubset_iff_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁ ⊂ s₂ ↔ ∃ x ∈ s₂, x ∉ s₁ :=
set.ssubset_iff_of_subset h

lemma ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) :
 s₁ ⊂ s₃ :=
set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃

lemma ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : finset α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) :
 s₁ ⊂ s₃ :=
set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃

lemma exists_of_ssubset {s₁ s₂ : finset α} (h : s₁ ⊂ s₂) :
 ∃ x ∈ s₂, x ∉ s₁ :=
set.exists_of_ssubset h

instance is_well_founded_ssubset : is_well_founded (finset α) (⊂) :=
subrelation.is_well_founded (inv_image _ _) $ λ _ _, val_lt_iff.2

instance is_well_founded_lt : well_founded_lt (finset α) := finset.is_well_founded_ssubset

end subset

-- TODO: these should be global attributes, but this will require fixing other files
local attribute [trans] subset.trans superset.trans

/-! ### Order embedding from `finset α` to `set α` -/

/-- Coercion to `set α` as an `order_embedding`. -/
def coe_emb : finset α ↪o set α := ⟨⟨coe, coe_injective⟩, λ s t, coe_subset⟩

@[simp] lemma coe_coe_emb : ⇑(coe_emb : finset α ↪o set α) = coe := rfl

/-! ### Nonempty -/

/-- The property `s.nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def nonempty (s : finset α) : Prop := ∃ x : α, x ∈ s

instance decidable_nonempty {s : finset α} : decidable s.nonempty :=
decidable_of_iff (∃ a ∈ s, true) $ by simp_rw [exists_prop, and_true, finset.nonempty]

@[simp, norm_cast] lemma coe_nonempty {s : finset α} : (s : set α).nonempty ↔ s.nonempty := iff.rfl

@[simp] lemma nonempty_coe_sort {s : finset α} : nonempty ↥s ↔ s.nonempty := nonempty_subtype

alias coe_nonempty ↔ _ nonempty.to_set
alias nonempty_coe_sort ↔ _ nonempty.coe_sort

lemma nonempty.bex {s : finset α} (h : s.nonempty) : ∃ x : α, x ∈ s := h

lemma nonempty.mono {s t : finset α} (hst : s ⊆ t) (hs : s.nonempty) : t.nonempty :=
set.nonempty.mono hst hs

lemma nonempty.forall_const {s : finset α} (h : s.nonempty) {p : Prop} : (∀ x ∈ s, p) ↔ p :=
let ⟨x, hx⟩ := h in ⟨λ h, h x hx, λ h x hx, h⟩

lemma nonempty.to_subtype {s : finset α} : s.nonempty → nonempty s := nonempty_coe_sort.2
lemma nonempty.to_type {s : finset α} : s.nonempty → nonempty α := λ ⟨x, hx⟩, ⟨x⟩

/-! ### empty -/

section empty
variables {s : finset α}

/-- The empty finset -/
protected def empty : finset α := ⟨0, nodup_zero⟩

instance : has_emptyc (finset α) := ⟨finset.empty⟩

instance inhabited_finset : inhabited (finset α) := ⟨∅⟩

@[simp] theorem empty_val : (∅ : finset α).1 = 0 := rfl

@[simp] theorem not_mem_empty (a : α) : a ∉ (∅ : finset α) := id

@[simp] theorem not_nonempty_empty : ¬(∅ : finset α).nonempty :=
λ ⟨x, hx⟩, not_mem_empty x hx

@[simp] theorem mk_zero : (⟨0, nodup_zero⟩ : finset α) = ∅ := rfl

theorem ne_empty_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ≠ ∅ :=
λ e, not_mem_empty a $ e ▸ h

theorem nonempty.ne_empty {s : finset α} (h : s.nonempty) : s ≠ ∅ :=
exists.elim h $ λ a, ne_empty_of_mem

@[simp] theorem empty_subset (s : finset α) : ∅ ⊆ s := zero_subset _

lemma eq_empty_of_forall_not_mem {s : finset α} (H : ∀ x, x ∉ s) : s = ∅ :=
eq_of_veq (eq_zero_of_forall_not_mem H)

lemma eq_empty_iff_forall_not_mem {s : finset α} : s = ∅ ↔ ∀ x, x ∉ s :=
⟨by rintro rfl x; exact id, λ h, eq_empty_of_forall_not_mem h⟩

@[simp] theorem val_eq_zero {s : finset α} : s.1 = 0 ↔ s = ∅ := @val_inj _ s ∅

theorem subset_empty {s : finset α} : s ⊆ ∅ ↔ s = ∅ := subset_zero.trans val_eq_zero

@[simp] lemma not_ssubset_empty (s : finset α) : ¬s ⊂ ∅ :=
λ h, let ⟨x, he, hs⟩ := exists_of_ssubset h in he

theorem nonempty_of_ne_empty {s : finset α} (h : s ≠ ∅) : s.nonempty :=
exists_mem_of_ne_zero (mt val_eq_zero.1 h)

theorem nonempty_iff_ne_empty {s : finset α} : s.nonempty ↔ s ≠ ∅ :=
⟨nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp] theorem not_nonempty_iff_eq_empty {s : finset α} : ¬s.nonempty ↔ s = ∅ :=
nonempty_iff_ne_empty.not.trans not_not

theorem eq_empty_or_nonempty (s : finset α) : s = ∅ ∨ s.nonempty :=
classical.by_cases or.inl (λ h, or.inr (nonempty_of_ne_empty h))

@[simp, norm_cast] lemma coe_empty : ((∅ : finset α) : set α) = ∅ := rfl

@[simp, norm_cast] lemma coe_eq_empty {s : finset α} : (s : set α) = ∅ ↔ s = ∅ :=
by rw [← coe_empty]; rw [ coe_inj]

@[simp] lemma is_empty_coe_sort {s : finset α} : is_empty ↥s ↔ s = ∅ :=
by simpa using @set.is_empty_coe_sort α s

instance : is_empty (∅ : finset α) := is_empty_coe_sort.2 rfl

/-- A `finset` for an empty type is empty. -/
lemma eq_empty_of_is_empty [is_empty α] (s : finset α) : s = ∅ :=
finset.eq_empty_of_forall_not_mem is_empty_elim

instance : order_bot (finset α) :=
{ bot := ∅, bot_le := empty_subset }

@[simp] lemma bot_eq_empty : (⊥ : finset α) = ∅ := rfl

@[simp] lemma empty_ssubset : ∅ ⊂ s ↔ s.nonempty :=
(@bot_lt_iff_ne_bot (finset α) _ _ _).trans nonempty_iff_ne_empty.symm

alias empty_ssubset ↔ _ nonempty.empty_ssubset

end empty

/-! ### singleton -/

section singleton
variables {s : finset α} {a b : α}

/--
`{a} : finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `decidable_eq` instance for `α`.
-/
instance : has_singleton α (finset α) := ⟨λ a, ⟨{a}, nodup_singleton a⟩⟩

@[simp] theorem singleton_val (a : α) : ({a} : finset α).1 = {a} := rfl

@[simp] theorem mem_singleton {a b : α} : b ∈ ({a} : finset α) ↔ b = a := mem_singleton

lemma eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : finset α)) : x = y := mem_singleton.1 h

theorem not_mem_singleton {a b : α} : a ∉ ({b} : finset α) ↔ a ≠ b := not_congr mem_singleton

theorem mem_singleton_self (a : α) : a ∈ ({a} : finset α) := or.inl rfl

@[simp] lemma val_eq_singleton_iff {a : α} {s : finset α} : s.val = {a} ↔ s = {a} :=
by { rw ←val_inj, refl }

lemma singleton_injective : injective (singleton : α → finset α) :=
λ a b h, mem_singleton.1 (h ▸ mem_singleton_self _)

@[simp] lemma singleton_inj : ({a} : finset α) = {b} ↔ a = b := singleton_injective.eq_iff

@[simp] theorem singleton_nonempty (a : α) : ({a} : finset α).nonempty := ⟨a, mem_singleton_self a⟩

@[simp] theorem singleton_ne_empty (a : α) : ({a} : finset α) ≠ ∅ := (singleton_nonempty a).ne_empty

lemma empty_ssubset_singleton : (∅ : finset α) ⊂ {a} := (singleton_nonempty _).empty_ssubset

@[simp, norm_cast] lemma coe_singleton (a : α) : (({a} : finset α) : set α) = {a} :=
by { ext, simp }

@[simp, norm_cast] lemma coe_eq_singleton {s : finset α} {a : α} : (s : set α) = {a} ↔ s = {a} :=
by rw [←coe_singleton]; rw [ coe_inj]

lemma eq_singleton_iff_unique_mem {s : finset α} {a : α} :
 s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
begin
 split; intro t,
 rw t,
 refine ⟨finset.mem_singleton_self _, λ _, finset.mem_singleton.1⟩,
 ext, rw finset.mem_singleton,
 refine ⟨t.right _, λ r, r.symm ▸ t.left⟩
end

lemma eq_singleton_iff_nonempty_unique_mem {s : finset α} {a : α} :
 s = {a} ↔ s.nonempty ∧ ∀ x ∈ s, x = a :=
begin
 split,
 { rintro rfl, simp },
 { rintros ⟨hne, h_uniq⟩, rw eq_singleton_iff_unique_mem, refine ⟨_, h_uniq⟩,
 rw ← h_uniq hne.some hne.some_spec, exact hne.some_spec }
end

lemma nonempty_iff_eq_singleton_default [unique α] {s : finset α} :
 s.nonempty ↔ s = {default} :=
by simp [eq_singleton_iff_nonempty_unique_mem]

alias nonempty_iff_eq_singleton_default ↔ nonempty.eq_singleton_default _

lemma singleton_iff_unique_mem (s : finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s :=
by simp only [eq_singleton_iff_unique_mem, exists_unique]

lemma singleton_subset_set_iff {s : set α} {a : α} : ↑({a} : finset α) ⊆ s ↔ a ∈ s :=
by rw [coe_singleton]; rw [ set.singleton_subset_iff]

@[simp] lemma singleton_subset_iff {s : finset α} {a : α} : {a} ⊆ s ↔ a ∈ s :=
singleton_subset_set_iff

@[simp] lemma subset_singleton_iff {s : finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} :=
by rw [←coe_subset]; rw [ coe_singleton]; rw [ set.subset_singleton_iff_eq]; rw [ coe_eq_empty]; rw [ coe_eq_singleton]

lemma singleton_subset_singleton : ({a} : finset α) ⊆ {b} ↔ a = b := by simp

protected lemma nonempty.subset_singleton_iff {s : finset α} {a : α} (h : s.nonempty) :
 s ⊆ {a} ↔ s = {a} :=
subset_singleton_iff.trans $ or_iff_right h.ne_empty

lemma subset_singleton_iff' {s : finset α} {a : α} : s ⊆ {a} ↔ ∀ b ∈ s, b = a :=
forall₂_congr $ λ _ _, mem_singleton

@[simp] lemma ssubset_singleton_iff {s : finset α} {a : α} :
 s ⊂ {a} ↔ s = ∅ :=
by rw [←coe_ssubset]; rw [ coe_singleton]; rw [ set.ssubset_singleton_iff]; rw [ coe_eq_empty]

lemma eq_empty_of_ssubset_singleton {s : finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
ssubset_singleton_iff.1 hs

/-- A finset is nontrivial if it has at least two elements. -/
@[reducible] protected def nontrivial (s : finset α) : Prop := (s : set α).nontrivial

@[simp] lemma not_nontrivial_empty : ¬ (∅ : finset α).nontrivial := by simp [finset.nontrivial]

@[simp] lemma not_nontrivial_singleton : ¬ ({a} : finset α).nontrivial :=
by simp [finset.nontrivial]

lemma nontrivial.ne_singleton (hs : s.nontrivial) : s ≠ {a} :=
by { rintro rfl, exact not_nontrivial_singleton hs }

lemma eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ s.nontrivial :=
by { rw ←coe_eq_singleton, exact set.eq_singleton_or_nontrivial ha }

lemma nontrivial_iff_ne_singleton (ha : a ∈ s) : s.nontrivial ↔ s ≠ {a} :=
⟨nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

lemma nonempty.exists_eq_singleton_or_nontrivial : s.nonempty → (∃ a, s = {a}) ∨ s.nontrivial :=
λ ⟨a, ha⟩, (eq_singleton_or_nontrivial ha).imp_left $ exists.intro a

instance nontrivial' [nonempty α] : nontrivial (finset α) :=
‹nonempty α›.elim $ λ a, ⟨⟨{a}, ∅, singleton_ne_empty _⟩⟩

instance [is_empty α] : unique (finset α) :=
{ default := ∅,
 uniq := λ s, eq_empty_of_forall_not_mem is_empty_elim }

end singleton

/-! ### cons -/

section cons
variables {s t : finset α} {a b : α}

/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `decidable_eq α`,
and the union is guaranteed to be disjoint. -/
def cons (a : α) (s : finset α) (h : a ∉ s) : finset α := ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩

@[simp] lemma mem_cons {h} : b ∈ s.cons a h ↔ b = a ∨ b ∈ s := mem_cons
@[simp] lemma mem_cons_self (a : α) (s : finset α) {h} : a ∈ cons a s h := mem_cons_self _ _
@[simp] lemma cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 := rfl

lemma forall_mem_cons (h : a ∉ s) (p : α → Prop) :
 (∀ x, x ∈ cons a s h → p x) ↔ p a ∧ ∀ x, x ∈ s → p x :=
by simp only [mem_cons, or_imp_distrib, forall_and_distrib, forall_eq]

/-- Useful in proofs by induction. -/
lemma forall_of_forall_cons {p : α → Prop} {h : a ∉ s} (H : ∀ x, x ∈ cons a s h → p x) (x)
 (h : x ∈ s) : p x := H _ $ mem_cons.2 $ or.inr h

@[simp] lemma mk_cons {s : multiset α} (h : (a ::ₘ s).nodup) :
 (⟨a ::ₘ s, h⟩ : finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1 := rfl

@[simp] lemma cons_empty (a : α) : cons a ∅ (not_mem_empty _) = {a} := rfl

@[simp] lemma nonempty_cons (h : a ∉ s) : (cons a s h).nonempty := ⟨a, mem_cons.2 $ or.inl rfl⟩

@[simp] lemma nonempty_mk {m : multiset α} {hm} : (⟨m, hm⟩ : finset α).nonempty ↔ m ≠ 0 :=
by induction m using multiset.induction_on; simp

@[simp] lemma coe_cons {a s h} : (@cons α a s h : set α) = insert a s := by { ext, simp }

lemma subset_cons (h : a ∉ s) : s ⊆ s.cons a h := subset_cons _ _
lemma ssubset_cons (h : a ∉ s) : s ⊂ s.cons a h := ssubset_cons h
lemma cons_subset {h : a ∉ s} : s.cons a h ⊆ t ↔ a ∈ t ∧ s ⊆ t := cons_subset

@[simp] lemma cons_subset_cons {hs ht} : s.cons a hs ⊆ t.cons a ht ↔ s ⊆ t :=
by rwa [← coe_subset]; rwa [ coe_cons]; rwa [ coe_cons]; rwa [ set.insert_subset_insert_iff]; rwa [ coe_subset]

lemma ssubset_iff_exists_cons_subset : s ⊂ t ↔ ∃ a (h : a ∉ s), s.cons a h ⊆ t :=
begin
 refine ⟨λ h, _, λ ⟨a, ha, h⟩, ssubset_of_ssubset_of_subset (ssubset_cons _) h⟩,
 obtain ⟨a, hs, ht⟩ := not_subset.1 h.2,
 exact ⟨a, ht, cons_subset.2 ⟨hs, h.subset⟩⟩,
end

end cons

/-! ### disjoint -/

section disjoint
variables {f : α → β} {s t u : finset α} {a b : α}

lemma disjoint_left : disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
⟨λ h a hs ht,
 singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
 λ h x hs ht a ha, h (hs ha) (ht ha)⟩

lemma disjoint_right : disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by rw [disjoint.comm]; rw [ disjoint_left]
lemma disjoint_iff_ne : disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b :=
by simp only [disjoint_left, imp_not_comm, forall_eq']

@[simp] lemma disjoint_val : s.1.disjoint t.1 ↔ disjoint s t := disjoint_left.symm

lemma _root_.disjoint.forall_ne_finset (h : disjoint s t) (ha : a ∈ s) (hb : b ∈ t) : a ≠ b :=
disjoint_iff_ne.1 h _ ha _ hb

lemma not_disjoint_iff : ¬ disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t :=
disjoint_left.not.trans $ not_forall.trans $ exists_congr $ λ _, by rw [not_imp]; rw [ not_not]

lemma disjoint_of_subset_left (h : s ⊆ u) (d : disjoint u t) : disjoint s t :=
disjoint_left.2 (λ x m₁, (disjoint_left.1 d) (h m₁))

lemma disjoint_of_subset_right (h : t ⊆ u) (d : disjoint s u) : disjoint s t :=
disjoint_right.2 (λ x m₁, (disjoint_right.1 d) (h m₁))

@[simp] theorem disjoint_empty_left (s : finset α) : disjoint ∅ s := disjoint_bot_left
@[simp] theorem disjoint_empty_right (s : finset α) : disjoint s ∅ := disjoint_bot_right

@[simp] lemma disjoint_singleton_left : disjoint (singleton a) s ↔ a ∉ s :=
by simp only [disjoint_left, mem_singleton, forall_eq]

@[simp] lemma disjoint_singleton_right : disjoint s (singleton a) ↔ a ∉ s :=
disjoint.comm.trans disjoint_singleton_left

@[simp] lemma disjoint_singleton : disjoint ({a} : finset α) {b} ↔ a ≠ b :=
by rw [disjoint_singleton_left]; rw [ mem_singleton]

lemma disjoint_self_iff_empty (s : finset α) : disjoint s s ↔ s = ∅ := disjoint_self

@[simp, norm_cast] lemma disjoint_coe : disjoint (s : set α) t ↔ disjoint s t :=
by { rw [finset.disjoint_left]; rw [ set.disjoint_left], refl }

@[simp, norm_cast] lemma pairwise_disjoint_coe {ι : Type*} {s : set ι} {f : ι → finset α} :
 s.pairwise_disjoint (λ i, f i : ι → set α) ↔ s.pairwise_disjoint f :=
forall₅_congr $ λ _ _ _ _ _, disjoint_coe

end disjoint

/-! ### disjoint union -/

/-- `disj_union s t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
def disj_union (s t : finset α) (h : disjoint s t) : finset α :=
⟨s.1 + t.1, multiset.nodup_add.2 ⟨s.2, t.2, disjoint_val.2 h⟩⟩

@[simp] theorem mem_disj_union {α s t h a} :
 a ∈ @disj_union α s t h ↔ a ∈ s ∨ a ∈ t :=
by rcases s with ⟨⟨s⟩⟩; rcases t with ⟨⟨t⟩⟩; apply list.mem_append

lemma disj_union_comm (s t : finset α) (h : disjoint s t) :
 disj_union s t h = disj_union t s h.symm :=
eq_of_veq $ add_comm _ _

@[simp] lemma empty_disj_union (t : finset α) (h : disjoint ∅ t := disjoint_bot_left) :
 disj_union ∅ t h = t :=
eq_of_veq $ zero_add _

@[simp] lemma disj_union_empty (s : finset α) (h : disjoint s ∅ := disjoint_bot_right) :
 disj_union s ∅ h = s :=
eq_of_veq $ add_zero _

lemma singleton_disj_union (a : α) (t : finset α) (h : disjoint {a} t) :
 disj_union {a} t h = cons a t (disjoint_singleton_left.mp h) :=
eq_of_veq $ multiset.singleton_add _ _

lemma disj_union_singleton (s : finset α) (a : α) (h : disjoint s {a}) :
 disj_union s {a} h = cons a s (disjoint_singleton_right.mp h) :=
by rw [disj_union_comm]; rw [ singleton_disj_union]

/-! ### insert -/

section insert
variables [decidable_eq α] {s t u v : finset α} {a b : α}

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : has_insert α (finset α) := ⟨λ a s, ⟨_, s.2.ndinsert a⟩⟩

lemma insert_def (a : α) (s : finset α) : insert a s = ⟨_, s.2.ndinsert a⟩ := rfl

@[simp] theorem insert_val (a : α) (s : finset α) : (insert a s).1 = ndinsert a s.1 := rfl

theorem insert_val' (a : α) (s : finset α) : (insert a s).1 = dedup (a ::ₘ s.1) :=
by rw [dedup_cons]; rw [ dedup_eq_self]; refl

theorem insert_val_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 :=
by rw [insert_val]; rw [ ndinsert_of_not_mem h]

@[simp] lemma mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s := mem_ndinsert

theorem mem_insert_self (a : α) (s : finset α) : a ∈ insert a s := mem_ndinsert_self a s.1
lemma mem_insert_of_mem (h : a ∈ s) : a ∈ insert b s := mem_ndinsert_of_mem h
lemma mem_of_mem_insert_of_ne (h : b ∈ insert a s) : b ≠ a → b ∈ s := (mem_insert.1 h).resolve_left
lemma eq_of_not_mem_of_mem_insert (ha : b ∈ insert a s) (hb : b ∉ s) : b = a :=
(mem_insert.1 ha).resolve_right hb

@[simp] theorem cons_eq_insert (a s h) : @cons α a s h = insert a s := ext $ λ a, by simp

@[simp, norm_cast] lemma coe_insert (a : α) (s : finset α) :
 ↑(insert a s) = (insert a s : set α) :=
set.ext $ λ x, by simp only [mem_coe, mem_insert, set.mem_insert_iff]

lemma mem_insert_coe {s : finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : set α) :=
by simp

instance : is_lawful_singleton α (finset α) := ⟨λ a, by { ext, simp }⟩

@[simp] lemma insert_eq_of_mem (h : a ∈ s) : insert a s = s := eq_of_veq $ ndinsert_of_mem h

@[simp] lemma insert_eq_self : insert a s = s ↔ a ∈ s :=
⟨λ h, h ▸ mem_insert_self _ _, insert_eq_of_mem⟩

lemma insert_ne_self : insert a s ≠ s ↔ a ∉ s := insert_eq_self.not

@[simp] theorem pair_eq_singleton (a : α) : ({a, a} : finset α) = {a} :=
insert_eq_of_mem $ mem_singleton_self _

theorem insert.comm (a b : α) (s : finset α) : insert a (insert b s) = insert b (insert a s) :=
ext $ λ x, by simp only [mem_insert, or.left_comm]

@[simp, norm_cast] lemma coe_pair {a b : α} :
 (({a, b} : finset α) : set α) = {a, b} := by { ext, simp }

@[simp, norm_cast] lemma coe_eq_pair {s : finset α} {a b : α} :
 (s : set α) = {a, b} ↔ s = {a, b} := by rw [←coe_pair]; rw [ coe_inj]

theorem pair_comm (a b : α) : ({a, b} : finset α) = {b, a} := insert.comm a b ∅

@[simp] theorem insert_idem (a : α) (s : finset α) : insert a (insert a s) = insert a s :=
ext $ λ x, by simp only [mem_insert, or.assoc.symm, or_self]

@[simp] theorem insert_nonempty (a : α) (s : finset α) : (insert a s).nonempty :=
⟨a, mem_insert_self a s⟩

@[simp] theorem insert_ne_empty (a : α) (s : finset α) : insert a s ≠ ∅ :=
(insert_nonempty a s).ne_empty

/-!
The universe annotation is required for the following instance, possibly this is a bug in Lean. See
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/strange.20error.20(universe.20issue.3F)
-/

instance {α : Type u} [decidable_eq α] (i : α) (s : finset α) :
 nonempty.{u + 1} ((insert i s : finset α) : set α) :=
(finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype

lemma ne_insert_of_not_mem (s t : finset α) {a : α} (h : a ∉ s) : s ≠ insert a t :=
by { contrapose! h, simp [h] }

lemma insert_subset : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
by simp only [subset_iff, mem_insert, forall_eq, or_imp_distrib, forall_and_distrib]

lemma subset_insert (a : α) (s : finset α) : s ⊆ insert a s := λ b, mem_insert_of_mem

theorem insert_subset_insert (a : α) {s t : finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
insert_subset.2 ⟨mem_insert_self _ _, subset.trans h (subset_insert _ _)⟩

lemma insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
⟨λ h, eq_of_not_mem_of_mem_insert (h.subst $ mem_insert_self _ _) ha, congr_arg _⟩

lemma insert_inj_on (s : finset α) : set.inj_on (λ a, insert a s) sᶜ := λ a h b _, (insert_inj h).1

lemma ssubset_iff : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t :=
by exact_mod_cast @set.ssubset_iff_insert α s t

lemma ssubset_insert (h : a ∉ s) : s ⊂ insert a s := ssubset_iff.mpr ⟨a, h, subset.rfl⟩

@[elab_as_eliminator]
lemma cons_induction {α : Type*} {p : finset α → Prop}
 (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α} (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
| ⟨s, nd⟩ := multiset.induction_on s (λ _, h₁) (λ a s IH nd, begin
 cases nodup_cons.1 nd with m nd',
 rw [← (eq_of_veq _ : cons a (finset.mk s _) m = ⟨a ::ₘ s, nd⟩)],
 { exact h₂ (by exact m) (IH nd') },
 { rw [cons_val] }
 end) nd

@[elab_as_eliminator]
lemma cons_induction_on {α : Type*} {p : finset α → Prop} (s : finset α)
 (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α} (h : a ∉ s), p s → p (cons a s h)) : p s :=
cons_induction h₁ h₂ s

@[elab_as_eliminator]
protected theorem induction {α : Type*} {p : finset α → Prop} [decidable_eq α]
 (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
cons_induction h₁ $ λ a s ha, (s.cons_eq_insert a ha).symm ▸ h₂ ha

/--
To prove a proposition about an arbitrary `finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α`,
then it holds for the `finset` obtained by inserting a new element.
-/
@[elab_as_eliminator]
protected theorem induction_on {α : Type*} {p : finset α → Prop} [decidable_eq α]
 (s : finset α) (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : p s :=
finset.induction h₁ h₂ s

/--
To prove a proposition about `S : finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α ⊆ S`,
then it holds for the `finset` obtained by inserting a new element of `S`.
-/
@[elab_as_eliminator]
theorem induction_on' {α : Type*} {p : finset α → Prop} [decidable_eq α]
 (S : finset α) (h₁ : p ∅) (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → p s → p (insert a s)) : p S :=
@finset.induction_on α (λ T, T ⊆ S → p T) _ S (λ _, h₁) (λ a s has hqs hs,
 let ⟨hS, sS⟩ := finset.insert_subset.1 hs in h₂ hS sS has (hqs sS)) (finset.subset.refl S)

/-- To prove a proposition about a nonempty `s : finset α`, it suffices to show it holds for all
singletons and that if it holds for nonempty `t : finset α`, then it also holds for the `finset`
obtained by inserting an element in `t`. -/
@[elab_as_eliminator]
lemma nonempty.cons_induction {α : Type*} {p : Π s : finset α, s.nonempty → Prop}
 (h₀ : ∀ a, p {a} (singleton_nonempty _))
 (h₁ : ∀ ⦃a⦄ s (h : a ∉ s) hs, p s hs → p (finset.cons a s h) (nonempty_cons h))
 {s : finset α} (hs : s.nonempty) : p s hs :=
begin
 induction s using finset.cons_induction with a t ha h,
 { exact (not_nonempty_empty hs).elim },
 obtain rfl | ht := t.eq_empty_or_nonempty,
 { exact h₀ a },
 { exact h₁ t ha ht (h ht) }
end

/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtype_insert_equiv_option {t : finset α} {x : α} (h : x ∉ t) :
 {i // i ∈ insert x t} ≃ option {i // i ∈ t} :=
begin
 refine
 { to_fun := λ y, if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩,
 inv_fun := λ y, y.elim ⟨x, mem_insert_self _ _⟩ $ λ z, ⟨z, mem_insert_of_mem z.2⟩,
 .. },
 { intro y, by_cases h : ↑y = x,
 simp only [subtype.ext_iff, h, option.elim, dif_pos, subtype.coe_mk],
 simp only [h, option.elim, dif_neg, not_false_iff, subtype.coe_eta, subtype.coe_mk] },
 { rintro (_|y), simp only [option.elim, dif_pos, subtype.coe_mk],
 have : ↑y ≠ x, { rintro ⟨⟩, exact h y.2 },
 simp only [this, option.elim, subtype.eta, dif_neg, not_false_iff, subtype.coe_eta,
 subtype.coe_mk] },
end

@[simp] lemma disjoint_insert_left : disjoint (insert a s) t ↔ a ∉ t ∧ disjoint s t :=
by simp only [disjoint_left, mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

@[simp] lemma disjoint_insert_right : disjoint s (insert a t) ↔ a ∉ s ∧ disjoint s t :=
disjoint.comm.trans $ by rw [disjoint_insert_left]; rw [ disjoint.comm]

end insert

/-! ### Lattice structure -/

section lattice
variables [decidable_eq α] {s s₁ s₂ t t₁ t₂ u v : finset α} {a b : α}

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance : has_union (finset α) := ⟨λ s t, ⟨_, t.2.ndunion s.1⟩⟩

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
instance : has_inter (finset α) := ⟨λ s t, ⟨_, s.2.ndinter t.1⟩⟩

instance : lattice (finset α) :=
{ sup := (∪),
 sup_le := λ s t u hs ht a ha, (mem_ndunion.1 ha).elim (λ h, hs h) (λ h, ht h),
 le_sup_left := λ s t a h, mem_ndunion.2 $ or.inl h,
 le_sup_right := λ s t a h, mem_ndunion.2 $ or.inr h,
 inf := (∩),
 le_inf := λ s t u ht hu a h, mem_ndinter.2 ⟨ht h, hu h⟩,
 inf_le_left := λ s t a h, (mem_ndinter.1 h).1,
 inf_le_right := λ s t a h, (mem_ndinter.1 h).2,
 ..finset.partial_order }

@[simp] lemma sup_eq_union : ((⊔) : finset α → finset α → finset α) = (∪) := rfl
@[simp] lemma inf_eq_inter : ((⊓) : finset α → finset α → finset α) = (∩) := rfl

lemma disjoint_iff_inter_eq_empty : disjoint s t ↔ s ∩ t = ∅ := disjoint_iff

instance decidable_disjoint (U V : finset α) : decidable (disjoint U V) :=
decidable_of_iff _ disjoint_left.symm

/-! #### union -/

lemma union_val_nd (s t : finset α) : (s ∪ t).1 = ndunion s.1 t.1 := rfl

@[simp] lemma union_val (s t : finset α) : (s ∪ t).1 = s.1 ∪ t.1 := ndunion_eq_union s.2
@[simp] lemma mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := mem_ndunion
@[simp] lemma disj_union_eq_union (s t h) : @disj_union α s t h = s ∪ t := ext $ λ a, by simp

lemma mem_union_left (t : finset α) (h : a ∈ s) : a ∈ s ∪ t := mem_union.2 $ or.inl h
lemma mem_union_right (s : finset α) (h : a ∈ t) : a ∈ s ∪ t := mem_union.2 $ or.inr h

lemma forall_mem_union {p : α → Prop} : (∀ a ∈ s ∪ t, p a) ↔ (∀ a ∈ s, p a) ∧ ∀ a ∈ t, p a :=
⟨λ h, ⟨λ a, h a ∘ mem_union_left _, λ b, h b ∘ mem_union_right _⟩,
 λ h ab hab, (mem_union.mp hab).elim (h.1 _) (h.2 _)⟩

lemma not_mem_union : a ∉ s ∪ t ↔ a ∉ s ∧ a ∉ t := by rw [mem_union]; rw [ not_or_distrib]

@[simp, norm_cast]
lemma coe_union (s₁ s₂ : finset α) : ↑(s₁ ∪ s₂) = (s₁ ∪ s₂ : set α) := set.ext $ λ x, mem_union

lemma union_subset (hs : s ⊆ u) : t ⊆ u → s ∪ t ⊆ u := sup_le $ le_iff_subset.2 hs

theorem subset_union_left (s₁ s₂ : finset α) : s₁ ⊆ s₁ ∪ s₂ := λ x, mem_union_left _
theorem subset_union_right (s₁ s₂ : finset α) : s₂ ⊆ s₁ ∪ s₂ := λ x, mem_union_right _

lemma union_subset_union (hsu : s ⊆ u) (htv : t ⊆ v) : s ∪ t ⊆ u ∪ v :=
sup_le_sup (le_iff_subset.2 hsu) htv

lemma union_subset_union_left (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t := union_subset_union h subset.rfl
lemma union_subset_union_right (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ := union_subset_union subset.rfl h

lemma union_comm (s₁ s₂ : finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ := sup_comm

instance : is_commutative (finset α) (∪) := ⟨union_comm⟩

@[simp] lemma union_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := sup_assoc

instance : is_associative (finset α) (∪) := ⟨union_assoc⟩

@[simp] lemma union_idempotent (s : finset α) : s ∪ s = s := sup_idem

instance : is_idempotent (finset α) (∪) := ⟨union_idempotent⟩

lemma union_subset_left (h : s ∪ t ⊆ u) : s ⊆ u := (subset_union_left _ _).trans h

lemma union_subset_right {s t u : finset α} (h : s ∪ t ⊆ u) : t ⊆ u :=
subset.trans (subset_union_right _ _) h

lemma union_left_comm (s t u : finset α) : s ∪ (t ∪ u) = t ∪ (s ∪ u) :=
ext $ λ _, by simp only [mem_union, or.left_comm]

lemma union_right_comm (s t u : finset α) : (s ∪ t) ∪ u = (s ∪ u) ∪ t :=
ext $ λ x, by simp only [mem_union, or_assoc, or_comm (x ∈ t)]

theorem union_self (s : finset α) : s ∪ s = s := union_idempotent s

@[simp] theorem union_empty (s : finset α) : s ∪ ∅ = s :=
ext $ λ x, mem_union.trans $ or_false _

@[simp] theorem empty_union (s : finset α) : ∅ ∪ s = s :=
ext $ λ x, mem_union.trans $ false_or _

theorem insert_eq (a : α) (s : finset α) : insert a s = {a} ∪ s := rfl

@[simp] theorem insert_union (a : α) (s t : finset α) : insert a s ∪ t = insert a (s ∪ t) :=
by simp only [insert_eq, union_assoc]

@[simp] theorem union_insert (a : α) (s t : finset α) : s ∪ insert a t = insert a (s ∪ t) :=
by simp only [insert_eq, union_left_comm]

lemma insert_union_distrib (a : α) (s t : finset α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
by simp only [insert_union, union_insert, insert_idem]

@[simp] lemma union_eq_left_iff_subset {s t : finset α} : s ∪ t = s ↔ t ⊆ s := sup_eq_left
@[simp] lemma left_eq_union_iff_subset {s t : finset α} : s = s ∪ t ↔ t ⊆ s :=
by rw [← union_eq_left_iff_subset]; rw [ eq_comm]

@[simp] lemma union_eq_right_iff_subset {s t : finset α} : s ∪ t = t ↔ s ⊆ t := sup_eq_right
@[simp] lemma right_eq_union_iff_subset {s t : finset α} : s = t ∪ s ↔ t ⊆ s :=
by rw [← union_eq_right_iff_subset]; rw [ eq_comm]

lemma union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ⊔ u := sup_congr_left ht hu
lemma union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u := sup_congr_right hs ht

lemma union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t := sup_eq_sup_iff_left
lemma union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u := sup_eq_sup_iff_right

@[simp] lemma disjoint_union_left : disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
by simp only [disjoint_left, mem_union, or_imp_distrib, forall_and_distrib]

@[simp] lemma disjoint_union_right : disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
by simp only [disjoint_right, mem_union, or_imp_distrib, forall_and_distrib]

/--
To prove a relation on pairs of `finset X`, it suffices to show that it is
 * symmetric,
 * it holds when one of the `finset`s is empty,
 * it holds for pairs of singletons,
 * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
lemma induction_on_union (P : finset α → finset α → Prop)
 (symm : ∀ {a b}, P a b → P b a)
 (empty_right : ∀ {a}, P a ∅)
 (singletons : ∀ {a b}, P {a} {b})
 (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) :
 ∀ a b, P a b :=
begin
 intros a b,
 refine finset.induction_on b empty_right (λ x s xs hi, symm _),
 rw finset.insert_eq,
 apply union_of _ (symm hi),
 refine finset.induction_on a empty_right (λ a t ta hi, symm _),
 rw finset.insert_eq,
 exact union_of singletons (symm hi),
end

lemma _root_.directed.exists_mem_subset_of_finset_subset_bUnion {α ι : Type*} [hn : nonempty ι]
 {f : ι → set α} (h : directed (⊆) f)
 {s : finset α} (hs : (s : set α) ⊆ ⋃ i, f i) : ∃ i, (s : set α) ⊆ f i :=
begin
 classical,
 revert hs,
 apply s.induction_on,
 { refine λ _, ⟨hn.some, _⟩,
 simp only [coe_empty, set.empty_subset], },
 { intros b t hbt htc hbtc,
 obtain ⟨i : ι , hti : (t : set α) ⊆ f i⟩ :=
 htc (set.subset.trans (t.subset_insert b) hbtc),
 obtain ⟨j, hbj⟩ : ∃ j, b ∈ f j,
 by simpa [set.mem_Union₂] using hbtc (t.mem_insert_self b),
 rcases h j i with ⟨k, hk, hk'⟩,
 use k,
 rw [coe_insert]; rw [ set.insert_subset],
 exact ⟨hk hbj, trans hti hk'⟩ }
end

lemma _root_.directed_on.exists_mem_subset_of_finset_subset_bUnion {α ι : Type*}
 {f : ι → set α} {c : set ι} (hn : c.nonempty) (hc : directed_on (λ i j, f i ⊆ f j) c)
 {s : finset α} (hs : (s : set α) ⊆ ⋃ i ∈ c, f i) : ∃ i ∈ c, (s : set α) ⊆ f i :=
begin
 rw set.bUnion_eq_Union at hs,
 haveI := hn.coe_sort,
 obtain ⟨⟨i, hic⟩, hi⟩ :=
 (directed_comp.2 hc.directed_coe).exists_mem_subset_of_finset_subset_bUnion hs,
 exact ⟨i, hic, hi⟩
end

/-! #### inter -/

theorem inter_val_nd (s₁ s₂ : finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 := rfl

@[simp] lemma inter_val (s₁ s₂ : finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 := ndinter_eq_inter s₁.2

@[simp] theorem mem_inter {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ := mem_ndinter

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : finset α} (h : a ∈ s₁ ∩ s₂) :
 a ∈ s₁ := (mem_inter.1 h).1

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : finset α} (h : a ∈ s₁ ∩ s₂) :
 a ∈ s₂ := (mem_inter.1 h).2

theorem mem_inter_of_mem {a : α} {s₁ s₂ : finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
and_imp.1 mem_inter.2

theorem inter_subset_left (s₁ s₂ : finset α) : s₁ ∩ s₂ ⊆ s₁ := λ a, mem_of_mem_inter_left

theorem inter_subset_right (s₁ s₂ : finset α) : s₁ ∩ s₂ ⊆ s₂ := λ a, mem_of_mem_inter_right

lemma subset_inter {s₁ s₂ u : finset α} : s₁ ⊆ s₂ → s₁ ⊆ u → s₁ ⊆ s₂ ∩ u :=
by simp only [subset_iff, mem_inter] {contextual:=tt}; intros; split; trivial

@[simp, norm_cast]
lemma coe_inter (s₁ s₂ : finset α) : ↑(s₁ ∩ s₂) = (s₁ ∩ s₂ : set α) := set.ext $ λ _, mem_inter

@[simp] theorem union_inter_cancel_left {s t : finset α} : (s ∪ t) ∩ s = s :=
by rw [← coe_inj]; rw [ coe_inter]; rw [ coe_union]; rw [ set.union_inter_cancel_left]

@[simp] theorem union_inter_cancel_right {s t : finset α} : (s ∪ t) ∩ t = t :=
by rw [← coe_inj]; rw [ coe_inter]; rw [ coe_union]; rw [ set.union_inter_cancel_right]

theorem inter_comm (s₁ s₂ : finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
ext $ λ _, by simp only [mem_inter, and_comm]

@[simp] theorem inter_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
ext $ λ _, by simp only [mem_inter, and_assoc]

theorem inter_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
ext $ λ _, by simp only [mem_inter, and.left_comm]

theorem inter_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
ext $ λ _, by simp only [mem_inter, and.right_comm]

@[simp] lemma inter_self (s : finset α) : s ∩ s = s := ext $ λ _, mem_inter.trans $ and_self _
@[simp] lemma inter_empty (s : finset α) : s ∩ ∅ = ∅ := ext $ λ _, mem_inter.trans $ and_false _
@[simp] lemma empty_inter (s : finset α) : ∅ ∩ s = ∅ := ext $ λ _, mem_inter.trans $ false_and _

@[simp] lemma inter_union_self (s t : finset α) : s ∩ (t ∪ s) = s :=
by rw [inter_comm]; rw [ union_inter_cancel_right]

@[simp] theorem insert_inter_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₂) :
 insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
ext $ λ x, have x = a ∨ x ∈ s₂ ↔ x ∈ s₂, from or_iff_right_of_imp $ by rintro rfl; exact h,
by simp only [mem_inter, mem_insert, or_and_distrib_left, this]

@[simp] theorem inter_insert_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₁) :
 s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) :=
by rw [inter_comm]; rw [ insert_inter_of_mem h]; rw [ inter_comm]

@[simp] theorem insert_inter_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₂) :
 insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
ext $ λ x, have ¬ (x = a ∧ x ∈ s₂), by rintro ⟨rfl, H⟩; exact h H,
by simp only [mem_inter, mem_insert, or_and_distrib_right, this, false_or]

@[simp] theorem inter_insert_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₁) :
 s₁ ∩ insert a s₂ = s₁ ∩ s₂ :=
by rw [inter_comm]; rw [ insert_inter_of_not_mem h]; rw [ inter_comm]

@[simp] theorem singleton_inter_of_mem {a : α} {s : finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
show insert a ∅ ∩ s = insert a ∅, by rw [insert_inter_of_mem H]; rw [ empty_inter]

@[simp] theorem singleton_inter_of_not_mem {a : α} {s : finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
eq_empty_of_forall_not_mem $ by simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[simp] theorem inter_singleton_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ∩ {a} = {a} :=
by rw [inter_comm]; rw [ singleton_inter_of_mem h]

@[simp] theorem inter_singleton_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : s ∩ {a} = ∅ :=
by rw [inter_comm]; rw [ singleton_inter_of_not_mem h]

@[mono]
lemma inter_subset_inter {x y s t : finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t :=
begin
 intros a a_in,
 rw finset.mem_inter at a_in ⊢,
 exact ⟨h a_in.1, h' a_in.2⟩
end

lemma inter_subset_inter_left (h : t ⊆ u) : s ∩ t ⊆ s ∩ u := inter_subset_inter subset.rfl h
lemma inter_subset_inter_right (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := inter_subset_inter h subset.rfl

lemma inter_subset_union : s ∩ t ⊆ s ∪ t := le_iff_subset.1 inf_le_sup

instance : distrib_lattice (finset α) :=
{ le_sup_inf := assume a b c, show (a ∪ b) ∩ (a ∪ c) ⊆ a ∪ b ∩ c,
 by simp only [subset_iff, mem_inter, mem_union, and_imp, or_imp_distrib] {contextual:=tt};
 simp only [true_or, imp_true_iff, true_and, or_true],
 ..finset.lattice }

@[simp] theorem union_left_idem (s t : finset α) : s ∪ (s ∪ t) = s ∪ t := sup_left_idem

@[simp] theorem union_right_idem (s t : finset α) : s ∪ t ∪ t = s ∪ t := sup_right_idem
@[simp] theorem inter_left_idem (s t : finset α) : s ∩ (s ∩ t) = s ∩ t := inf_left_idem

@[simp] theorem inter_right_idem (s t : finset α) : s ∩ t ∩ t = s ∩ t := inf_right_idem

theorem inter_distrib_left (s t u : finset α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := inf_sup_left

theorem inter_distrib_right (s t u : finset α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := inf_sup_right

theorem union_distrib_left (s t u : finset α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) := sup_inf_left

theorem union_distrib_right (s t u : finset α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) := sup_inf_right

lemma union_union_distrib_left (s t u : finset α) : s ∪ (t ∪ u) = (s ∪ t) ∪ (s ∪ u) :=
sup_sup_distrib_left _ _ _

lemma union_union_distrib_right (s t u : finset α) : (s ∪ t) ∪ u = (s ∪ u) ∪ (t ∪ u) :=
sup_sup_distrib_right _ _ _

lemma inter_inter_distrib_left (s t u : finset α) : s ∩ (t ∩ u) = (s ∩ t) ∩ (s ∩ u) :=
inf_inf_distrib_left _ _ _

lemma inter_inter_distrib_right (s t u : finset α) : (s ∩ t) ∩ u = (s ∩ u) ∩ (t ∩ u) :=
inf_inf_distrib_right _ _ _

lemma union_union_union_comm (s t u v : finset α) : (s ∪ t) ∪ (u ∪ v) = (s ∪ u) ∪ (t ∪ v) :=
sup_sup_sup_comm _ _ _ _

lemma inter_inter_inter_comm (s t u v : finset α) : (s ∩ t) ∩ (u ∩ v) = (s ∩ u) ∩ (t ∩ v) :=
inf_inf_inf_comm _ _ _ _

lemma union_eq_empty_iff (A B : finset α) : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ := sup_eq_bot_iff

lemma union_subset_iff : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u := (sup_le_iff : s ⊔ t ≤ u ↔ s ≤ u ∧ t ≤ u)
lemma subset_inter_iff : s ⊆ t ∩ u ↔ s ⊆ t ∧ s ⊆ u := (le_inf_iff : s ≤ t ⊓ u ↔ s ≤ t ∧ s ≤ u)

@[simp] lemma inter_eq_left_iff_subset (s t : finset α) : s ∩ t = s ↔ s ⊆ t := inf_eq_left
@[simp] lemma inter_eq_right_iff_subset (s t : finset α) : t ∩ s = s ↔ s ⊆ t := inf_eq_right

lemma inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u := inf_congr_left ht hu
lemma inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u := inf_congr_right hs ht

lemma inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u := inf_eq_inf_iff_left
lemma inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t := inf_eq_inf_iff_right

lemma ite_subset_union (s s' : finset α) (P : Prop) [decidable P] :
 ite P s s' ⊆ s ∪ s' := ite_le_sup s s' P

lemma inter_subset_ite (s s' : finset α) (P : Prop) [decidable P] :
 s ∩ s' ⊆ ite P s s' := inf_le_ite s s' P

lemma not_disjoint_iff_nonempty_inter : ¬disjoint s t ↔ (s ∩ t).nonempty :=
not_disjoint_iff.trans $ by simp [finset.nonempty]

alias not_disjoint_iff_nonempty_inter ↔ _ nonempty.not_disjoint

lemma disjoint_or_nonempty_inter (s t : finset α) : disjoint s t ∨ (s ∩ t).nonempty :=
by { rw ←not_disjoint_iff_nonempty_inter, exact em _ }

end lattice

/-! ### erase -/
section erase
variables [decidable_eq α] {s t u v : finset α} {a b : α}

/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
 not equal to `a`. -/
def erase (s : finset α) (a : α) : finset α := ⟨_, s.2.erase a⟩

@[simp] theorem erase_val (s : finset α) (a : α) : (erase s a).1 = s.1.erase a := rfl

@[simp] theorem mem_erase {a b : α} {s : finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
s.2.mem_erase_iff

lemma not_mem_erase (a : α) (s : finset α) : a ∉ erase s a := s.2.not_mem_erase

-- While this can be solved by `simp`, this lemma is eligible for `dsimp`
@[nolint simp_nf, simp] theorem erase_empty (a : α) : erase ∅ a = ∅ := rfl

@[simp] lemma erase_singleton (a : α) : ({a} : finset α).erase a = ∅ :=
begin
 ext x,
 rw [mem_erase]; rw [ mem_singleton]; rw [ not_and_self],
 refl,
end

lemma ne_of_mem_erase : b ∈ erase s a → b ≠ a := λ h, (mem_erase.1 h).1
lemma mem_of_mem_erase : b ∈ erase s a → b ∈ s := mem_of_mem_erase

lemma mem_erase_of_ne_of_mem : a ≠ b → a ∈ s → a ∈ erase s b :=
by simp only [mem_erase]; exact and.intro

/-- An element of `s` that is not an element of `erase s a` must be
`a`. -/
lemma eq_of_mem_of_not_mem_erase (hs : b ∈ s) (hsa : b ∉ s.erase a) : b = a :=
begin
 rw [mem_erase] at hsa; rw [ not_and] at hsa,
 exact not_imp_not.mp hsa hs
end

@[simp]
theorem erase_eq_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : erase s a = s :=
eq_of_veq $ erase_of_not_mem h

@[simp] lemma erase_eq_self : s.erase a = s ↔ a ∉ s :=
⟨λ h, h ▸ not_mem_erase _ _, erase_eq_of_not_mem⟩

@[simp] lemma erase_insert_eq_erase (s : finset α) (a : α) :
 (insert a s).erase a = s.erase a :=
ext $ λ x, by simp only [mem_erase, mem_insert, and.congr_right_iff, false_or, iff_self,
 implies_true_iff] { contextual := tt }

theorem erase_insert {a : α} {s : finset α} (h : a ∉ s) : erase (insert a s) a = s :=
by rw [erase_insert_eq_erase]; rw [ erase_eq_of_not_mem h]

theorem erase_insert_of_ne {a b : α} {s : finset α} (h : a ≠ b) :
 erase (insert a s) b = insert a (erase s b) :=
ext $ λ x, have x ≠ b ∧ x = a ↔ x = a, from and_iff_right_of_imp (λ hx, hx.symm ▸ h),
by simp only [mem_erase, mem_insert, and_or_distrib_left, this]

theorem erase_cons_of_ne {a b : α} {s : finset α} (ha : a ∉ s) (hb : a ≠ b) :
 erase (cons a s ha) b = cons a (erase s b) (λ h, ha $ erase_subset _ _ h) :=
by simp only [cons_eq_insert, erase_insert_of_ne hb]

theorem insert_erase {a : α} {s : finset α} (h : a ∈ s) : insert a (erase s a) = s :=
ext $ assume x, by simp only [mem_insert, mem_erase, or_and_distrib_left, dec_em, true_and];
apply or_iff_right_of_imp; rintro rfl; exact h

theorem erase_subset_erase (a : α) {s t : finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
val_le_iff.1 $ erase_le_erase _ $ val_le_iff.2 h

theorem erase_subset (a : α) (s : finset α) : erase s a ⊆ s := erase_subset _ _

lemma subset_erase {a : α} {s t : finset α} : s ⊆ t.erase a ↔ s ⊆ t ∧ a ∉ s :=
⟨λ h, ⟨h.trans (erase_subset _ _), λ ha, not_mem_erase _ _ (h ha)⟩,
 λ h b hb, mem_erase.2 ⟨ne_of_mem_of_not_mem hb h.2, h.1 hb⟩⟩

@[simp, norm_cast] lemma coe_erase (a : α) (s : finset α) : ↑(erase s a) = (s \ {a} : set α) :=
set.ext $ λ _, mem_erase.trans $ by rw [and_comm]; rw [ set.mem_diff]; rw [ set.mem_singleton_iff]; refl

lemma erase_ssubset {a : α} {s : finset α} (h : a ∈ s) : s.erase a ⊂ s :=
calc s.erase a ⊂ insert a (s.erase a) : ssubset_insert $ not_mem_erase _ _
 ... = _ : insert_erase h

lemma ssubset_iff_exists_subset_erase {s t : finset α} : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t.erase a :=
begin
 refine ⟨λ h, _, λ ⟨a, ha, h⟩, ssubset_of_subset_of_ssubset h $ erase_ssubset ha⟩,
 obtain ⟨a, ht, hs⟩ := not_subset.1 h.2,
 exact ⟨a, ht, subset_erase.2 ⟨h.1, hs⟩⟩,
end

lemma erase_ssubset_insert (s : finset α) (a : α) : s.erase a ⊂ insert a s :=
ssubset_iff_exists_subset_erase.2 ⟨a, mem_insert_self _ _, erase_subset_erase _ $ subset_insert _ _⟩

lemma erase_ne_self : s.erase a ≠ s ↔ a ∈ s := erase_eq_self.not_left

lemma erase_cons {s : finset α} {a : α} (h : a ∉ s) : (s.cons a h).erase a = s :=
by rw [cons_eq_insert]; rw [ erase_insert_eq_erase]; rw [ erase_eq_of_not_mem h]

lemma erase_idem {a : α} {s : finset α} : erase (erase s a) a = erase s a :=
by simp

lemma erase_right_comm {a b : α} {s : finset α} : erase (erase s a) b = erase (erase s b) a :=
by { ext x, simp only [mem_erase, ←and_assoc], rw and_comm (x ≠ a) }

theorem subset_insert_iff {a : α} {s t : finset α} : s ⊆ insert a t ↔ erase s a ⊆ t :=
by simp only [subset_iff, or_iff_not_imp_left, mem_erase, mem_insert, and_imp];
exact forall_congr (λ x, forall_swap)

theorem erase_insert_subset (a : α) (s : finset α) : erase (insert a s) a ⊆ s :=
subset_insert_iff.1 $ subset.rfl

theorem insert_erase_subset (a : α) (s : finset α) : s ⊆ insert a (erase s a) :=
subset_insert_iff.2 $ subset.rfl

lemma subset_insert_iff_of_not_mem (h : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t :=
by rw [subset_insert_iff]; rw [ erase_eq_of_not_mem h]

lemma erase_subset_iff_of_mem (h : a ∈ t) : s.erase a ⊆ t ↔ s ⊆ t :=
by rw [←subset_insert_iff]; rw [ insert_eq_of_mem h]

lemma erase_inj {x y : α} (s : finset α) (hx : x ∈ s) : s.erase x = s.erase y ↔ x = y :=
begin
 refine ⟨λ h, _, congr_arg _⟩,
 rw eq_of_mem_of_not_mem_erase hx,
 rw ←h,
 simp,
end

lemma erase_inj_on (s : finset α) : set.inj_on s.erase s := λ _ _ _ _, (erase_inj s ‹_›).mp

lemma erase_inj_on' (a : α) : {s : finset α | a ∈ s}.inj_on (λ s, erase s a) :=
λ s hs t ht (h : s.erase a = _), by rw [←insert_erase hs]; rw [ ←insert_erase ht]; rw [ h]

end erase

/-! ### sdiff -/

section sdiff
variables [decidable_eq α] {s t u v : finset α} {a b : α}

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance : has_sdiff (finset α) := ⟨λs₁ s₂, ⟨s₁.1 - s₂.1, nodup_of_le tsub_le_self s₁.2⟩⟩

@[simp] lemma sdiff_val (s₁ s₂ : finset α) : (s₁ \ s₂).val = s₁.val - s₂.val := rfl

@[simp] theorem mem_sdiff : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t := mem_sub_of_nodup s.2

@[simp] theorem inter_sdiff_self (s₁ s₂ : finset α) : s₁ ∩ (s₂ \ s₁) = ∅ :=
eq_empty_of_forall_not_mem $
by simp only [mem_inter, mem_sdiff]; rintro x ⟨h, _, hn⟩; exact hn h

instance : generalized_boolean_algebra (finset α) :=
{ sup_inf_sdiff := λ x y, by { simp only [ext_iff, mem_union, mem_sdiff, inf_eq_inter, sup_eq_union,
 mem_inter], tauto },
 inf_inf_sdiff := λ x y, by { simp only [ext_iff, inter_sdiff_self, inter_empty, inter_assoc,
 false_iff, inf_eq_inter, not_mem_empty], tauto },
 ..finset.has_sdiff,
 ..finset.distrib_lattice,
 ..finset.order_bot }

lemma not_mem_sdiff_of_mem_right (h : a ∈ t) : a ∉ s \ t :=
by simp only [mem_sdiff, h, not_true, not_false_iff, and_false]

lemma not_mem_sdiff_of_not_mem_left (h : a ∉ s) : a ∉ s \ t := by simpa

lemma union_sdiff_of_subset (h : s ⊆ t) : s ∪ (t \ s) = t := sup_sdiff_cancel_right h

theorem sdiff_union_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : (s₂ \ s₁) ∪ s₁ = s₂ :=
(union_comm _ _).trans (union_sdiff_of_subset h)

lemma inter_sdiff (s t u : finset α) : s ∩ (t \ u) = s ∩ t \ u := by { ext x, simp [and_assoc] }

@[simp] lemma sdiff_inter_self (s₁ s₂ : finset α) : (s₂ \ s₁) ∩ s₁ = ∅ := inf_sdiff_self_left

@[simp] protected lemma sdiff_self (s₁ : finset α) : s₁ \ s₁ = ∅ := sdiff_self

lemma sdiff_inter_distrib_right (s t u : finset α) : s \ (t ∩ u) = (s \ t) ∪ (s \ u) := sdiff_inf

@[simp] lemma sdiff_inter_self_left (s t : finset α) : s \ (s ∩ t) = s \ t :=
sdiff_inf_self_left _ _

@[simp] lemma sdiff_inter_self_right (s t : finset α) : s \ (t ∩ s) = s \ t :=
sdiff_inf_self_right _ _

@[simp] lemma sdiff_empty : s \ ∅ = s := sdiff_bot

@[mono] lemma sdiff_subset_sdiff (hst : s ⊆ t) (hvu : v ⊆ u) : s \ u ⊆ t \ v :=
sdiff_le_sdiff ‹s ≤ t› ‹v ≤ u›

@[simp, norm_cast] lemma coe_sdiff (s₁ s₂ : finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : set α) :=
set.ext $ λ _, mem_sdiff

@[simp] lemma union_sdiff_self_eq_union : s ∪ t \ s = s ∪ t := sup_sdiff_self_right _ _
@[simp] lemma sdiff_union_self_eq_union : s \ t ∪ t = s ∪ t := sup_sdiff_self_left _ _

lemma union_sdiff_left (s t : finset α) : (s ∪ t) \ s = t \ s := sup_sdiff_left_self
lemma union_sdiff_right (s t : finset α) : (s ∪ t) \ t = s \ t := sup_sdiff_right_self

lemma union_sdiff_cancel_left (h : disjoint s t) : (s ∪ t) \ s = t := h.sup_sdiff_cancel_left
lemma union_sdiff_cancel_right (h : disjoint s t) : (s ∪ t) \ t = s := h.sup_sdiff_cancel_right

lemma union_sdiff_symm : s ∪ (t \ s) = t ∪ (s \ t) := by simp [union_comm]

lemma sdiff_union_inter (s t : finset α) : (s \ t) ∪ (s ∩ t) = s := sup_sdiff_inf _ _

@[simp] lemma sdiff_idem (s t : finset α) : s \ t \ t = s \ t := sdiff_idem

lemma subset_sdiff : s ⊆ t \ u ↔ s ⊆ t ∧ disjoint s u := le_iff_subset.symm.trans le_sdiff

@[simp] lemma sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s ⊆ t := sdiff_eq_bot_iff

lemma sdiff_nonempty : (s \ t).nonempty ↔ ¬ s ⊆ t :=
nonempty_iff_ne_empty.trans sdiff_eq_empty_iff_subset.not

@[simp] lemma empty_sdiff (s : finset α) : ∅ \ s = ∅ := bot_sdiff

lemma insert_sdiff_of_not_mem (s : finset α) {t : finset α} {x : α} (h : x ∉ t) :
 (insert x s) \ t = insert x (s \ t) :=
begin
 rw [← coe_inj]; rw [ coe_insert]; rw [ coe_sdiff]; rw [ coe_sdiff]; rw [ coe_insert],
 exact set.insert_diff_of_not_mem s h
end

lemma insert_sdiff_of_mem (s : finset α) {x : α} (h : x ∈ t) : (insert x s) \ t = s \ t :=
begin
 rw [← coe_inj]; rw [ coe_sdiff]; rw [ coe_sdiff]; rw [ coe_insert],
 exact set.insert_diff_of_mem s h
end

@[simp] lemma insert_sdiff_insert (s t : finset α) (x : α) :
 (insert x s) \ (insert x t) = s \ insert x t :=
insert_sdiff_of_mem _ (mem_insert_self _ _)

lemma sdiff_insert_of_not_mem {x : α} (h : x ∉ s) (t : finset α) : s \ (insert x t) = s \ t :=
begin
 refine subset.antisymm (sdiff_subset_sdiff (subset.refl _) (subset_insert _ _)) (λ y hy, _),
 simp only [mem_sdiff, mem_insert, not_or_distrib] at hy ⊢,
 exact ⟨hy.1, λ hxy, h $ hxy ▸ hy.1, hy.2⟩
end

@[simp] lemma sdiff_subset (s t : finset α) : s \ t ⊆ s := show s \ t ≤ s, from sdiff_le

lemma sdiff_ssubset (h : t ⊆ s) (ht : t.nonempty) : s \ t ⊂ s := sdiff_lt ‹t ≤ s› ht.ne_empty

lemma union_sdiff_distrib (s₁ s₂ t : finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t := sup_sdiff
lemma sdiff_union_distrib (s t₁ t₂ : finset α) : s \ (t₁ ∪ t₂) = (s \ t₁) ∩ (s \ t₂) := sdiff_sup

lemma union_sdiff_self (s t : finset α) : (s ∪ t) \ t = s \ t := sup_sdiff_right_self

-- TODO: Do we want to delete this lemma and `finset.disj_union_singleton`,
-- or instead add `finset.union_singleton`/`finset.singleton_union`?
lemma sdiff_singleton_eq_erase (a : α) (s : finset α) : s \ singleton a = erase s a :=
by { ext, rw [mem_erase]; rw [ mem_sdiff]; rw [ mem_singleton], tauto }

-- This lemma matches `finset.insert_eq` in functionality.
lemma erase_eq (s : finset α) (a : α) : s.erase a = s \ {a} := (sdiff_singleton_eq_erase _ _).symm

lemma disjoint_erase_comm : disjoint (s.erase a) t ↔ disjoint s (t.erase a) :=
by simp_rw [erase_eq, disjoint_sdiff_comm]

lemma disjoint_of_erase_left (ha : a ∉ t) (hst : disjoint (s.erase a) t) : disjoint s t :=
by { rw [←erase_insert ha]; rw [ ←disjoint_erase_comm]; rw [ disjoint_insert_right],
 exact ⟨not_mem_erase _ _, hst⟩ }

lemma disjoint_of_erase_right (ha : a ∉ s) (hst : disjoint s (t.erase a)) : disjoint s t :=
by { rw [←erase_insert ha]; rw [ disjoint_erase_comm]; rw [ disjoint_insert_left],
 exact ⟨not_mem_erase _ _, hst⟩ }

@[simp] lemma inter_erase (a : α) (s t : finset α) : s ∩ t.erase a = (s ∩ t).erase a :=
by simp only [erase_eq, inter_sdiff]

@[simp] lemma erase_inter (a : α) (s t : finset α) : s.erase a ∩ t = (s ∩ t).erase a :=
by simpa only [inter_comm t] using inter_erase a t s

lemma erase_sdiff_comm (s t : finset α) (a : α) : s.erase a \ t = (s \ t).erase a :=
by simp_rw [erase_eq, sdiff_right_comm]

lemma insert_union_comm (s t : finset α) (a : α) : insert a s ∪ t = s ∪ insert a t :=
by rw [insert_union]; rw [ union_insert]

lemma erase_inter_comm (s t : finset α) (a : α) : s.erase a ∩ t = s ∩ t.erase a :=
by rw [erase_inter]; rw [ inter_erase]

lemma erase_union_distrib (s t : finset α) (a : α) : (s ∪ t).erase a = s.erase a ∪ t.erase a :=
by simp_rw [erase_eq, union_sdiff_distrib]

lemma insert_inter_distrib (s t : finset α) (a : α) : insert a (s ∩ t) = insert a s ∩ insert a t :=
by simp_rw [insert_eq, union_distrib_left]

lemma erase_sdiff_distrib (s t : finset α) (a : α) : (s \ t).erase a = s.erase a \ t.erase a :=
by simp_rw [erase_eq, sdiff_sdiff, sup_sdiff_eq_sup le_rfl, sup_comm]

lemma erase_union_of_mem (ha : a ∈ t) (s : finset α) : s.erase a ∪ t = s ∪ t :=
by rw [←insert_erase (mem_union_right s ha)]; rw [ erase_union_distrib]; rw [ ←union_insert]; rw [ insert_erase ha]

lemma union_erase_of_mem (ha : a ∈ s) (t : finset α) : s ∪ t.erase a = s ∪ t :=
by rw [←insert_erase (mem_union_left t ha)]; rw [ erase_union_distrib]; rw [ ←insert_union]; rw [ insert_erase ha]

@[simp] lemma sdiff_singleton_eq_self (ha : a ∉ s) : s \ {a} = s :=
sdiff_eq_self_iff_disjoint.2 $ by simp [ha]

lemma sdiff_sdiff_left' (s t u : finset α) :
 (s \ t) \ u = (s \ t) ∩ (s \ u) := sdiff_sdiff_left'

lemma sdiff_union_sdiff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
sdiff_sup_sdiff_cancel hts hut

lemma sdiff_union_erase_cancel (hts : t ⊆ s) (ha : a ∈ t) : s \ t ∪ t.erase a = s.erase a :=
by simp_rw [erase_eq, sdiff_union_sdiff_cancel hts (singleton_subset_iff.2 ha)]

lemma sdiff_sdiff_eq_sdiff_union (h : u ⊆ s) : s \ (t \ u) = s \ t ∪ u := sdiff_sdiff_eq_sdiff_sup h

lemma sdiff_insert (s t : finset α) (x : α) :
 s \ insert x t = (s \ t).erase x :=
by simp_rw [← sdiff_singleton_eq_erase, insert_eq, sdiff_sdiff_left', sdiff_union_distrib, inter_comm]

lemma sdiff_insert_insert_of_mem_of_not_mem {s t : finset α} {x : α} (hxs : x ∈ s) (hxt : x ∉ t) :
 insert x (s \ insert x t) = s \ t :=
by rw [sdiff_insert]; rw [ insert_erase (mem_sdiff.mpr ⟨hxs, hxt⟩)]

lemma sdiff_erase (h : a ∈ s) : s \ t.erase a = insert a (s \ t) :=
by rw [←sdiff_singleton_eq_erase]; rw [ sdiff_sdiff_eq_sdiff_union (singleton_subset_iff.2 h)]; rw [ insert_eq]; rw [ union_comm]

lemma sdiff_erase_self (ha : a ∈ s) : s \ s.erase a = {a} :=
by rw [sdiff_erase ha]; rw [ finset.sdiff_self]; rw [ insert_emptyc_eq]

lemma sdiff_sdiff_self_left (s t : finset α) : s \ (s \ t) = s ∩ t := sdiff_sdiff_right_self

lemma sdiff_sdiff_eq_self (h : t ⊆ s) : s \ (s \ t) = t := sdiff_sdiff_eq_self h

lemma sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : finset α} : s \ t₁ = s \ t₂ ↔ s ∩ t₁ = s ∩ t₂ :=
sdiff_eq_sdiff_iff_inf_eq_inf

lemma union_eq_sdiff_union_sdiff_union_inter (s t : finset α) :
 s ∪ t = (s \ t) ∪ (t \ s) ∪ (s ∩ t) :=
sup_eq_sdiff_sup_sdiff_sup_inf

lemma erase_eq_empty_iff (s : finset α) (a : α) : s.erase a = ∅ ↔ s = ∅ ∨ s = {a} :=
by rw [←sdiff_singleton_eq_erase]; rw [ sdiff_eq_empty_iff_subset]; rw [ subset_singleton_iff]

--TODO@Yaël: Kill lemmas duplicate with `boolean_algebra`
lemma sdiff_disjoint : disjoint (t \ s) s := disjoint_left.2 $ assume a ha, (mem_sdiff.1 ha).2
lemma disjoint_sdiff : disjoint s (t \ s) := sdiff_disjoint.symm

lemma disjoint_sdiff_inter (s t : finset α) : disjoint (s \ t) (s ∩ t) :=
disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint

lemma sdiff_eq_self_iff_disjoint : s \ t = s ↔ disjoint s t := sdiff_eq_self_iff_disjoint'
lemma sdiff_eq_self_of_disjoint (h : disjoint s t) : s \ t = s := sdiff_eq_self_iff_disjoint.2 h

end sdiff

/-! ### Symmetric difference -/

section symm_diff
variables [decidable_eq α] {s t : finset α} {a b : α}

lemma mem_symm_diff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s :=
by simp_rw [symm_diff, sup_eq_union, mem_union, mem_sdiff]

@[simp, norm_cast] lemma coe_symm_diff : (↑(s ∆ t) : set α) = s ∆ t := set.ext $ λ _, mem_symm_diff

end symm_diff

/-! ### attach -/

/-- `attach s` takes the elements of `s` and forms a new set of elements of the subtype
`{x // x ∈ s}`. -/
def attach (s : finset α) : finset {x // x ∈ s} := ⟨attach s.1, nodup_attach.2 s.2⟩

theorem sizeof_lt_sizeof_of_mem [has_sizeof α] {x : α} {s : finset α} (hx : x ∈ s) :
 sizeof x < sizeof s := by
{ cases s, dsimp [sizeof, has_sizeof.sizeof, finset.sizeof],
 apply lt_add_left, exact multiset.sizeof_lt_sizeof_of_mem hx }

@[simp] theorem attach_val (s : finset α) : s.attach.1 = s.1.attach := rfl

@[simp] theorem mem_attach (s : finset α) : ∀ x, x ∈ s.attach := mem_attach _

@[simp] theorem attach_empty : attach (∅ : finset α) = ∅ := rfl

@[simp] lemma attach_nonempty_iff {s : finset α} : s.attach.nonempty ↔ s.nonempty :=
by simp [finset.nonempty]

@[simp] lemma attach_eq_empty_iff {s : finset α} : s.attach = ∅ ↔ s = ∅ :=
by simpa [eq_empty_iff_forall_not_mem]

/-! ### piecewise -/

section piecewise

/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
def piecewise {α : Type*} {δ : α → Sort*} (s : finset α) (f g : Π i, δ i) [Π j, decidable (j ∈ s)] :
 Π i, δ i :=
λi, if i ∈ s then f i else g i

variables {δ : α → Sort*} (s : finset α) (f g : Π i, δ i)

@[simp] lemma piecewise_insert_self [decidable_eq α] {j : α} [∀ i, decidable (i ∈ insert j s)] :
 (insert j s).piecewise f g j = f j :=
by simp [piecewise]

@[simp] lemma piecewise_empty [Π i : α, decidable (i ∈ (∅ : finset α))] : piecewise ∅ f g = g :=
by { ext i, simp [piecewise] }

variable [Π j, decidable (j ∈ s)]

-- TODO: fix this in norm_cast
@[norm_cast move] lemma piecewise_coe [∀ j, decidable (j ∈ (s : set α))] :
 (s : set α).piecewise f g = s.piecewise f g :=
by { ext, congr }

@[simp, priority 980]
lemma piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i := by simp [piecewise, hi]

@[simp, priority 980]
lemma piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
by simp [piecewise, hi]

lemma piecewise_congr {f f' g g' : Π i, δ i} (hf : ∀ i ∈ s, f i = f' i) (hg : ∀ i ∉ s, g i = g' i) :
 s.piecewise f g = s.piecewise f' g' :=
funext $ λ i, if_ctx_congr iff.rfl (hf i) (hg i)

@[simp, priority 990]
lemma piecewise_insert_of_ne [decidable_eq α] {i j : α} [∀ i, decidable (i ∈ insert j s)]
 (h : i ≠ j) : (insert j s).piecewise f g i = s.piecewise f g i :=
by simp [piecewise, h]

lemma piecewise_insert [decidable_eq α] (j : α) [∀ i, decidable (i ∈ insert j s)] :
 (insert j s).piecewise f g = update (s.piecewise f g) j (f j) :=
by { classical, simp only [← piecewise_coe, coe_insert, ← set.piecewise_insert] }

lemma piecewise_cases {i} (p : δ i → Prop) (hf : p (f i)) (hg : p (g i)) : p (s.piecewise f g i) :=
by by_cases hi : i ∈ s; simpa [hi]

lemma piecewise_mem_set_pi {δ : α → Type*} {t : set α} {t' : Π i, set (δ i)}
 {f g} (hf : f ∈ set.pi t t') (hg : g ∈ set.pi t t') : s.piecewise f g ∈ set.pi t t' :=
by { classical, rw ← piecewise_coe, exact set.piecewise_mem_pi ↑s hf hg }

lemma piecewise_singleton [decidable_eq α] (i : α) :
 piecewise {i} f g = update g i (f i) :=
by rw [← insert_emptyc_eq]; rw [ piecewise_insert]; rw [ piecewise_empty]

lemma piecewise_piecewise_of_subset_left {s t : finset α} [Π i, decidable (i ∈ s)]
 [Π i, decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : Π a, δ a) :
 s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
s.piecewise_congr (λ i hi, piecewise_eq_of_mem _ _ _ (h hi)) (λ _ _, rfl)

@[simp] lemma piecewise_idem_left (f₁ f₂ g : Π a, δ a) :
 s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
piecewise_piecewise_of_subset_left (subset.refl _) _ _ _

lemma piecewise_piecewise_of_subset_right {s t : finset α} [Π i, decidable (i ∈ s)]
 [Π i, decidable (i ∈ t)] (h : t ⊆ s) (f g₁ g₂ : Π a, δ a) :
 s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
s.piecewise_congr (λ _ _, rfl) (λ i hi, t.piecewise_eq_of_not_mem _ _ (mt (@h _) hi))

@[simp] lemma piecewise_idem_right (f g₁ g₂ : Π a, δ a) :
 s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
piecewise_piecewise_of_subset_right (subset.refl _) f g₁ g₂

lemma update_eq_piecewise {β : Type*} [decidable_eq α] (f : α → β) (i : α) (v : β) :
 update f i v = piecewise (singleton i) (λj, v) f :=
(piecewise_singleton _ _ _).symm

lemma update_piecewise [decidable_eq α] (i : α) (v : δ i) :
 update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) :=
begin
 ext j,
 rcases em (j = i) with (rfl|hj); by_cases hs : j ∈ s; simp *
end

lemma update_piecewise_of_mem [decidable_eq α] {i : α} (hi : i ∈ s) (v : δ i) :
 update (s.piecewise f g) i v = s.piecewise (update f i v) g :=
begin
 rw update_piecewise,
 refine s.piecewise_congr (λ _ _, rfl) (λ j hj, update_noteq _ _ _),
 exact λ h, hj (h.symm ▸ hi)
end

lemma update_piecewise_of_not_mem [decidable_eq α] {i : α} (hi : i ∉ s) (v : δ i) :
 update (s.piecewise f g) i v = s.piecewise f (update g i v) :=
begin
 rw update_piecewise,
 refine s.piecewise_congr (λ j hj, update_noteq _ _ _) (λ _ _, rfl),
 exact λ h, hi (h ▸ hj)
end

lemma piecewise_le_of_le_of_le {δ : α → Type*} [Π i, preorder (δ i)] {f g h : Π i, δ i}
 (Hf : f ≤ h) (Hg : g ≤ h) : s.piecewise f g ≤ h :=
λ x, piecewise_cases s f g (≤ h x) (Hf x) (Hg x)

lemma le_piecewise_of_le_of_le {δ : α → Type*} [Π i, preorder (δ i)] {f g h : Π i, δ i}
 (Hf : h ≤ f) (Hg : h ≤ g) : h ≤ s.piecewise f g :=
λ x, piecewise_cases s f g (λ y, h x ≤ y) (Hf x) (Hg x)

lemma piecewise_le_piecewise' {δ : α → Type*} [Π i, preorder (δ i)] {f g f' g' : Π i, δ i}
 (Hf : ∀ x ∈ s, f x ≤ f' x) (Hg : ∀ x ∉ s, g x ≤ g' x) : s.piecewise f g ≤ s.piecewise f' g' :=
λ x, by { by_cases hx : x ∈ s; simp [hx, *] }

lemma piecewise_le_piecewise {δ : α → Type*} [Π i, preorder (δ i)] {f g f' g' : Π i, δ i}
 (Hf : f ≤ f') (Hg : g ≤ g') : s.piecewise f g ≤ s.piecewise f' g' :=
s.piecewise_le_piecewise' (λ x _, Hf x) (λ x _, Hg x)

lemma piecewise_mem_Icc_of_mem_of_mem {δ : α → Type*} [Π i, preorder (δ i)] {f f₁ g g₁ : Π i, δ i}
 (hf : f ∈ set.Icc f₁ g₁) (hg : g ∈ set.Icc f₁ g₁) :
 s.piecewise f g ∈ set.Icc f₁ g₁ :=
⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩

lemma piecewise_mem_Icc {δ : α → Type*} [Π i, preorder (δ i)] {f g : Π i, δ i} (h : f ≤ g) :
 s.piecewise f g ∈ set.Icc f g :=
piecewise_mem_Icc_of_mem_of_mem _ (set.left_mem_Icc.2 h) (set.right_mem_Icc.2 h)

lemma piecewise_mem_Icc' {δ : α → Type*} [Π i, preorder (δ i)] {f g : Π i, δ i} (h : g ≤ f) :
 s.piecewise f g ∈ set.Icc g f :=
piecewise_mem_Icc_of_mem_of_mem _ (set.right_mem_Icc.2 h) (set.left_mem_Icc.2 h)

end piecewise

section decidable_pi_exists
variables {s : finset α}

instance decidable_dforall_finset {p : Π a ∈ s, Prop} [hp : ∀ a (h : a ∈ s), decidable (p a h)] :
 decidable (∀ a (h : a ∈ s), p a h) :=
multiset.decidable_dforall_multiset

/-- decidable equality for functions whose domain is bounded by finsets -/
instance decidable_eq_pi_finset {β : α → Type*} [h : ∀ a, decidable_eq (β a)] :
 decidable_eq (Π a ∈ s, β a) :=
multiset.decidable_eq_pi_multiset

instance decidable_dexists_finset {p : Π a ∈ s, Prop} [hp : ∀ a (h : a ∈ s), decidable (p a h)] :
 decidable (∃ a (h : a ∈ s), p a h) :=
multiset.decidable_dexists_multiset

end decidable_pi_exists

/-! ### filter -/
section filter
variables (p q : α → Prop) [decidable_pred p] [decidable_pred q] {s : finset α}

/-- `filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (s : finset α) : finset α := ⟨_, s.2.filter p⟩

@[simp] theorem filter_val (s : finset α) : (filter p s).1 = s.1.filter p := rfl

@[simp] theorem filter_subset (s : finset α) : s.filter p ⊆ s := filter_subset _ _

variable {p}

@[simp] theorem mem_filter {s : finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a := mem_filter

lemma mem_of_mem_filter {s : finset α} (x : α) (h : x ∈ s.filter p) : x ∈ s :=
mem_of_mem_filter h

theorem filter_ssubset {s : finset α} : s.filter p ⊂ s ↔ ∃ x ∈ s, ¬ p x :=
⟨λ h, let ⟨x, hs, hp⟩ := set.exists_of_ssubset h in ⟨x, hs, mt (λ hp, mem_filter.2 ⟨hs, hp⟩) hp⟩,
 λ ⟨x, hs, hp⟩, ⟨s.filter_subset _, λ h, hp (mem_filter.1 (h hs)).2⟩⟩

variable (p)

theorem filter_filter (s : finset α) : (s.filter p).filter q = s.filter (λa, p a ∧ q a) :=
ext $ assume a, by simp only [mem_filter, and_comm, and.left_comm]

lemma filter_comm (s : finset α) : (s.filter p).filter q = (s.filter q).filter p :=
by simp_rw [filter_filter, and_comm]

/- We can simplify an application of filter where the decidability is inferred in "the wrong way" -/
@[simp] lemma filter_congr_decidable (s : finset α) (p : α → Prop) (h : decidable_pred p)
 [decidable_pred p] : @filter α p h s = s.filter p :=
by congr

lemma filter_true {h} (s : finset α) : @filter α (λ a, true) h s = s := by ext; simp
lemma filter_false {h} (s : finset α) : @filter α (λ a, false) h s = ∅ := by ext; simp

variables {p q}

lemma filter_eq_self : s.filter p = s ↔ ∀ ⦃x⦄, x ∈ s → p x := by simp [finset.ext_iff]
lemma filter_eq_empty_iff : s.filter p = ∅ ↔ ∀ ⦃x⦄, x ∈ s → ¬ p x := by simp [finset.ext_iff]

lemma filter_nonempty_iff {s : finset α} : (s.filter p).nonempty ↔ ∃ a ∈ s, p a :=
by simp only [nonempty_iff_ne_empty, ne.def, filter_eq_empty_iff, not_not, not_forall]

/-- If all elements of a `finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
@[simp] lemma filter_true_of_mem (h : ∀ x ∈ s, p x) : s.filter p = s := filter_eq_self.2 h

/-- If all elements of a `finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
@[simp] lemma filter_false_of_mem (h : ∀ x ∈ s, ¬ p x) : s.filter p = ∅ := filter_eq_empty_iff.2 h

@[simp] lemma filter_const (p : Prop) [decidable p] (s : finset α) :
 s.filter (λ a, p) = if p then s else ∅ :=
by split_ifs; simp [*]

lemma filter_congr {s : finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
eq_of_veq $ filter_congr H

variables (p q)

lemma filter_empty : filter p ∅ = ∅ := subset_empty.1 $ filter_subset _ _

lemma filter_subset_filter {s t : finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p :=
assume a ha, mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

lemma monotone_filter_left : monotone (filter p) :=
λ _ _, filter_subset_filter p

lemma monotone_filter_right (s : finset α) ⦃p q : α → Prop⦄
 [decidable_pred p] [decidable_pred q] (h : p ≤ q) :
 s.filter p ≤ s.filter q :=
multiset.subset_of_le (multiset.monotone_filter_right s.val h)

@[simp, norm_cast] lemma coe_filter (s : finset α) : ↑(s.filter p) = ({x ∈ ↑s | p x} : set α) :=
set.ext $ λ _, mem_filter

lemma subset_coe_filter_of_subset_forall (s : finset α) {t : set α}
 (h₁ : t ⊆ s) (h₂ : ∀ x ∈ t, p x) : t ⊆ s.filter p :=
λ x hx, (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩

theorem filter_singleton (a : α) : filter p (singleton a) = if p a then singleton a else ∅ :=
by { classical, ext x, simp, split_ifs with h; by_cases h' : x = a; simp [h, h'] }

theorem filter_cons_of_pos (a : α) (s : finset α) (ha : a ∉ s) (hp : p a):
 filter p (cons a s ha) = cons a (filter p s) (mem_filter.not.mpr $ mt and.left ha) :=
eq_of_veq $ multiset.filter_cons_of_pos s.val hp

theorem filter_cons_of_neg (a : α) (s : finset α) (ha : a ∉ s) (hp : ¬p a):
 filter p (cons a s ha) = filter p s :=
eq_of_veq $ multiset.filter_cons_of_neg s.val hp

lemma disjoint_filter {s : finset α} {p q : α → Prop} [decidable_pred p] [decidable_pred q] :
 disjoint (s.filter p) (s.filter q) ↔ ∀ x ∈ s, p x → ¬ q x :=
by split; simp [disjoint_left] {contextual := tt}

lemma disjoint_filter_filter {s t : finset α} {p q : α → Prop}
 [decidable_pred p] [decidable_pred q] :
 disjoint s t → disjoint (s.filter p) (t.filter q) :=
disjoint.mono (filter_subset _ _) (filter_subset _ _)

lemma disjoint_filter_filter' (s t : finset α) {p q : α → Prop}
 [decidable_pred p] [decidable_pred q] (h : disjoint p q) :
 disjoint (s.filter p) (t.filter q) :=
begin
 simp_rw [disjoint_left, mem_filter],
 rintros a ⟨hs, hp⟩ ⟨ht, hq⟩,
 exact h.le_bot _ ⟨hp, hq⟩,
end

lemma disjoint_filter_filter_neg (s t : finset α) (p : α → Prop)
 [decidable_pred p] [decidable_pred (λ a, ¬ p a)] :
 disjoint (s.filter p) (t.filter $ λ a, ¬ p a) :=
disjoint_filter_filter' s t disjoint_compl_right

theorem filter_disj_union (s : finset α) (t : finset α) (h : disjoint s t) :
 filter p (disj_union s t h) = (filter p s).disj_union (filter p t)
 (disjoint_filter_filter h) :=
eq_of_veq $ multiset.filter_add _ _ _

theorem filter_cons {a : α} (s : finset α) (ha : a ∉ s) :
 filter p (cons a s ha) = (if p a then {a} else ∅ : finset α).disj_union (filter p s) (by
 { split_ifs,
 { rw disjoint_singleton_left,
 exact (mem_filter.not.mpr $ mt and.left ha) },
 { exact disjoint_empty_left _ } }) :=
begin
 split_ifs with h,
 { rw [filter_cons_of_pos _ _ _ ha h]; rw [ singleton_disj_union] },
 { rw [filter_cons_of_neg _ _ _ ha h]; rw [ empty_disj_union] },
end

variable [decidable_eq α]

theorem filter_union (s₁ s₂ : finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
ext $ λ _, by simp only [mem_filter, mem_union, or_and_distrib_right]

theorem filter_union_right (s : finset α) : s.filter p ∪ s.filter q = s.filter (λx, p x ∨ q x) :=
ext $ λ x, by simp only [mem_filter, mem_union, and_or_distrib_left.symm]

lemma filter_mem_eq_inter {s t : finset α} [Π i, decidable (i ∈ t)] :
 s.filter (λ i, i ∈ t) = s ∩ t :=
ext $ λ i, by rw [mem_filter]; rw [ mem_inter]

lemma filter_inter_distrib (s t : finset α) : (s ∩ t).filter p = s.filter p ∩ t.filter p :=
by { ext, simp only [mem_filter, mem_inter], exact and_and_distrib_right _ _ _ }

theorem filter_inter (s t : finset α) : filter p s ∩ t = filter p (s ∩ t) :=
by { ext, simp only [mem_inter, mem_filter, and.right_comm] }

theorem inter_filter (s t : finset α) : s ∩ filter p t = filter p (s ∩ t) :=
by rw [inter_comm]; rw [ filter_inter]; rw [ inter_comm]

theorem filter_insert (a : α) (s : finset α) :
 filter p (insert a s) = if p a then insert a (filter p s) else filter p s :=
by { ext x, simp, split_ifs with h; by_cases h' : x = a; simp [h, h'] }

theorem filter_erase (a : α) (s : finset α) : filter p (erase s a) = erase (filter p s) a :=
by { ext x, simp only [and_assoc, mem_filter, iff_self, mem_erase] }

theorem filter_or [decidable_pred (λ a, p a ∨ q a)] (s : finset α) :
 s.filter (λ a, p a ∨ q a) = s.filter p ∪ s.filter q :=
ext $ λ _, by simp only [mem_filter, mem_union, and_or_distrib_left]

theorem filter_and [decidable_pred (λ a, p a ∧ q a)] (s : finset α) :
 s.filter (λ a, p a ∧ q a) = s.filter p ∩ s.filter q :=
ext $ λ _, by simp only [mem_filter, mem_inter, and_comm, and.left_comm, and_self]

theorem filter_not [decidable_pred (λ a, ¬ p a)] (s : finset α) :
 s.filter (λ a, ¬ p a) = s \ s.filter p :=
ext $ by simpa only [mem_filter, mem_sdiff, and_comm, not_and] using λ a, and_congr_right $
 λ h : a ∈ s, (imp_iff_right h).symm.trans imp_not_comm

theorem sdiff_eq_filter (s₁ s₂ : finset α) :
 s₁ \ s₂ = filter (∉ s₂) s₁ := ext $ λ _, by simp only [mem_sdiff, mem_filter]

lemma sdiff_eq_self (s₁ s₂ : finset α) : s₁ \ s₂ = s₁ ↔ s₁ ∩ s₂ ⊆ ∅ :=
by { simp [subset.antisymm_iff],
 split; intro h,
 { transitivity' ((s₁ \ s₂) ∩ s₂), mono, simp },
 { calc s₁ \ s₂
 ⊇ s₁ \ (s₁ ∩ s₂) : by simp [(⊇)]
 ... ⊇ s₁ \ ∅ : by mono using [(⊇)]
 ... ⊇ s₁ : by simp [(⊇)] } }

lemma subset_union_elim {s : finset α} {t₁ t₂ : set α} (h : ↑s ⊆ t₁ ∪ t₂) :
 ∃ s₁ s₂ : finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ :=
begin
 classical,
 refine ⟨s.filter (∈ t₁), s.filter (∉ t₁), _, _ , _⟩,
 { simp [filter_union_right, em] },
 { intro x, simp },
 { intro x, simp, intros hx hx₂, refine ⟨or.resolve_left (h hx) hx₂, hx₂⟩ }
end

section classical
open_locale classical
/-- The following instance allows us to write `{x ∈ s | p x}` for `finset.filter p s`.
 Since the former notation requires us to define this for all propositions `p`, and `finset.filter`
 only works for decidable propositions, the notation `{x ∈ s | p x}` is only compatible with
 classical logic because it uses `classical.prop_decidable`.
 We don't want to redo all lemmas of `finset.filter` for `has_sep.sep`, so we make sure that `simp`
 unfolds the notation `{x ∈ s | p x}` to `finset.filter p s`. If `p` happens to be decidable, the
 simp-lemma `finset.filter_congr_decidable` will make sure that `finset.filter` uses the right
 instance for decidability.
-/
noncomputable instance {α : Type*} : has_sep α (finset α) := ⟨λ p x, x.filter p⟩

@[simp] lemma sep_def {α : Type*} (s : finset α) (p : α → Prop) : {x ∈ s | p x} = s.filter p := rfl

end classical

/--
 After filtering out everything that does not equal a given value, at most that value remains.

 This is equivalent to `filter_eq'` with the equality the other way.
-/
-- This is not a good simp lemma, as it would prevent `finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter(eq b)`.
lemma filter_eq [decidable_eq β] (s : finset β) (b : β) : s.filter (eq b) = ite (b ∈ s) {b} ∅ :=
begin
 split_ifs,
 { ext,
 simp only [mem_filter, mem_singleton],
 exact ⟨λ h, h.2.symm, by { rintro ⟨h⟩, exact ⟨h, rfl⟩ }⟩ },
 { ext,
 simp only [mem_filter, not_and, iff_false, not_mem_empty],
 rintro m ⟨e⟩, exact h m }
end

/--
 After filtering out everything that does not equal a given value, at most that value remains.

 This is equivalent to `filter_eq` with the equality the other way.
-/
lemma filter_eq' [decidable_eq β] (s : finset β) (b : β) :
 s.filter (λ a, a = b) = ite (b ∈ s) {b} ∅ :=
trans (filter_congr (λ _ _, ⟨eq.symm, eq.symm⟩)) (filter_eq s b)

lemma filter_ne [decidable_eq β] (s : finset β) (b : β) : s.filter (λ a, b ≠ a) = s.erase b :=
by { ext, simp only [mem_filter, mem_erase, ne.def], tauto }

lemma filter_ne' [decidable_eq β] (s : finset β) (b : β) : s.filter (λ a, a ≠ b) = s.erase b :=
trans (filter_congr (λ _ _, ⟨ne.symm, ne.symm⟩)) (filter_ne s b)

theorem filter_inter_filter_neg_eq [decidable_pred (λ a, ¬ p a)] (s t : finset α) :
 s.filter p ∩ t.filter (λa, ¬ p a) = ∅ :=
(disjoint_filter_filter_neg s t p).eq_bot

theorem filter_union_filter_of_codisjoint (s : finset α) (h : codisjoint p q) :
 s.filter p ∪ s.filter q = s :=
(filter_or _ _ _).symm.trans $ filter_true_of_mem $ λ x hx, h.top_le x trivial

theorem filter_union_filter_neg_eq [decidable_pred (λ a, ¬ p a)] (s : finset α) :
 s.filter p ∪ s.filter (λa, ¬ p a) = s :=
filter_union_filter_of_codisjoint _ _ _ codisjoint_hnot_right

end filter

/-! ### range -/

section range
variables {n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : finset ℕ := ⟨_, nodup_range n⟩

@[simp] theorem range_val (n : ℕ) : (range n).1 = multiset.range n := rfl

@[simp] theorem mem_range : m ∈ range n ↔ m < n := mem_range

@[simp, norm_cast] lemma coe_range (n : ℕ) : (range n : set ℕ) = set.Iio n :=
set.ext $ λ _, mem_range

@[simp] theorem range_zero : range 0 = ∅ := rfl

@[simp] theorem range_one : range 1 = {0} := rfl

theorem range_succ : range (succ n) = insert n (range n) :=
eq_of_veq $ (range_succ n).trans $ (ndinsert_of_not_mem not_mem_range_self).symm

lemma range_add_one : range (n + 1) = insert n (range n) := range_succ

@[simp] theorem not_mem_range_self : n ∉ range n := not_mem_range_self

@[simp] theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := multiset.self_mem_range_succ n

@[simp] theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m := range_subset

theorem range_mono : monotone range := λ _ _, range_subset.2

lemma mem_range_succ_iff {a b : ℕ} : a ∈ finset.range b.succ ↔ a ≤ b :=
finset.mem_range.trans nat.lt_succ_iff

lemma mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n := (mem_range.1 hx).le

lemma mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 :=
ne_of_gt $ tsub_pos_of_lt $ mem_range.1 hx

@[simp] lemma nonempty_range_iff : (range n).nonempty ↔ n ≠ 0 :=
⟨λ ⟨k, hk⟩, ((zero_le k).trans_lt $ mem_range.1 hk).ne',
 λ h, ⟨0, mem_range.2 $ pos_iff_ne_zero.2 h⟩⟩

@[simp] lemma range_eq_empty_iff : range n = ∅ ↔ n = 0 :=
by rw [← not_nonempty_iff_eq_empty]; rw [ nonempty_range_iff]; rw [ not_not]

lemma nonempty_range_succ : (range $ n + 1).nonempty :=
nonempty_range_iff.2 n.succ_ne_zero

@[simp]
lemma range_filter_eq {n m : ℕ} : (range n).filter (= m) = if m < n then {m} else ∅ :=
begin
 convert filter_eq (range n) m,
 { ext, exact comm },
 { simp }
end

end range

/- useful rules for calculations with quantifiers -/
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : finset α) ∧ p x) ↔ false :=
by simp only [not_mem_empty, false_and, exists_false]

lemma exists_mem_insert [decidable_eq α] (a : α) (s : finset α) (p : α → Prop) :
 (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ x, x ∈ s ∧ p x :=
by simp only [mem_insert, or_and_distrib_right, exists_or_distrib, exists_eq_left]

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : finset α) → p x) ↔ true :=
iff_true_intro $ λ _, false.elim

lemma forall_mem_insert [decidable_eq α] (a : α) (s : finset α) (p : α → Prop) :
 (∀ x, x ∈ insert a s → p x) ↔ p a ∧ ∀ x, x ∈ s → p x :=
by simp only [mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

/-- Useful in proofs by induction. -/
lemma forall_of_forall_insert [decidable_eq α] {p : α → Prop} {a : α} {s : finset α}
 (H : ∀ x, x ∈ insert a s → p x) (x) (h : x ∈ s) : p x := H _ $ mem_insert_of_mem h

end finset

/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
def not_mem_range_equiv (k : ℕ) : {n // n ∉ range k} ≃ ℕ :=
{ to_fun := λ i, i.1 - k,
 inv_fun := λ j, ⟨j + k, by simp⟩,
 left_inv := λ j,
 begin
 rw subtype.ext_iff_val,
 apply tsub_add_cancel_of_le,
 simpa using j.2
 end,
 right_inv := λ j, add_tsub_cancel_right _ _ }

@[simp] lemma coe_not_mem_range_equiv (k : ℕ) :
 (not_mem_range_equiv k : {n // n ∉ range k} → ℕ) = (λ i, i - k) := rfl

@[simp] lemma coe_not_mem_range_equiv_symm (k : ℕ) :
 ((not_mem_range_equiv k).symm : ℕ → {n // n ∉ range k}) = λ j, ⟨j + k, by simp⟩ := rfl

/-! ### dedup on list and multiset -/

namespace multiset
variables [decidable_eq α] {s t : multiset α}

/-- `to_finset s` removes duplicates from the multiset `s` to produce a finset. -/
def to_finset (s : multiset α) : finset α := ⟨_, nodup_dedup s⟩

@[simp] theorem to_finset_val (s : multiset α) : s.to_finset.1 = s.dedup := rfl

theorem to_finset_eq {s : multiset α} (n : nodup s) : finset.mk s n = s.to_finset :=
finset.val_inj.1 n.dedup.symm

lemma nodup.to_finset_inj {l l' : multiset α} (hl : nodup l) (hl' : nodup l')
 (h : l.to_finset = l'.to_finset) : l = l' :=
by simpa [←to_finset_eq hl, ←to_finset_eq hl'] using h

@[simp] lemma mem_to_finset {a : α} {s : multiset α} : a ∈ s.to_finset ↔ a ∈ s := mem_dedup

@[simp] lemma to_finset_zero : to_finset (0 : multiset α) = ∅ := rfl

@[simp] lemma to_finset_cons (a : α) (s : multiset α) :
 to_finset (a ::ₘ s) = insert a (to_finset s) :=
finset.eq_of_veq dedup_cons

@[simp] lemma to_finset_singleton (a : α) : to_finset ({a} : multiset α) = {a} :=
by rw [←cons_zero]; rw [ to_finset_cons]; rw [ to_finset_zero]; rw [ is_lawful_singleton.insert_emptyc_eq]

@[simp] lemma to_finset_add (s t : multiset α) : to_finset (s + t) = to_finset s ∪ to_finset t :=
finset.ext $ by simp

@[simp] lemma to_finset_nsmul (s : multiset α) :
 ∀ (n : ℕ) (hn : n ≠ 0), (n • s).to_finset = s.to_finset
| 0 h := by contradiction
| (n+1) h :=
 begin
 by_cases n = 0,
 { rw [h]; rw [ zero_add]; rw [ one_nsmul] },
 { rw [add_nsmul]; rw [ to_finset_add]; rw [ one_nsmul]; rw [ to_finset_nsmul n h]; rw [ finset.union_idempotent] }
 end

@[simp] lemma to_finset_inter (s t : multiset α) : to_finset (s ∩ t) = to_finset s ∩ to_finset t :=
finset.ext $ by simp

@[simp] lemma to_finset_union (s t : multiset α) : (s ∪ t).to_finset = s.to_finset ∪ t.to_finset :=
by ext; simp

@[simp] theorem to_finset_eq_empty {m : multiset α} : m.to_finset = ∅ ↔ m = 0 :=
finset.val_inj.symm.trans multiset.dedup_eq_zero

@[simp] lemma to_finset_nonempty : s.to_finset.nonempty ↔ s ≠ 0 :=
by simp only [to_finset_eq_empty, ne.def, finset.nonempty_iff_ne_empty]

@[simp] lemma to_finset_subset : s.to_finset ⊆ t.to_finset ↔ s ⊆ t :=
by simp only [finset.subset_iff, multiset.subset_iff, multiset.mem_to_finset]

@[simp] lemma to_finset_ssubset : s.to_finset ⊂ t.to_finset ↔ s ⊂ t :=
by { simp_rw [finset.ssubset_def, to_finset_subset], refl }

@[simp] lemma to_finset_dedup (m : multiset α) :
 m.dedup.to_finset = m.to_finset :=
by simp_rw [to_finset, dedup_idempotent]

@[simp] lemma to_finset_bind_dedup [decidable_eq β] (m : multiset α) (f : α → multiset β) :
 (m.dedup.bind f).to_finset = (m.bind f).to_finset :=
by simp_rw [to_finset, dedup_bind_dedup]

instance is_well_founded_ssubset : is_well_founded (multiset β) (⊂) :=
subrelation.is_well_founded (inv_image _ _) $ λ _ _, by classical; exact to_finset_ssubset.2

end multiset

namespace finset

@[simp] lemma val_to_finset [decidable_eq α] (s : finset α) : s.val.to_finset = s :=
by { ext, rw [multiset.mem_to_finset]; rw [ ←mem_def] }

lemma val_le_iff_val_subset {a : finset α} {b : multiset α} : a.val ≤ b ↔ a.val ⊆ b :=
multiset.le_iff_subset a.nodup

end finset

namespace list
variables [decidable_eq α] {l l' : list α} {a : α}

/-- `to_finset l` removes duplicates from the list `l` to produce a finset. -/
def to_finset (l : list α) : finset α := multiset.to_finset l

@[simp] theorem to_finset_val (l : list α) : l.to_finset.1 = (l.dedup : multiset α) := rfl
@[simp] theorem to_finset_coe (l : list α) : (l : multiset α).to_finset = l.to_finset := rfl

lemma to_finset_eq (n : nodup l) : @finset.mk α l n = l.to_finset := multiset.to_finset_eq n

@[simp] lemma mem_to_finset : a ∈ l.to_finset ↔ a ∈ l := mem_dedup
@[simp, norm_cast] lemma coe_to_finset (l : list α) : (l.to_finset : set α) = {a | a ∈ l} :=
set.ext $ λ _, list.mem_to_finset

@[simp] lemma to_finset_nil : to_finset (@nil α) = ∅ := rfl

@[simp] lemma to_finset_cons : to_finset (a :: l) = insert a (to_finset l) :=
finset.eq_of_veq $ by by_cases h : a ∈ l; simp [finset.insert_val', multiset.dedup_cons, h]

lemma to_finset_surj_on : set.surj_on to_finset {l : list α | l.nodup} set.univ :=
by { rintro ⟨⟨l⟩, hl⟩ _, exact ⟨l, hl, (to_finset_eq hl).symm⟩ }

theorem to_finset_surjective : surjective (to_finset : list α → finset α) :=
λ s, let ⟨l, _, hls⟩ := to_finset_surj_on (set.mem_univ s) in ⟨l, hls⟩

lemma to_finset_eq_iff_perm_dedup : l.to_finset = l'.to_finset ↔ l.dedup ~ l'.dedup :=
by simp [finset.ext_iff, perm_ext (nodup_dedup _) (nodup_dedup _)]

lemma to_finset.ext_iff {a b : list α} : a.to_finset = b.to_finset ↔ ∀ x, x ∈ a ↔ x ∈ b :=
by simp only [finset.ext_iff, mem_to_finset]

lemma to_finset.ext : (∀ x, x ∈ l ↔ x ∈ l') → l.to_finset = l'.to_finset := to_finset.ext_iff.mpr

lemma to_finset_eq_of_perm (l l' : list α) (h : l ~ l') : l.to_finset = l'.to_finset :=
to_finset_eq_iff_perm_dedup.mpr h.dedup

lemma perm_of_nodup_nodup_to_finset_eq (hl : nodup l) (hl' : nodup l')
 (h : l.to_finset = l'.to_finset) : l ~ l' :=
by { rw ←multiset.coe_eq_coe, exact multiset.nodup.to_finset_inj hl hl' h }

@[simp] lemma to_finset_append : to_finset (l ++ l') = l.to_finset ∪ l'.to_finset :=
begin
 induction l with hd tl hl,
 { simp },
 { simp [hl] }
end

@[simp] lemma to_finset_reverse {l : list α} : to_finset l.reverse = l.to_finset :=
to_finset_eq_of_perm _ _ (reverse_perm l)

lemma to_finset_replicate_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (list.replicate n a).to_finset = {a} :=
by { ext x, simp [hn, list.mem_replicate] }

@[simp] lemma to_finset_union (l l' : list α) : (l ∪ l').to_finset = l.to_finset ∪ l'.to_finset :=
by { ext, simp }

@[simp] lemma to_finset_inter (l l' : list α) : (l ∩ l').to_finset = l.to_finset ∩ l'.to_finset :=
by { ext, simp }

@[simp] lemma to_finset_eq_empty_iff (l : list α) : l.to_finset = ∅ ↔ l = nil := by cases l; simp

@[simp] lemma to_finset_nonempty_iff (l : list α) : l.to_finset.nonempty ↔ l ≠ [] :=
by simp [finset.nonempty_iff_ne_empty]

end list

namespace finset

section to_list

/-- Produce a list of the elements in the finite set using choice. -/
noncomputable def to_list (s : finset α) : list α := s.1.to_list

lemma nodup_to_list (s : finset α) : s.to_list.nodup :=
by { rw [to_list]; rw [ ←multiset.coe_nodup]; rw [ multiset.coe_to_list], exact s.nodup }

@[simp] lemma mem_to_list {a : α} {s : finset α} : a ∈ s.to_list ↔ a ∈ s := mem_to_list

@[simp] lemma to_list_eq_nil {s : finset α} : s.to_list = [] ↔ s = ∅ :=
to_list_eq_nil.trans val_eq_zero

@[simp] lemma empty_to_list {s : finset α} : s.to_list.empty ↔ s = ∅ :=
list.empty_iff_eq_nil.trans to_list_eq_nil

@[simp] lemma to_list_empty : (∅ : finset α).to_list = [] := to_list_eq_nil.mpr rfl

lemma nonempty.to_list_ne_nil {s : finset α} (hs : s.nonempty) : s.to_list ≠ [] :=
mt to_list_eq_nil.mp hs.ne_empty

lemma nonempty.not_empty_to_list {s : finset α} (hs : s.nonempty) : ¬s.to_list.empty :=
mt empty_to_list.mp hs.ne_empty

@[simp, norm_cast]
lemma coe_to_list (s : finset α) : (s.to_list : multiset α) = s.val := s.val.coe_to_list

@[simp] lemma to_list_to_finset [decidable_eq α] (s : finset α) : s.to_list.to_finset = s :=
by { ext, simp }

@[simp] lemma to_list_eq_singleton_iff {a : α} {s : finset α} : s.to_list = [a] ↔ s = {a} :=
by rw [to_list]; rw [ to_list_eq_singleton_iff]; rw [ val_eq_singleton_iff]

@[simp] lemma to_list_singleton : ∀ a, ({a} : finset α).to_list = [a] := to_list_singleton

lemma exists_list_nodup_eq [decidable_eq α] (s : finset α) :
 ∃ (l : list α), l.nodup ∧ l.to_finset = s :=
⟨s.to_list, s.nodup_to_list, s.to_list_to_finset⟩

lemma to_list_cons {a : α} {s : finset α} (h : a ∉ s) : (cons a s h).to_list ~ a :: s.to_list :=
(list.perm_ext (nodup_to_list _) (by simp [h, nodup_to_list s])).2 $
 λ x, by simp only [list.mem_cons_iff, finset.mem_to_list, finset.mem_cons]

lemma to_list_insert [decidable_eq α] {a : α} {s : finset α} (h : a ∉ s) :
 (insert a s).to_list ~ a :: s.to_list :=
cons_eq_insert _ _ h ▸ to_list_cons _

end to_list

/-!
### disj_Union

This section is about the bounded union of a disjoint indexed family `t : α → finset β` of finite
sets over a finite set `s : finset α`. In most cases `finset.bUnion` should be preferred.
-/
section disj_Union

variables {s s₁ s₂ : finset α} {t t₁ t₂ : α → finset β}

/-- `disj_Union s f h` is the set such that `a ∈ disj_Union s f` iff `a ∈ f i` for some `i ∈ s`.
It is the same as `s.bUnion f`, but it does not require decidable equality on the type. The
hypothesis ensures that the sets are disjoint. -/
def disj_Union (s : finset α) (t : α → finset β)
 (hf : (s : set α).pairwise_disjoint t) : finset β :=
⟨(s.val.bind (finset.val ∘ t)), multiset.nodup_bind.mpr
 ⟨λ a ha, (t a).nodup, s.nodup.pairwise $ λ a ha b hb hab, disjoint_val.2 $ hf ha hb hab⟩⟩

@[simp] theorem disj_Union_val (s : finset α) (t : α → finset β) (h) :
 (s.disj_Union t h).1 = (s.1.bind (λ a, (t a).1)) := rfl

@[simp] theorem disj_Union_empty (t : α → finset β) : disj_Union ∅ t (by simp) = ∅ := rfl

@[simp] lemma mem_disj_Union {b : β} {h} :
 b ∈ s.disj_Union t h ↔ ∃ a ∈ s, b ∈ t a :=
by simp only [mem_def, disj_Union_val, mem_bind, exists_prop]

@[simp, norm_cast] lemma coe_disj_Union {h} : (s.disj_Union t h : set β) = ⋃ x ∈ (s : set α), t x :=
by simp only [set.ext_iff, mem_disj_Union, set.mem_Union, iff_self, mem_coe, implies_true_iff]

@[simp] theorem disj_Union_cons (a : α) (s : finset α) (ha : a ∉ s) (f : α → finset β) (H) :
 disj_Union (cons a s ha) f H = (f a).disj_union
 (s.disj_Union f $
 λ b hb c hc, H (mem_cons_of_mem hb) (mem_cons_of_mem hc))
 (disjoint_left.mpr $ λ b hb h, let ⟨c, hc, h⟩ := mem_disj_Union.mp h in
 disjoint_left.mp
 (H (mem_cons_self a s) (mem_cons_of_mem hc) (ne_of_mem_of_not_mem hc ha).symm) hb h)
 :=
eq_of_veq $ multiset.cons_bind _ _ _

@[simp] lemma singleton_disj_Union (a : α) {h} : finset.disj_Union {a} t h = t a :=
eq_of_veq $ multiset.singleton_bind _ _


lemma disj_Union_disj_Union (s : finset α) (f : α → finset β) (g : β → finset γ) (h1 h2) :
 (s.disj_Union f h1).disj_Union g h2 =
 s.attach.disj_Union (λ a, (f a).disj_Union g $
 λ b hb c hc, h2 (mem_disj_Union.mpr ⟨_, a.prop, hb⟩) (mem_disj_Union.mpr ⟨_, a.prop, hc⟩))
 (λ a ha b hb hab, disjoint_left.mpr $ λ x hxa hxb, begin
 obtain ⟨xa, hfa, hga⟩ := mem_disj_Union.mp hxa,
 obtain ⟨xb, hfb, hgb⟩ := mem_disj_Union.mp hxb,
 refine disjoint_left.mp (h2
 (mem_disj_Union.mpr ⟨_, a.prop, hfa⟩) (mem_disj_Union.mpr ⟨_, b.prop, hfb⟩) _) hga hgb,
 rintro rfl,
 exact disjoint_left.mp (h1 a.prop b.prop $ subtype.coe_injective.ne hab) hfa hfb,
 end) :=
eq_of_veq $ multiset.bind_assoc.trans (multiset.attach_bind_coe _ _).symm

lemma disj_Union_filter_eq_of_maps_to [decidable_eq β] {s : finset α} {t : finset β} {f : α → β}
 (h : ∀ x ∈ s, f x ∈ t) :
 t.disj_Union (λ a, s.filter $ (λ c, f c = a))
 (λ x' hx y' hy hne, disjoint_filter_filter' _ _ begin
 simp_rw [pi.disjoint_iff, Prop.disjoint_iff],
 rintros i ⟨rfl, rfl⟩,
 exact hne rfl,
 end) = s :=
ext $ λ b, by simpa using h b

end disj_Union

section bUnion
/-!
### bUnion

This section is about the bounded union of an indexed family `t : α → finset β` of finite sets
over a finite set `s : finset α`.
-/

variables [decidable_eq β] {s s₁ s₂ : finset α} {t t₁ t₂ : α → finset β}

/-- `bUnion s t` is the union of `t x` over `x ∈ s`.
(This was formerly `bind` due to the monad structure on types with `decidable_eq`.) -/
protected def bUnion (s : finset α) (t : α → finset β) : finset β :=
(s.1.bind (λ a, (t a).1)).to_finset

@[simp] theorem bUnion_val (s : finset α) (t : α → finset β) :
 (s.bUnion t).1 = (s.1.bind (λ a, (t a).1)).dedup := rfl

@[simp] theorem bUnion_empty : finset.bUnion ∅ t = ∅ := rfl

@[simp] lemma mem_bUnion {b : β} : b ∈ s.bUnion t ↔ ∃ a ∈ s, b ∈ t a :=
by simp only [mem_def, bUnion_val, mem_dedup, mem_bind, exists_prop]

@[simp, norm_cast] lemma coe_bUnion : (s.bUnion t : set β) = ⋃ x ∈ (s : set α), t x :=
by simp only [set.ext_iff, mem_bUnion, set.mem_Union, iff_self, mem_coe, implies_true_iff]

@[simp] theorem bUnion_insert [decidable_eq α] {a : α} : (insert a s).bUnion t = t a ∪ s.bUnion t :=
ext $ λ x, by simp only [mem_bUnion, exists_prop, mem_union, mem_insert,
 or_and_distrib_right, exists_or_distrib, exists_eq_left]
-- ext $ λ x, by simp [or_and_distrib_right, exists_or_distrib]

lemma bUnion_congr (hs : s₁ = s₂) (ht : ∀ a ∈ s₁, t₁ a = t₂ a) : s₁.bUnion t₁ = s₂.bUnion t₂ :=
ext $ λ x, by simp [hs, ht] { contextual := tt }

@[simp] lemma disj_Union_eq_bUnion (s : finset α) (f : α → finset β) (hf) :
 s.disj_Union f hf = s.bUnion f :=
begin
 dsimp [disj_Union, finset.bUnion, function.comp],
 generalize_proofs h,
 exact eq_of_veq h.dedup.symm,
end

theorem bUnion_subset {s' : finset β} : s.bUnion t ⊆ s' ↔ ∀ x ∈ s, t x ⊆ s' :=
by simp only [subset_iff, mem_bUnion]; exact
⟨λ H a ha b hb, H ⟨a, ha, hb⟩, λ H b ⟨a, ha, hb⟩, H a ha hb⟩

@[simp] lemma singleton_bUnion {a : α} : finset.bUnion {a} t = t a :=
by { classical, rw [← insert_emptyc_eq]; rw [ bUnion_insert]; rw [ bUnion_empty]; rw [ union_empty] }

theorem bUnion_inter (s : finset α) (f : α → finset β) (t : finset β) :
 s.bUnion f ∩ t = s.bUnion (λ x, f x ∩ t) :=
begin
 ext x,
 simp only [mem_bUnion, mem_inter],
 tauto
end

theorem inter_bUnion (t : finset β) (s : finset α) (f : α → finset β) :
 t ∩ s.bUnion f = s.bUnion (λ x, t ∩ f x) :=
by rw [inter_comm]; rw [ bUnion_inter]; simp [inter_comm]

lemma bUnion_bUnion [decidable_eq γ] (s : finset α) (f : α → finset β) (g : β → finset γ) :
 (s.bUnion f).bUnion g = s.bUnion (λ a, (f a).bUnion g) :=
begin
 ext,
 simp only [finset.mem_bUnion, exists_prop],
 simp_rw [←exists_and_distrib_right, ←exists_and_distrib_left, and_assoc],
 rw exists_comm,
end

theorem bind_to_finset [decidable_eq α] (s : multiset α) (t : α → multiset β) :
 (s.bind t).to_finset = s.to_finset.bUnion (λa, (t a).to_finset) :=
ext $ λ x, by simp only [multiset.mem_to_finset, mem_bUnion, multiset.mem_bind, exists_prop]

lemma bUnion_mono (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) : s.bUnion t₁ ⊆ s.bUnion t₂ :=
have ∀ b a, a ∈ s → b ∈ t₁ a → (∃ (a : α), a ∈ s ∧ b ∈ t₂ a),
 from assume b a ha hb, ⟨a, ha, finset.mem_of_subset (h a ha) hb⟩,
by simpa only [subset_iff, mem_bUnion, exists_imp_distrib, and_imp, exists_prop]

lemma bUnion_subset_bUnion_of_subset_left (t : α → finset β) (h : s₁ ⊆ s₂) :
 s₁.bUnion t ⊆ s₂.bUnion t :=
begin
 intro x,
 simp only [and_imp, mem_bUnion, exists_prop],
 exact Exists.imp (λ a ha, ⟨h ha.1, ha.2⟩)
end

lemma subset_bUnion_of_mem (u : α → finset β) {x : α} (xs : x ∈ s) : u x ⊆ s.bUnion u :=
singleton_bUnion.superset.trans $ bUnion_subset_bUnion_of_subset_left u $ singleton_subset_iff.2 xs

@[simp] lemma bUnion_subset_iff_forall_subset {α β : Type*} [decidable_eq β]
 {s : finset α} {t : finset β} {f : α → finset β} : s.bUnion f ⊆ t ↔ ∀ x ∈ s, f x ⊆ t :=
⟨λ h x hx, (subset_bUnion_of_mem f hx).trans h,
 λ h x hx, let ⟨a, ha₁, ha₂⟩ := mem_bUnion.mp hx in h _ ha₁ ha₂⟩

@[simp] lemma bUnion_singleton_eq_self [decidable_eq α] : s.bUnion (singleton : α → finset α) = s :=
ext $ λ x, by simp only [mem_bUnion, mem_singleton, exists_prop, exists_eq_right']

lemma filter_bUnion (s : finset α) (f : α → finset β) (p : β → Prop) [decidable_pred p] :
 (s.bUnion f).filter p = s.bUnion (λ a, (f a).filter p) :=
begin
 ext b,
 simp only [mem_bUnion, exists_prop, mem_filter],
 split,
 { rintro ⟨⟨a, ha, hba⟩, hb⟩,
 exact ⟨a, ha, hba, hb⟩ },
 { rintro ⟨a, ha, hba, hb⟩,
 exact ⟨⟨a, ha, hba⟩, hb⟩ }
end

lemma bUnion_filter_eq_of_maps_to [decidable_eq α] {s : finset α} {t : finset β} {f : α → β}
 (h : ∀ x ∈ s, f x ∈ t) :
 t.bUnion (λ a, s.filter $ (λ c, f c = a)) = s :=
by simpa only [disj_Union_eq_bUnion] using disj_Union_filter_eq_of_maps_to h

lemma erase_bUnion (f : α → finset β) (s : finset α) (b : β) :
 (s.bUnion f).erase b = s.bUnion (λ x, (f x).erase b) :=
by { ext, simp only [finset.mem_bUnion, iff_self, exists_and_distrib_left, finset.mem_erase] }

@[simp] lemma bUnion_nonempty : (s.bUnion t).nonempty ↔ ∃ x ∈ s, (t x).nonempty :=
by simp [finset.nonempty, ← exists_and_distrib_left, @exists_swap α]

lemma nonempty.bUnion (hs : s.nonempty) (ht : ∀ x ∈ s, (t x).nonempty) : (s.bUnion t).nonempty :=
bUnion_nonempty.2 $ hs.imp $ λ x hx, ⟨hx, ht x hx⟩

lemma disjoint_bUnion_left (s : finset α) (f : α → finset β) (t : finset β) :
 disjoint (s.bUnion f) t ↔ (∀ i ∈ s, disjoint (f i) t) :=
begin
 classical,
 refine s.induction _ _,
 { simp only [forall_mem_empty_iff, bUnion_empty, disjoint_empty_left] },
 { assume i s his ih,
 simp only [disjoint_union_left, bUnion_insert, his, forall_mem_insert, ih] }
end

lemma disjoint_bUnion_right (s : finset β) (t : finset α) (f : α → finset β) :
 disjoint s (t.bUnion f) ↔ ∀ i ∈ t, disjoint s (f i) :=
by simpa only [disjoint.comm] using disjoint_bUnion_left t f s

end bUnion

/-! ### choose -/
section choose
variables (p : α → Prop) [decidable_pred p] (l : finset α)

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x (hp : (∃! a, a ∈ l ∧ p a)) : { a // a ∈ l ∧ p a } :=
multiset.choose_x p l.val hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α := choose_x p l hp

lemma choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
(choose_x p l hp).property

lemma choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l := (choose_spec _ _ _).1

lemma choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) := (choose_spec _ _ _).2

end choose

section pairwise
variables {s : finset α}

lemma pairwise_subtype_iff_pairwise_finset' (r : β → β → Prop) (f : α → β) :
 pairwise (r on λ x : s, f x) ↔ (s : set α).pairwise (r on f) :=
pairwise_subtype_iff_pairwise_set (s : set α) (r on f)

lemma pairwise_subtype_iff_pairwise_finset (r : α → α → Prop) :
 pairwise (r on λ x : s, x) ↔ (s : set α).pairwise r :=
pairwise_subtype_iff_pairwise_finset' r id

lemma pairwise_cons' {a : α} (ha : a ∉ s) (r : β → β → Prop) (f : α → β) :
 pairwise (r on λ a : s.cons a ha, f a) ↔
 pairwise (r on λ a : s, f a) ∧ ∀ b ∈ s, r (f a) (f b) ∧ r (f b) (f a) :=
begin
 simp only [pairwise_subtype_iff_pairwise_finset', finset.coe_cons, set.pairwise_insert,
 finset.mem_coe, and.congr_right_iff],
 exact λ hsr, ⟨λ h b hb, h b hb $ by { rintro rfl, contradiction }, λ h b hb _, h b hb⟩,
end

lemma pairwise_cons {a : α} (ha : a ∉ s) (r : α → α → Prop) :
 pairwise (r on λ a : s.cons a ha, a) ↔ pairwise (r on λ a : s, a) ∧ ∀ b ∈ s, r a b ∧ r b a :=
pairwise_cons' ha r id

end pairwise
end finset

namespace equiv

/--
Inhabited types are equivalent to `option β` for some `β` by identifying `default α` with `none`.
-/
def sigma_equiv_option_of_inhabited (α : Type u) [inhabited α] [decidable_eq α] :
 Σ (β : Type u), α ≃ option β :=
⟨{x : α // x ≠ default},
{ to_fun := λ (x : α), if h : x = default then none else some ⟨x, h⟩,
 inv_fun := option.elim default coe,
 left_inv := λ x, by { dsimp only, split_ifs; simp [*] },
 right_inv := begin
 rintro (_|⟨x,h⟩),
 { simp },
 { dsimp only,
 split_ifs with hi,
 { simpa [h] using hi },
 { simp } }
 end }⟩

end equiv

namespace multiset
variable [decidable_eq α]

lemma disjoint_to_finset {m1 m2 : multiset α} :
 _root_.disjoint m1.to_finset m2.to_finset ↔ m1.disjoint m2 :=
begin
 rw finset.disjoint_iff_ne,
 refine ⟨λ h a ha1 ha2, _, _⟩,
 { rw ← multiset.mem_to_finset at ha1 ha2,
 exact h _ ha1 _ ha2 rfl },
 { rintros h a ha b hb rfl,
 rw multiset.mem_to_finset at ha hb,
 exact h ha hb }
end

end multiset

namespace list
variables [decidable_eq α] {l l' : list α}

lemma disjoint_to_finset_iff_disjoint : _root_.disjoint l.to_finset l'.to_finset ↔ l.disjoint l' :=
multiset.disjoint_to_finset

end list

-- Assert that we define `finset` without the material on `list.sublists`.
-- Note that we cannot use `list.sublists` itself as that is defined very early.
assert_not_exists list.sublists_len
assert_not_exists multiset.powerset

