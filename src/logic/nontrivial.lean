/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.prod.basic
import data.subtype
import logic.function.basic
import logic.unique

/-!
# Nontrivial types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A type is *nontrivial* if it contains at least two elements. This is useful in particular for rings
(where it is equivalent to the fact that zero is different from one) and for vector spaces
(where it is equivalent to the fact that the dimension is positive).

We introduce a typeclass `nontrivial` formalizing this property.
-/

variables {α : Type*} {β : Type*}

open_locale classical

/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
class nontrivial (α : Type*) : Prop :=
(exists_pair_ne : ∃ (x y : α), x ≠ y)

lemma nontrivial_iff : nontrivial α ↔ ∃ (x y : α), x ≠ y :=
⟨λ h, h.exists_pair_ne, λ h, ⟨h⟩⟩

lemma exists_pair_ne (α : Type*) [nontrivial α] : ∃ (x y : α), x ≠ y :=
nontrivial.exists_pair_ne

-- See Note [decidable namespace]
protected lemma decidable.exists_ne [nontrivial α] [decidable_eq α] (x : α) : ∃ y, y ≠ x :=
begin
  rcases exists_pair_ne α with ⟨y, y', h⟩,
  by_cases hx : x = y,
  { rw ← hx at h,
    exact ⟨y', h.symm⟩ },
  { exact ⟨y, ne.symm hx⟩ }
end

lemma exists_ne [nontrivial α] (x : α) : ∃ y, y ≠ x :=
by classical; exact decidable.exists_ne x

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
lemma nontrivial_of_ne (x y : α) (h : x ≠ y) : nontrivial α :=
⟨⟨x, y, h⟩⟩

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
lemma nontrivial_of_lt [preorder α] (x y : α) (h : x < y) : nontrivial α :=
⟨⟨x, y, ne_of_lt h⟩⟩

lemma exists_pair_lt (α : Type*) [nontrivial α] [linear_order α] : ∃ (x y : α), x < y :=
begin
  rcases exists_pair_ne α with ⟨x, y, hxy⟩,
  cases lt_or_gt_of_ne hxy;
  exact ⟨_, _, h⟩
end

lemma nontrivial_iff_lt [linear_order α] : nontrivial α ↔ ∃ (x y : α), x < y :=
⟨λ h, @exists_pair_lt α h _, λ ⟨x, y, h⟩, nontrivial_of_lt x y h⟩

lemma nontrivial_iff_exists_ne (x : α) : nontrivial α ↔ ∃ y, y ≠ x :=
⟨λ h, @exists_ne α h x, λ ⟨y, hy⟩, nontrivial_of_ne _ _ hy⟩

lemma subtype.nontrivial_iff_exists_ne (p : α → Prop) (x : subtype p) :
  nontrivial (subtype p) ↔ ∃ (y : α) (hy : p y), y ≠ x :=
by simp only [nontrivial_iff_exists_ne x, subtype.exists, ne.def, subtype.ext_iff, subtype.coe_mk]

instance : nontrivial Prop := ⟨⟨true, false, true_ne_false⟩⟩

/--
See Note [lower instance priority]

Note that since this and `nonempty_of_inhabited` are the most "obvious" way to find a nonempty
instance if no direct instance can be found, we give this a higher priority than the usual `100`.
-/
@[priority 500]
instance nontrivial.to_nonempty [nontrivial α] : nonempty α :=
let ⟨x, _⟩ := exists_pair_ne α in ⟨x⟩

attribute [instance, priority 500] nonempty_of_inhabited

/-- An inhabited type is either nontrivial, or has a unique element. -/
noncomputable def nontrivial_psum_unique (α : Type*) [inhabited α] :
  psum (nontrivial α) (unique α) :=
if h : nontrivial α then psum.inl h else psum.inr
{ default := default,
  uniq := λ (x : α),
  begin
    change x = default,
    contrapose! h,
    use [x, default]
  end }

lemma subsingleton_iff : subsingleton α ↔ ∀ (x y : α), x = y :=
⟨by { introsI h, exact subsingleton.elim }, λ h, ⟨h⟩⟩

lemma not_nontrivial_iff_subsingleton : ¬(nontrivial α) ↔ subsingleton α :=
by { rw [nontrivial_iff, subsingleton_iff], push_neg, refl }

lemma not_nontrivial (α) [subsingleton α] : ¬nontrivial α :=
λ ⟨⟨x, y, h⟩⟩, h $ subsingleton.elim x y

lemma not_subsingleton (α) [h : nontrivial α] : ¬subsingleton α :=
let ⟨⟨x, y, hxy⟩⟩ := h in λ ⟨h'⟩, hxy $ h' x y

/-- A type is either a subsingleton or nontrivial. -/
lemma subsingleton_or_nontrivial (α : Type*) : subsingleton α ∨ nontrivial α :=
by { rw [← not_nontrivial_iff_subsingleton, or_comm], exact classical.em _ }

lemma false_of_nontrivial_of_subsingleton (α : Type*) [nontrivial α] [subsingleton α] : false :=
let ⟨x, y, h⟩ := exists_pair_ne α in h $ subsingleton.elim x y

instance option.nontrivial [nonempty α] : nontrivial (option α) :=
by { inhabit α, use [none, some default] }

/-- Pushforward a `nontrivial` instance along an injective function. -/
protected lemma function.injective.nontrivial [nontrivial α]
  {f : α → β} (hf : function.injective f) : nontrivial β :=
let ⟨x, y, h⟩ := exists_pair_ne α in ⟨⟨f x, f y, hf.ne h⟩⟩

/-- Pullback a `nontrivial` instance along a surjective function. -/
protected lemma function.surjective.nontrivial [nontrivial β]
  {f : α → β} (hf : function.surjective f) : nontrivial α :=
begin
  rcases exists_pair_ne β with ⟨x, y, h⟩,
  rcases hf x with ⟨x', hx'⟩,
  rcases hf y with ⟨y', hy'⟩,
  have : x' ≠ y', by { contrapose! h, rw [← hx', ← hy', h] },
  exact ⟨⟨x', y', this⟩⟩
end

/-- An injective function from a nontrivial type has an argument at
which it does not take a given value. -/
protected lemma function.injective.exists_ne [nontrivial α] {f : α → β}
  (hf : function.injective f) (y : β) : ∃ x, f x ≠ y :=
begin
  rcases exists_pair_ne α with ⟨x₁, x₂, hx⟩,
  by_cases h : f x₂ = y,
  { exact ⟨x₁, (hf.ne_iff' h).2 hx⟩ },
  { exact ⟨x₂, h⟩ }
end

instance nontrivial_prod_right [nonempty α] [nontrivial β] : nontrivial (α × β) :=
prod.snd_surjective.nontrivial

instance nontrivial_prod_left [nontrivial α] [nonempty β] : nontrivial (α × β) :=
prod.fst_surjective.nontrivial

namespace pi

variables {I : Type*} {f : I → Type*}

/-- A pi type is nontrivial if it's nonempty everywhere and nontrivial somewhere. -/
lemma nontrivial_at (i' : I) [inst : Π i, nonempty (f i)] [nontrivial (f i')] :
  nontrivial (Π i : I, f i) :=
by classical; exact
(function.update_injective (λ i, classical.choice (inst i)) i').nontrivial

/--
As a convenience, provide an instance automatically if `(f default)` is nontrivial.

If a different index has the non-trivial type, then use `haveI := nontrivial_at that_index`.
-/
instance nontrivial [inhabited I] [inst : Π i, nonempty (f i)] [nontrivial (f default)] :
  nontrivial (Π i : I, f i) := nontrivial_at default

end pi

instance function.nontrivial [h : nonempty α] [nontrivial β] : nontrivial (α → β) :=
h.elim $ λ a, pi.nontrivial_at a

@[nontriviality]
protected lemma subsingleton.le [preorder α] [subsingleton α] (x y : α) : x ≤ y :=
le_of_eq (subsingleton.elim x y)

namespace bool

instance : nontrivial bool := ⟨⟨tt,ff, tt_eq_ff_eq_false⟩⟩

end bool
