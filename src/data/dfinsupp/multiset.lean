/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.dfinsupp.order

/-!
# Equivalence between `multiset` and `ℕ`-valued finitely supported functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `dfinsupp.to_multiset` the equivalence between `Π₀ a : α, ℕ` and `multiset α`, along
with `multiset.to_dfinsupp` the reverse equivalence.

Note that this provides a computable alternative to `finsupp.to_multiset`.
-/

open function

variables {α : Type*} {β : α → Type*}

namespace dfinsupp

/-- Non-dependent special case of `dfinsupp.add_zero_class` to help typeclass search. -/
instance add_zero_class' {β} [add_zero_class β] : add_zero_class (Π₀ a : α, β) :=
@dfinsupp.add_zero_class α (λ _, β) _

variables [decidable_eq α]

/-- A computable version of `finsupp.to_multiset`. -/
def to_multiset : (Π₀ a : α, ℕ) →+ multiset α :=
dfinsupp.sum_add_hom (λ a : α, multiset.replicate_add_monoid_hom a)

@[simp] lemma to_multiset_single (a : α) (n : ℕ) :
  to_multiset (dfinsupp.single a n) = multiset.replicate n a :=
dfinsupp.sum_add_hom_single _ _ _

end dfinsupp

namespace multiset
variables [decidable_eq α] {s t : multiset α}

/-- A computable version of `multiset.to_finsupp` -/
def to_dfinsupp : multiset α →+ Π₀ a : α, ℕ :=
{ to_fun := λ s,
  { to_fun := λ n, s.count n,
    support' := trunc.mk ⟨s, λ i, (em (i ∈ s)).imp_right multiset.count_eq_zero_of_not_mem⟩ },
  map_zero' := rfl,
  map_add' := λ s t, dfinsupp.ext $ λ _, multiset.count_add _ _ _ }

@[simp] lemma to_dfinsupp_apply (s : multiset α) (a : α) :
  s.to_dfinsupp a = s.count a := rfl

@[simp] lemma to_dfinsupp_support (s : multiset α) : s.to_dfinsupp.support = s.to_finset :=
finset.filter_true_of_mem $ λ x hx, count_ne_zero.mpr $ multiset.mem_to_finset.1 hx

@[simp] lemma to_dfinsupp_replicate (a : α) (n : ℕ) :
  to_dfinsupp (multiset.replicate n a) = dfinsupp.single a n :=
begin
  ext i,
  dsimp [to_dfinsupp],
  simp [count_replicate, eq_comm],
end

@[simp] lemma to_dfinsupp_singleton (a : α) : to_dfinsupp {a} = dfinsupp.single a 1 :=
by rw [←replicate_one, to_dfinsupp_replicate]

/-- `multiset.to_dfinsupp` as an `add_equiv`. -/
@[simps apply symm_apply]
def equiv_dfinsupp : multiset α ≃+ Π₀ a : α, ℕ :=
add_monoid_hom.to_add_equiv
  multiset.to_dfinsupp
  dfinsupp.to_multiset
  (by { ext x : 1, simp })
  (by { refine @dfinsupp.add_hom_ext α (λ _, ℕ) _ _ _ _ _ _ (λ i hi, _), simp, })

@[simp] lemma to_dfinsupp_to_multiset (s : multiset α) : s.to_dfinsupp.to_multiset = s :=
equiv_dfinsupp.symm_apply_apply s

lemma to_dfinsupp_injective : injective (to_dfinsupp : multiset α → Π₀ a, ℕ) :=
equiv_dfinsupp.injective

@[simp] lemma to_dfinsupp_inj : to_dfinsupp s = to_dfinsupp t ↔ s = t :=
to_dfinsupp_injective.eq_iff

@[simp] lemma to_dfinsupp_le_to_dfinsupp : to_dfinsupp s ≤ to_dfinsupp t ↔ s ≤ t :=
by simp [multiset.le_iff_count, dfinsupp.le_def]

@[simp] lemma to_dfinsupp_lt_to_dfinsupp : to_dfinsupp s < to_dfinsupp t ↔ s < t :=
lt_iff_lt_of_le_iff_le' to_dfinsupp_le_to_dfinsupp to_dfinsupp_le_to_dfinsupp

@[simp] lemma to_dfinsupp_inter (s t : multiset α) :
  to_dfinsupp (s ∩ t) = s.to_dfinsupp ⊓ t.to_dfinsupp :=
by { ext i, simp [inf_eq_min] }

@[simp] lemma to_dfinsupp_union (s t : multiset α) :
  to_dfinsupp (s ∪ t) = s.to_dfinsupp ⊔ t.to_dfinsupp :=
by { ext i, simp [sup_eq_max] }

end multiset

namespace dfinsupp
variables [decidable_eq α] {f g : Π₀ a : α, ℕ}

@[simp] lemma to_multiset_to_dfinsupp : f.to_multiset.to_dfinsupp = f :=
multiset.equiv_dfinsupp.apply_symm_apply f

lemma to_multiset_injective : injective (to_multiset : (Π₀ a, ℕ) → multiset α) :=
multiset.equiv_dfinsupp.symm.injective

@[simp] lemma to_multiset_inj : to_multiset f = to_multiset g ↔ f = g :=
to_multiset_injective.eq_iff

@[simp] lemma to_multiset_le_to_multiset : to_multiset f ≤ to_multiset g ↔ f ≤ g :=
by simp_rw [←multiset.to_dfinsupp_le_to_dfinsupp, to_multiset_to_dfinsupp]

@[simp] lemma to_multiset_lt_to_multiset : to_multiset f < to_multiset g ↔ f < g :=
by simp_rw [←multiset.to_dfinsupp_lt_to_dfinsupp, to_multiset_to_dfinsupp]

variables (f g)

@[simp] lemma to_multiset_inf : to_multiset (f ⊓ g) = f.to_multiset ∩ g.to_multiset :=
multiset.to_dfinsupp_injective $ by simp

@[simp] lemma to_multiset_sup : to_multiset (f ⊔ g) = f.to_multiset ∪ g.to_multiset :=
multiset.to_dfinsupp_injective $ by simp

end dfinsupp
