/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.integral.bochner
import measure_theory.constructions.prod.basic

/-!
# Markov Kernels

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A kernel from a measurable space `α` to another measurable space `β` is a measurable map
`α → measure β`, where the measurable space instance on `measure β` is the one defined in
`measure_theory.measure.measurable_space`. That is, a kernel `κ` verifies that for all measurable
sets `s` of `β`, `a ↦ κ a s` is measurable.

## Main definitions

Classes of kernels:
* `probability_theory.kernel α β`: kernels from `α` to `β`, defined as the `add_submonoid` of the
 measurable functions in `α → measure β`.
* `probability_theory.is_markov_kernel κ`: a kernel from `α` to `β` is said to be a Markov kernel
 if for all `a : α`, `k a` is a probability measure.
* `probability_theory.is_finite_kernel κ`: a kernel from `α` to `β` is said to be finite if there
 exists `C : ℝ≥0∞` such that `C < ∞` and for all `a : α`, `κ a univ ≤ C`. This implies in
 particular that all measures in the image of `κ` are finite, but is stronger since it requires an
 uniform bound. This stronger condition is necessary to ensure that the composition of two finite
 kernels is finite.
* `probability_theory.is_s_finite_kernel κ`: a kernel is called s-finite if it is a countable
 sum of finite kernels.

Particular kernels:
* `probability_theory.kernel.deterministic (f : α → β) (hf : measurable f)`:
 kernel `a ↦ measure.dirac (f a)`.
* `probability_theory.kernel.const α (μβ : measure β)`: constant kernel `a ↦ μβ`.
* `probability_theory.kernel.restrict κ (hs : measurable_set s)`: kernel for which the image of
 `a : α` is `(κ a).restrict s`.
 Integral: `∫⁻ b, f b ∂(kernel.restrict κ hs a) = ∫⁻ b in s, f b ∂(κ a)`

## Main statements

* `probability_theory.kernel.ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable
 functions `f` and all `a`, then the two kernels `κ` and `η` are equal.

-/

open measure_theory

open_locale measure_theory ennreal nnreal big_operators

namespace probability_theory

/-- A kernel from a measurable space `α` to another measurable space `β` is a measurable function
`κ : α → measure β`. The measurable space structure on `measure β` is given by
`measure_theory.measure.measurable_space`. A map `κ : α → measure β` is measurable iff
`∀ s : set β, measurable_set s → measurable (λ a, κ a s)`. -/
def kernel (α β : Type*) [measurable_space α] [measurable_space β] :
 add_submonoid (α → measure β) :=
{ carrier := measurable,
 zero_mem' := measurable_zero,
 add_mem' := λ f g hf hg, measurable.add hf hg, }

instance {α β : Type*} [measurable_space α] [measurable_space β] :
 has_coe_to_fun (kernel α β) (λ _, α → measure β) := ⟨λ κ, κ.val⟩

variables {α β ι : Type*} {mα : measurable_space α} {mβ : measurable_space β}

include mα mβ

namespace kernel

@[simp] lemma coe_fn_zero : ⇑(0 : kernel α β) = 0 := rfl
@[simp] lemma coe_fn_add (κ η : kernel α β) : ⇑(κ + η) = κ + η := rfl

omit mα mβ

/-- Coercion to a function as an additive monoid homomorphism. -/
def coe_add_hom (α β : Type*) [measurable_space α] [measurable_space β] :
 kernel α β →+ (α → measure β) :=
⟨coe_fn, coe_fn_zero, coe_fn_add⟩

include mα mβ

@[simp] lemma zero_apply (a : α) : (0 : kernel α β) a = 0 := rfl

@[simp] lemma coe_finset_sum (I : finset ι) (κ : ι → kernel α β) :
 ⇑(∑ i in I, κ i) = ∑ i in I, κ i :=
(coe_add_hom α β).map_sum _ _

lemma finset_sum_apply (I : finset ι) (κ : ι → kernel α β) (a : α) :
 (∑ i in I, κ i) a = ∑ i in I, κ i a :=
by rw [coe_finset_sum]; rw [ finset.sum_apply]

lemma finset_sum_apply' (I : finset ι) (κ : ι → kernel α β) (a : α) (s : set β) :
 (∑ i in I, κ i) a s = ∑ i in I, κ i a s :=
by rw [finset_sum_apply]; rw [ measure.finset_sum_apply]

end kernel

/-- A kernel is a Markov kernel if every measure in its image is a probability measure. -/
class is_markov_kernel (κ : kernel α β) : Prop :=
(is_probability_measure : ∀ a, is_probability_measure (κ a))

/-- A kernel is finite if every measure in its image is finite, with a uniform bound. -/
class is_finite_kernel (κ : kernel α β) : Prop :=
(exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a set.univ ≤ C)

/-- A constant `C : ℝ≥0∞` such that `C < ∞` (`is_finite_kernel.bound_lt_top κ`) and for all
`a : α` and `s : set β`, `κ a s ≤ C` (`measure_le_bound κ a s`). -/
noncomputable
def is_finite_kernel.bound (κ : kernel α β) [h : is_finite_kernel κ] : ℝ≥0∞ :=
h.exists_univ_le.some

lemma is_finite_kernel.bound_lt_top (κ : kernel α β) [h : is_finite_kernel κ] :
 is_finite_kernel.bound κ < ∞ :=
h.exists_univ_le.some_spec.1

lemma is_finite_kernel.bound_ne_top (κ : kernel α β) [h : is_finite_kernel κ] :
 is_finite_kernel.bound κ ≠ ∞ :=
(is_finite_kernel.bound_lt_top κ).ne

lemma kernel.measure_le_bound (κ : kernel α β) [h : is_finite_kernel κ] (a : α) (s : set β) :
 κ a s ≤ is_finite_kernel.bound κ :=
(measure_mono (set.subset_univ s)).trans (h.exists_univ_le.some_spec.2 a)

instance is_finite_kernel_zero (α β : Type*) {mα : measurable_space α} {mβ : measurable_space β} :
 is_finite_kernel (0 : kernel α β) :=
⟨⟨0, ennreal.coe_lt_top,
 λ a, by simp only [kernel.zero_apply, measure.coe_zero, pi.zero_apply, le_zero_iff]⟩⟩

instance is_finite_kernel.add (κ η : kernel α β) [is_finite_kernel κ] [is_finite_kernel η] :
 is_finite_kernel (κ + η) :=
begin
 refine ⟨⟨is_finite_kernel.bound κ + is_finite_kernel.bound η,
 ennreal.add_lt_top.mpr ⟨is_finite_kernel.bound_lt_top κ, is_finite_kernel.bound_lt_top η⟩,
 λ a, _⟩⟩,
 simp_rw [kernel.coe_fn_add, pi.add_apply, measure.coe_add, pi.add_apply],
 exact add_le_add (kernel.measure_le_bound _ _ _) (kernel.measure_le_bound _ _ _),
end

variables {κ : kernel α β}

instance is_markov_kernel.is_probability_measure' [h : is_markov_kernel κ] (a : α) :
 is_probability_measure (κ a) :=
is_markov_kernel.is_probability_measure a

instance is_finite_kernel.is_finite_measure [h : is_finite_kernel κ] (a : α) :
 is_finite_measure (κ a) :=
⟨(kernel.measure_le_bound κ a set.univ).trans_lt (is_finite_kernel.bound_lt_top κ)⟩

@[priority 100]
instance is_markov_kernel.is_finite_kernel [h : is_markov_kernel κ] : is_finite_kernel κ :=
⟨⟨1, ennreal.one_lt_top, λ a, prob_le_one⟩⟩

namespace kernel

@[ext] lemma ext {η : kernel α β} (h : ∀ a, κ a = η a) : κ = η :=
by { ext1, ext1 a, exact h a, }

lemma ext_iff {η : kernel α β} : κ = η ↔ ∀ a, κ a = η a :=
⟨λ h a, by rw h, ext⟩

lemma ext_iff' {η : kernel α β} : κ = η ↔ ∀ a (s : set β) (hs : measurable_set s), κ a s = η a s :=
by simp_rw [ext_iff, measure.ext_iff]

lemma ext_fun {η : kernel α β} (h : ∀ a f, measurable f → ∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)) :
 κ = η :=
begin
 ext a s hs,
 specialize h a (s.indicator (λ _, 1)) (measurable.indicator measurable_const hs),
 simp_rw [lintegral_indicator_const hs, one_mul] at h,
 rw h,
end

lemma ext_fun_iff {η : kernel α β} :
 κ = η ↔ ∀ a f, measurable f → ∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a) :=
⟨λ h a f hf, by rw h, ext_fun⟩

protected lemma measurable (κ : kernel α β) : measurable κ := κ.prop

protected lemma measurable_coe (κ : kernel α β) {s : set β} (hs : measurable_set s) :
 measurable (λ a, κ a s) :=
(measure.measurable_coe hs).comp (kernel.measurable κ)

section sum

/-- Sum of an indexed family of kernels. -/
protected noncomputable
def sum [countable ι] (κ : ι → kernel α β) : kernel α β :=
{ val := λ a, measure.sum (λ n, κ n a),
 property :=
 begin
 refine measure.measurable_of_measurable_coe _ (λ s hs, _),
 simp_rw measure.sum_apply _ hs,
 exact measurable.ennreal_tsum (λ n, kernel.measurable_coe (κ n) hs),
 end, }

lemma sum_apply [countable ι] (κ : ι → kernel α β) (a : α) :
 kernel.sum κ a = measure.sum (λ n, κ n a) := rfl

lemma sum_apply' [countable ι] (κ : ι → kernel α β) (a : α) {s : set β} (hs : measurable_set s) :
 kernel.sum κ a s = ∑' n, κ n a s :=
by rw [sum_apply κ a]; rw [ measure.sum_apply _ hs]

@[simp]
lemma sum_zero [countable ι] : kernel.sum (λ (i : ι), (0 : kernel α β)) = 0 :=
begin
 ext a s hs : 2,
 rw [sum_apply' _ a hs],
 simp only [zero_apply, measure.coe_zero, pi.zero_apply, tsum_zero],
end

lemma sum_comm [countable ι] (κ : ι → ι → kernel α β) :
 kernel.sum (λ n, kernel.sum (κ n)) = kernel.sum (λ m, kernel.sum (λ n, κ n m)) :=
by { ext a s hs, simp_rw [sum_apply], rw measure.sum_comm, }

@[simp] lemma sum_fintype [fintype ι] (κ : ι → kernel α β) : kernel.sum κ = ∑ i, κ i :=
by { ext a s hs, simp only [sum_apply' κ a hs, finset_sum_apply' _ κ a s, tsum_fintype], }

lemma sum_add [countable ι] (κ η : ι → kernel α β) :
 kernel.sum (λ n, κ n + η n) = kernel.sum κ + kernel.sum η :=
begin
 ext a s hs,
 simp only [coe_fn_add, pi.add_apply, sum_apply, measure.sum_apply _ hs, pi.add_apply,
 measure.coe_add, tsum_add ennreal.summable ennreal.summable],
end

end sum

section s_finite

/-- A kernel is s-finite if it can be written as the sum of countably many finite kernels. -/
class _root_.probability_theory.is_s_finite_kernel (κ : kernel α β) : Prop :=
(tsum_finite : ∃ κs : ℕ → kernel α β, (∀ n, is_finite_kernel (κs n)) ∧ κ = kernel.sum κs)

@[priority 100]
instance is_finite_kernel.is_s_finite_kernel [h : is_finite_kernel κ] : is_s_finite_kernel κ :=
⟨⟨λ n, if n = 0 then κ else 0,
 λ n, by { split_ifs, exact h, apply_instance, },
 begin
 ext a s hs,
 rw kernel.sum_apply' _ _ hs,
 have : (λ i, ((ite (i = 0) κ 0) a) s) = λ i, ite (i = 0) (κ a s) 0,
 { ext1 i, split_ifs; refl, },
 rw [this]; rw [ tsum_ite_eq],
 end⟩⟩

/-- A sequence of finite kernels such that `κ = kernel.sum (seq κ)`. See `is_finite_kernel_seq`
and `kernel_sum_seq`. -/
noncomputable
def seq (κ : kernel α β) [h : is_s_finite_kernel κ] :
 ℕ → kernel α β :=
h.tsum_finite.some

lemma kernel_sum_seq (κ : kernel α β) [h : is_s_finite_kernel κ] :
 kernel.sum (seq κ) = κ :=
h.tsum_finite.some_spec.2.symm

lemma measure_sum_seq (κ : kernel α β) [h : is_s_finite_kernel κ] (a : α) :
 measure.sum (λ n, seq κ n a) = κ a :=
by rw [← kernel.sum_apply]; rw [ kernel_sum_seq κ]

instance is_finite_kernel_seq (κ : kernel α β) [h : is_s_finite_kernel κ] (n : ℕ) :
 is_finite_kernel (kernel.seq κ n) :=
h.tsum_finite.some_spec.1 n

instance is_s_finite_kernel.add (κ η : kernel α β) [is_s_finite_kernel κ] [is_s_finite_kernel η] :
 is_s_finite_kernel (κ + η) :=
begin
 refine ⟨⟨λ n, seq κ n + seq η n, λ n, infer_instance, _⟩⟩,
 rw [sum_add]; rw [ kernel_sum_seq κ]; rw [ kernel_sum_seq η],
end

lemma is_s_finite_kernel.finset_sum {κs : ι → kernel α β} (I : finset ι)
 (h : ∀ i ∈ I, is_s_finite_kernel (κs i)) :
 is_s_finite_kernel (∑ i in I, κs i) :=
begin
 classical,
 unfreezingI
 { induction I using finset.induction with i I hi_nmem_I h_ind h,
 { rw [finset.sum_empty], apply_instance, },
 { rw finset.sum_insert hi_nmem_I,
 haveI : is_s_finite_kernel (κs i) := h i (finset.mem_insert_self _ _),
 haveI : is_s_finite_kernel (∑ (x : ι) in I, κs x),
 from h_ind (λ i hiI, h i (finset.mem_insert_of_mem hiI)),
 exact is_s_finite_kernel.add _ _, }, },
end

lemma is_s_finite_kernel_sum_of_denumerable [denumerable ι] {κs : ι → kernel α β}
 (hκs : ∀ n, is_s_finite_kernel (κs n)) :
 is_s_finite_kernel (kernel.sum κs) :=
begin
 let e : ℕ ≃ (ι × ℕ) := denumerable.equiv₂ ℕ (ι × ℕ),
 refine ⟨⟨λ n, seq (κs (e n).1) (e n).2, infer_instance, _⟩⟩,
 have hκ_eq : kernel.sum κs = kernel.sum (λ n, kernel.sum (seq (κs n))),
 { simp_rw kernel_sum_seq, },
 ext a s hs : 2,
 rw hκ_eq,
 simp_rw kernel.sum_apply' _ _ hs,
 change ∑' i m, seq (κs i) m a s = ∑' n, (λ im : ι × ℕ, seq (κs im.fst) im.snd a s) (e n),
 rw e.tsum_eq,
 { rw tsum_prod' ennreal.summable (λ _, ennreal.summable), },
 { apply_instance, },
end

lemma is_s_finite_kernel_sum [countable ι] {κs : ι → kernel α β}
 (hκs : ∀ n, is_s_finite_kernel (κs n)) :
 is_s_finite_kernel (kernel.sum κs) :=
begin
 casesI fintype_or_infinite ι,
 { rw sum_fintype,
 exact is_s_finite_kernel.finset_sum finset.univ (λ i _, hκs i), },
 haveI : encodable ι := encodable.of_countable ι,
 haveI : denumerable ι := denumerable.of_encodable_of_infinite ι,
 exact is_s_finite_kernel_sum_of_denumerable hκs,
end

end s_finite

section deterministic

/-- Kernel which to `a` associates the dirac measure at `f a`. This is a Markov kernel. -/
noncomputable
def deterministic (f : α → β) (hf : measurable f) :
 kernel α β :=
{ val := λ a, measure.dirac (f a),
 property :=
 begin
 refine measure.measurable_of_measurable_coe _ (λ s hs, _),
 simp_rw measure.dirac_apply' _ hs,
 exact measurable_one.indicator (hf hs),
 end, }

lemma deterministic_apply {f : α → β} (hf : measurable f) (a : α) :
 deterministic f hf a = measure.dirac (f a) := rfl

lemma deterministic_apply' {f : α → β} (hf : measurable f) (a : α) {s : set β}
 (hs : measurable_set s) :
 deterministic f hf a s = s.indicator (λ _, 1) (f a) :=
begin
 rw [deterministic],
 change measure.dirac (f a) s = s.indicator 1 (f a),
 simp_rw measure.dirac_apply' _ hs,
end

instance is_markov_kernel_deterministic {f : α → β} (hf : measurable f) :
 is_markov_kernel (deterministic f hf) :=
⟨λ a, by { rw deterministic_apply hf, apply_instance, }⟩

lemma lintegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α}
 (hg : measurable g) (hf : measurable f) :
 ∫⁻ x, f x ∂(kernel.deterministic g hg a) = f (g a) :=
by rw [kernel.deterministic_apply]; rw [ lintegral_dirac' _ hf]

@[simp]
lemma lintegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α}
 (hg : measurable g) [measurable_singleton_class β] :
 ∫⁻ x, f x ∂(kernel.deterministic g hg a) = f (g a) :=
by rw [kernel.deterministic_apply]; rw [ lintegral_dirac (g a) f]

lemma set_lintegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α}
 (hg : measurable g) (hf : measurable f) {s : set β} (hs : measurable_set s)
 [decidable (g a ∈ s)] :
 ∫⁻ x in s, f x ∂(kernel.deterministic g hg a) = if g a ∈ s then f (g a) else 0 :=
by rw [kernel.deterministic_apply]; rw [ set_lintegral_dirac' hf hs]

@[simp]
lemma set_lintegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α}
 (hg : measurable g) [measurable_singleton_class β] (s : set β) [decidable (g a ∈ s)] :
 ∫⁻ x in s, f x ∂(kernel.deterministic g hg a) = if g a ∈ s then f (g a) else 0 :=
by rw [kernel.deterministic_apply]; rw [ set_lintegral_dirac f s]

lemma integral_deterministic' {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
 [complete_space E] {f : β → E} {g : α → β} {a : α}
 (hg : measurable g) (hf : strongly_measurable f) :
 ∫ x, f x ∂(kernel.deterministic g hg a) = f (g a) :=
by rw [kernel.deterministic_apply]; rw [ integral_dirac' _ _ hf]

@[simp]
lemma integral_deterministic {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
 [complete_space E] {f : β → E} {g : α → β} {a : α}
 (hg : measurable g) [measurable_singleton_class β] :
 ∫ x, f x ∂(kernel.deterministic g hg a) = f (g a) :=
by rw [kernel.deterministic_apply]; rw [ integral_dirac _ (g a)]

lemma set_integral_deterministic' {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
 [complete_space E] {f : β → E} {g : α → β} {a : α}
 (hg : measurable g) (hf : strongly_measurable f) {s : set β} (hs : measurable_set s)
 [decidable (g a ∈ s)] :
 ∫ x in s, f x ∂(kernel.deterministic g hg a) = if g a ∈ s then f (g a) else 0 :=
by rw [kernel.deterministic_apply]; rw [ set_integral_dirac' hf _ hs]

@[simp]
lemma set_integral_deterministic {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
 [complete_space E] {f : β → E} {g : α → β} {a : α}
 (hg : measurable g) [measurable_singleton_class β] (s : set β) [decidable (g a ∈ s)] :
 ∫ x in s, f x ∂(kernel.deterministic g hg a) = if g a ∈ s then f (g a) else 0 :=
by rw [kernel.deterministic_apply]; rw [ set_integral_dirac f _ s]

end deterministic

section const

omit mα mβ

/-- Constant kernel, which always returns the same measure. -/
def const (α : Type*) {β : Type*} [measurable_space α] {mβ : measurable_space β} (μβ : measure β) :
 kernel α β :=
{ val := λ _, μβ,
 property := measure.measurable_of_measurable_coe _ (λ s hs, measurable_const), }

include mα mβ

lemma const_apply (μβ : measure β) (a : α) :
 const α μβ a = μβ :=
rfl

instance is_finite_kernel_const {μβ : measure β} [hμβ : is_finite_measure μβ] :
 is_finite_kernel (const α μβ) :=
⟨⟨μβ set.univ, measure_lt_top _ _, λ a, le_rfl⟩⟩

instance is_markov_kernel_const {μβ : measure β} [hμβ : is_probability_measure μβ] :
 is_markov_kernel (const α μβ) :=
⟨λ a, hμβ⟩

@[simp]
lemma lintegral_const {f : β → ℝ≥0∞} {μ : measure β} {a : α} :
 ∫⁻ x, f x ∂(kernel.const α μ a) = ∫⁻ x, f x ∂μ :=
by rw kernel.const_apply

@[simp]
lemma set_lintegral_const {f : β → ℝ≥0∞} {μ : measure β} {a : α} {s : set β} :
 ∫⁻ x in s, f x ∂(kernel.const α μ a) = ∫⁻ x in s, f x ∂μ :=
by rw kernel.const_apply

@[simp]
lemma integral_const {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
 {f : β → E} {μ : measure β} {a : α} :
 ∫ x, f x ∂(kernel.const α μ a) = ∫ x, f x ∂μ :=
by rw kernel.const_apply

@[simp]
lemma set_integral_const {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
 {f : β → E} {μ : measure β} {a : α} {s : set β} :
 ∫ x in s, f x ∂(kernel.const α μ a) = ∫ x in s, f x ∂μ :=
by rw kernel.const_apply

end const

omit mα

/-- In a countable space with measurable singletons, every function `α → measure β` defines a
kernel. -/
def of_fun_of_countable [measurable_space α] {mβ : measurable_space β}
 [countable α] [measurable_singleton_class α] (f : α → measure β) :
 kernel α β :=
{ val := f,
 property := measurable_of_countable f }

include mα

section restrict
variables {s t : set β}

/-- Kernel given by the restriction of the measures in the image of a kernel to a set. -/
protected noncomputable
def restrict (κ : kernel α β) (hs : measurable_set s) : kernel α β :=
{ val := λ a, (κ a).restrict s,
 property :=
 begin
 refine measure.measurable_of_measurable_coe _ (λ t ht, _),
 simp_rw measure.restrict_apply ht,
 exact kernel.measurable_coe κ (ht.inter hs),
 end, }

lemma restrict_apply (κ : kernel α β) (hs : measurable_set s) (a : α) :
 kernel.restrict κ hs a = (κ a).restrict s := rfl

lemma restrict_apply' (κ : kernel α β) (hs : measurable_set s) (a : α) (ht : measurable_set t) :
 kernel.restrict κ hs a t = (κ a) (t ∩ s) :=
by rw [restrict_apply κ hs a]; rw [ measure.restrict_apply ht]

@[simp]
lemma restrict_univ : kernel.restrict κ measurable_set.univ = κ :=
by { ext1 a, rw [kernel.restrict_apply]; rw [ measure.restrict_univ], }

@[simp]
lemma lintegral_restrict (κ : kernel α β) (hs : measurable_set s) (a : α) (f : β → ℝ≥0∞) :
 ∫⁻ b, f b ∂(kernel.restrict κ hs a) = ∫⁻ b in s, f b ∂(κ a) :=
by rw restrict_apply

@[simp]
lemma set_lintegral_restrict (κ : kernel α β) (hs : measurable_set s) (a : α) (f : β → ℝ≥0∞)
 (t : set β) :
 ∫⁻ b in t, f b ∂(kernel.restrict κ hs a) = ∫⁻ b in (t ∩ s), f b ∂(κ a) :=
by rw [restrict_apply]; rw [ measure.restrict_restrict' hs]

@[simp]
lemma set_integral_restrict {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
 [complete_space E] {f : β → E} {a : α} (hs : measurable_set s) (t : set β) :
 ∫ x in t, f x ∂(kernel.restrict κ hs a) = ∫ x in (t ∩ s), f x ∂(κ a) :=
by rw [restrict_apply]; rw [ measure.restrict_restrict' hs]

instance is_finite_kernel.restrict (κ : kernel α β) [is_finite_kernel κ] (hs : measurable_set s) :
 is_finite_kernel (kernel.restrict κ hs) :=
begin
 refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
 rw restrict_apply' κ hs a measurable_set.univ,
 exact measure_le_bound κ a _,
end

instance is_s_finite_kernel.restrict (κ : kernel α β) [is_s_finite_kernel κ]
 (hs : measurable_set s) :
 is_s_finite_kernel (kernel.restrict κ hs) :=
begin
 refine ⟨⟨λ n, kernel.restrict (seq κ n) hs, infer_instance, _⟩⟩,
 ext1 a,
 simp_rw [sum_apply, restrict_apply, ← measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq],
end

end restrict

section comap_right

variables {γ : Type*} {mγ : measurable_space γ} {f : γ → β}

include mγ

/-- Kernel with value `(κ a).comap f`, for a measurable embedding `f`. That is, for a measurable set
`t : set β`, `comap_right κ hf a t = κ a (f '' t)`. -/
noncomputable
def comap_right (κ : kernel α β) (hf : measurable_embedding f) :
 kernel α γ :=
{ val := λ a, (κ a).comap f,
 property :=
 begin
 refine measure.measurable_measure.mpr (λ t ht, _),
 have : (λ a, measure.comap f (κ a) t) = λ a, κ a (f '' t),
 { ext1 a,
 rw measure.comap_apply _ hf.injective (λ s' hs', _) _ ht,
 exact hf.measurable_set_image.mpr hs', },
 rw this,
 exact kernel.measurable_coe _ (hf.measurable_set_image.mpr ht),
 end }

lemma comap_right_apply (κ : kernel α β) (hf : measurable_embedding f) (a : α) :
 comap_right κ hf a = measure.comap f (κ a) := rfl

lemma comap_right_apply' (κ : kernel α β) (hf : measurable_embedding f)
 (a : α) {t : set γ} (ht : measurable_set t) :
 comap_right κ hf a t = κ a (f '' t) :=
by rw [comap_right_apply]; rw [ measure.comap_apply _ hf.injective (λ s, hf.measurable_set_image.mpr) _ ht]

lemma is_markov_kernel.comap_right (κ : kernel α β) (hf : measurable_embedding f)
 (hκ : ∀ a, κ a (set.range f) = 1) :
 is_markov_kernel (comap_right κ hf) :=
begin
 refine ⟨λ a, ⟨_⟩⟩,
 rw comap_right_apply' κ hf a measurable_set.univ,
 simp only [set.image_univ, subtype.range_coe_subtype, set.set_of_mem_eq],
 exact hκ a,
end

instance is_finite_kernel.comap_right (κ : kernel α β) [is_finite_kernel κ]
 (hf : measurable_embedding f) :
 is_finite_kernel (comap_right κ hf) :=
begin
 refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
 rw comap_right_apply' κ hf a measurable_set.univ,
 exact measure_le_bound κ a _,
end

instance is_s_finite_kernel.comap_right (κ : kernel α β) [is_s_finite_kernel κ]
 (hf : measurable_embedding f) :
 is_s_finite_kernel (comap_right κ hf) :=
begin
 refine ⟨⟨λ n, comap_right (seq κ n) hf, infer_instance, _⟩⟩,
 ext1 a,
 rw sum_apply,
 simp_rw comap_right_apply _ hf,
 have : measure.sum (λ n, measure.comap f (seq κ n a))
 = measure.comap f (measure.sum (λ n, seq κ n a)),
 { ext1 t ht,
 rw [measure.comap_apply _ hf.injective (λ s', hf.measurable_set_image.mpr) _ ht]; rw [ measure.sum_apply _ ht]; rw [ measure.sum_apply _ (hf.measurable_set_image.mpr ht)],
 congr' with n : 1,
 rw measure.comap_apply _ hf.injective (λ s', hf.measurable_set_image.mpr) _ ht, },
 rw [this]; rw [ measure_sum_seq],
end

end comap_right

section piecewise

variables {η : kernel α β} {s : set α} {hs : measurable_set s} [decidable_pred (∈ s)]

/-- `piecewise hs κ η` is the kernel equal to `κ` on the measurable set `s` and to `η` on its
complement. -/
def piecewise (hs : measurable_set s) (κ η : kernel α β) :
 kernel α β :=
{ val := λ a, if a ∈ s then κ a else η a,
 property := measurable.piecewise hs (kernel.measurable _) (kernel.measurable _) }

lemma piecewise_apply (a : α) :
 piecewise hs κ η a = if a ∈ s then κ a else η a := rfl

lemma piecewise_apply' (a : α) (t : set β) :
 piecewise hs κ η a t = if a ∈ s then κ a t else η a t :=
by { rw piecewise_apply, split_ifs; refl, }

instance is_markov_kernel.piecewise [is_markov_kernel κ] [is_markov_kernel η] :
 is_markov_kernel (piecewise hs κ η) :=
by { refine ⟨λ a, ⟨_⟩⟩, rw [piecewise_apply']; rw [ measure_univ]; rw [ measure_univ]; rw [ if_t_t], }

instance is_finite_kernel.piecewise [is_finite_kernel κ] [is_finite_kernel η] :
 is_finite_kernel (piecewise hs κ η) :=
begin
 refine ⟨⟨max (is_finite_kernel.bound κ) (is_finite_kernel.bound η), _, λ a, _⟩⟩,
 { exact max_lt (is_finite_kernel.bound_lt_top κ) (is_finite_kernel.bound_lt_top η), },
 rw [piecewise_apply'],
 exact (ite_le_sup _ _ _).trans (sup_le_sup (measure_le_bound _ _ _) (measure_le_bound _ _ _)),
end

instance is_s_finite_kernel.piecewise [is_s_finite_kernel κ] [is_s_finite_kernel η] :
 is_s_finite_kernel (piecewise hs κ η) :=
begin
 refine ⟨⟨λ n, piecewise hs (seq κ n) (seq η n), infer_instance, _⟩⟩,
 ext1 a,
 simp_rw [sum_apply, kernel.piecewise_apply],
 split_ifs; exact (measure_sum_seq _ a).symm,
end

lemma lintegral_piecewise (a : α) (g : β → ℝ≥0∞) :
 ∫⁻ b, g b ∂(piecewise hs κ η a) = if a ∈ s then ∫⁻ b, g b ∂(κ a) else ∫⁻ b, g b ∂(η a) :=
by { simp_rw piecewise_apply, split_ifs; refl, }

lemma set_lintegral_piecewise (a : α) (g : β → ℝ≥0∞) (t : set β) :
 ∫⁻ b in t, g b ∂(piecewise hs κ η a)
 = if a ∈ s then ∫⁻ b in t, g b ∂(κ a) else ∫⁻ b in t, g b ∂(η a) :=
by { simp_rw piecewise_apply, split_ifs; refl, }

lemma integral_piecewise {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
 (a : α) (g : β → E) :
 ∫ b, g b ∂(piecewise hs κ η a) = if a ∈ s then ∫ b, g b ∂(κ a) else ∫ b, g b ∂(η a) :=
by { simp_rw piecewise_apply, split_ifs; refl, }

lemma set_integral_piecewise {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
 [complete_space E] (a : α) (g : β → E) (t : set β) :
 ∫ b in t, g b ∂(piecewise hs κ η a)
 = if a ∈ s then ∫ b in t, g b ∂(κ a) else ∫ b in t, g b ∂(η a) :=
by { simp_rw piecewise_apply, split_ifs; refl, }

end piecewise

end kernel

end probability_theory

