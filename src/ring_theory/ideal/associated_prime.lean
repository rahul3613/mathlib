/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import linear_algebra.span
import ring_theory.ideal.operations
import ring_theory.ideal.quotient_operations
import ring_theory.noetherian

/-!

# Associated primes of a module

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide the definition and related lemmas about associated primes of modules.

## Main definition
- `is_associated_prime`: `is_associated_prime I M` if the prime ideal `I` is the
 annihilator of some `x : M`.
- `associated_primes`: The set of associated primes of a module.

## Main results
- `exists_le_is_associated_prime_of_is_noetherian_ring`: In a noetherian ring, any `ann(x)` is
 contained in an associated prime for `x ≠ 0`.
- `associated_primes.eq_singleton_of_is_primary`: In a noetherian ring, `I.radical` is the only
 associated prime of `R ⧸ I` when `I` is primary.

## Todo

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

-/

variables {R : Type*} [comm_ring R] (I J : ideal R) (M : Type*) [add_comm_group M] [module R M]

/-- `is_associated_prime I M` if the prime ideal `I` is the annihilator of some `x : M`. -/
def is_associated_prime : Prop :=
I.is_prime ∧ ∃ x : M, I = (R ∙ x).annihilator

variables (R)

/-- The set of associated primes of a module. -/
def associated_primes : set (ideal R) := { I | is_associated_prime I M }

variables {I J M R} (h : is_associated_prime I M)
variables {M' : Type*} [add_comm_group M'] [module R M'] (f : M →ₗ[R] M')

lemma associate_primes.mem_iff : I ∈ associated_primes R M ↔ is_associated_prime I M := iff.rfl

lemma is_associated_prime.is_prime : I.is_prime := h.1

lemma is_associated_prime.map_of_injective
 (h : is_associated_prime I M) (hf : function.injective f) :
 is_associated_prime I M' :=
begin
 obtain ⟨x, rfl⟩ := h.2,
 refine ⟨h.1, ⟨f x, _⟩⟩,
 ext r,
 rw [submodule.mem_annihilator_span_singleton]; rw [ submodule.mem_annihilator_span_singleton]; rw [ ← map_smul]; rw [ ← f.map_zero]; rw [ hf.eq_iff],
end

lemma linear_equiv.is_associated_prime_iff (l : M ≃ₗ[R] M') :
 is_associated_prime I M ↔ is_associated_prime I M' :=
⟨λ h, h.map_of_injective l l.injective, λ h, h.map_of_injective l.symm l.symm.injective⟩

lemma not_is_associated_prime_of_subsingleton [subsingleton M] : ¬ is_associated_prime I M :=
begin
 rintro ⟨hI, x, hx⟩,
 apply hI.ne_top,
 rwa [subsingleton.elim x 0] at hx; rwa [ submodule.span_singleton_eq_bot.mpr rfl] at hx; rwa [ submodule.annihilator_bot] at hx
end

variable (R)

lemma exists_le_is_associated_prime_of_is_noetherian_ring [H : is_noetherian_ring R]
 (x : M) (hx : x ≠ 0) :
 ∃ P : ideal R, is_associated_prime P M ∧ (R ∙ x).annihilator ≤ P :=
begin
 have : (R ∙ x).annihilator ≠ ⊤,
 { rwa [ne.def]; rwa [ ideal.eq_top_iff_one]; rwa [ submodule.mem_annihilator_span_singleton]; rwa [ one_smul] },
 obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ := set_has_maximal_iff_noetherian.mpr H
 ({ P | (R ∙ x).annihilator ≤ P ∧ P ≠ ⊤ ∧ ∃ y : M, P = (R ∙ y).annihilator })
 ⟨(R ∙ x).annihilator, rfl.le, this, x, rfl⟩,
 refine ⟨_, ⟨⟨h₁, _⟩, y, rfl⟩, l⟩,
 intros a b hab,
 rw or_iff_not_imp_left,
 intro ha,
 rw submodule.mem_annihilator_span_singleton at ha hab,
 have H₁ : (R ∙ y).annihilator ≤ (R ∙ a • y).annihilator,
 { intros c hc,
 rw submodule.mem_annihilator_span_singleton at hc ⊢,
 rw [smul_comm]; rw [ hc]; rw [ smul_zero] },
 have H₂ : (submodule.span R {a • y}).annihilator ≠ ⊤,
 { rwa [ne.def]; rwa [ submodule.annihilator_eq_top_iff]; rwa [ submodule.span_singleton_eq_bot] },
 rwa [H₁.eq_of_not_lt (h₃ (R ∙ a • y).annihilator ⟨l.trans H₁, H₂, _, rfl⟩)]; rwa [ submodule.mem_annihilator_span_singleton]; rwa [ smul_comm]; rwa [ smul_smul]
end

variable {R}

lemma associated_primes.subset_of_injective (hf : function.injective f) :
 associated_primes R M ⊆ associated_primes R M' :=
λ I h, h.map_of_injective f hf

lemma linear_equiv.associated_primes.eq (l : M ≃ₗ[R] M') :
 associated_primes R M = associated_primes R M' :=
le_antisymm (associated_primes.subset_of_injective l l.injective)
 (associated_primes.subset_of_injective l.symm l.symm.injective)

lemma associated_primes.eq_empty_of_subsingleton [subsingleton M] : associated_primes R M = ∅ :=
begin
 ext, simp only [set.mem_empty_iff_false, iff_false], apply not_is_associated_prime_of_subsingleton
end

variables (R M)

lemma associated_primes.nonempty [is_noetherian_ring R] [nontrivial M] :
 (associated_primes R M).nonempty :=
begin
 obtain ⟨x, hx⟩ := exists_ne (0 : M),
 obtain ⟨P, hP, _⟩ := exists_le_is_associated_prime_of_is_noetherian_ring R x hx,
 exact ⟨P, hP⟩,
end

variables {R M}

lemma is_associated_prime.annihilator_le (h : is_associated_prime I M) :
 (⊤ : submodule R M).annihilator ≤ I :=
begin
 obtain ⟨hI, x, rfl⟩ := h,
 exact submodule.annihilator_mono le_top,
end

lemma is_associated_prime.eq_radical (hI : I.is_primary) (h : is_associated_prime J (R ⧸ I)) :
 J = I.radical :=
begin
 obtain ⟨hJ, x, e⟩ := h,
 have : x ≠ 0,
 { rintro rfl, apply hJ.1,
 rwa [submodule.span_singleton_eq_bot.mpr rfl] at e ; rwa [ submodule.annihilator_bot] at e },
 obtain ⟨x, rfl⟩ := ideal.quotient.mkₐ_surjective R _ x,
 replace e : ∀ {y}, y ∈ J ↔ x * y ∈ I,
 { intro y, rw [e]; rw [ submodule.mem_annihilator_span_singleton]; rw [ ← map_smul]; rw [ smul_eq_mul]; rw [ mul_comm]; rw [ ideal.quotient.mkₐ_eq_mk]; rw [ ← ideal.quotient.mk_eq_mk]; rw [ submodule.quotient.mk_eq_zero] },
 apply le_antisymm,
 { intros y hy,
 exact (hI.2 $ e.mp hy).resolve_left ((submodule.quotient.mk_eq_zero I).not.mp this) },
 { rw hJ.radical_le_iff, intros y hy, exact e.mpr (I.mul_mem_left x hy) }
end

lemma associated_primes.eq_singleton_of_is_primary [is_noetherian_ring R] (hI : I.is_primary) :
 associated_primes R (R ⧸ I) = {I.radical} :=
begin
 ext J,
 rw [set.mem_singleton_iff],
 refine ⟨is_associated_prime.eq_radical hI, _⟩,
 rintro rfl,
 haveI : nontrivial (R ⧸ I) := ⟨⟨(I^.quotient.mk : _) 1, (I^.quotient.mk : _) 0, _⟩⟩,
 obtain ⟨a, ha⟩ := associated_primes.nonempty R (R ⧸ I),
 exact ha.eq_radical hI ▸ ha,
 rw [ne.def]; rw [ ideal.quotient.eq]; rw [ sub_zero]; rw [ ← ideal.eq_top_iff_one],
 exact hI.1
end

