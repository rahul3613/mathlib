/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/

import algebra.big_operators.associated
import algebra.gcd_monoid.basic
import data.finsupp.multiset
import ring_theory.noetherian
import ring_theory.multiplicity

/-!

# Unique factorization

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main Definitions
* `wf_dvd_monoid` holds for `monoid`s for which a strict divisibility relation is
  well-founded.
* `unique_factorization_monoid` holds for `wf_dvd_monoid`s where
  `irreducible` is equivalent to `prime`

## To do
* set up the complete lattice structure on `factor_set`.

-/

variables {α : Type*}
local infix ` ~ᵤ ` : 50 := associated

/-- Well-foundedness of the strict version of |, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
  -/
class wf_dvd_monoid (α : Type*) [comm_monoid_with_zero α] : Prop :=
(well_founded_dvd_not_unit : well_founded (@dvd_not_unit α _))

export wf_dvd_monoid (well_founded_dvd_not_unit)

@[priority 100]  -- see Note [lower instance priority]
instance is_noetherian_ring.wf_dvd_monoid [comm_ring α] [is_domain α] [is_noetherian_ring α] :
  wf_dvd_monoid α :=
⟨by { convert inv_image.wf (λ a, ideal.span ({a} : set α)) (well_founded_submodule_gt _ _),
      ext,
      exact ideal.span_singleton_lt_span_singleton.symm }⟩

namespace wf_dvd_monoid

variables [comm_monoid_with_zero α]
open associates nat

theorem of_wf_dvd_monoid_associates (h : wf_dvd_monoid (associates α)): wf_dvd_monoid α :=
⟨begin
  haveI := h,
  refine (surjective.well_founded_iff mk_surjective _).2 well_founded_dvd_not_unit,
  intros, rw mk_dvd_not_unit_mk_iff
end⟩

variables [wf_dvd_monoid α]

instance wf_dvd_monoid_associates : wf_dvd_monoid (associates α) :=
⟨begin
  refine (surjective.well_founded_iff mk_surjective _).1 well_founded_dvd_not_unit,
  intros, rw mk_dvd_not_unit_mk_iff
end⟩

theorem well_founded_associates : well_founded ((<) : associates α → associates α → Prop) :=
subrelation.wf (λ x y, dvd_not_unit_of_lt) well_founded_dvd_not_unit

local attribute [elab_as_eliminator] well_founded.fix

lemma exists_irreducible_factor {a : α} (ha : ¬ is_unit a) (ha0 : a ≠ 0) :
  ∃ i, irreducible i ∧ i ∣ a :=
let ⟨b, hs, hr⟩ := well_founded_dvd_not_unit.has_min {b | b ∣ a ∧ ¬ is_unit b} ⟨a, dvd_rfl, ha⟩ in
⟨b, ⟨hs.2, λ c d he, let h := dvd_trans ⟨d, he⟩ hs.1 in or_iff_not_imp_left.2 $
  λ hc, of_not_not $ λ hd, hr c ⟨h, hc⟩ ⟨ne_zero_of_dvd_ne_zero ha0 h, d, hd, he⟩⟩, hs.1⟩

@[elab_as_eliminator] lemma induction_on_irreducible {P : α → Prop} (a : α)
  (h0 : P 0) (hu : ∀ u : α, is_unit u → P u)
  (hi : ∀ a i : α, a ≠ 0 → irreducible i → P a → P (i * a)) :
  P a :=
by haveI := classical.dec; exact
well_founded_dvd_not_unit.fix
  (λ a ih, if ha0 : a = 0 then ha0.substr h0
    else if hau : is_unit a then hu a hau
    else let ⟨i, hii, b, hb⟩ := exists_irreducible_factor hau ha0,
      hb0 : b ≠ 0 := ne_zero_of_dvd_ne_zero ha0 ⟨i, mul_comm i b ▸ hb⟩ in
      hb.symm ▸ hi b i hb0 hii $ ih b ⟨hb0, i, hii.1, mul_comm i b ▸ hb⟩)
  a

lemma exists_factors (a : α) : a ≠ 0 →
  ∃ f : multiset α, (∀ b ∈ f, irreducible b) ∧ associated f.prod a :=
induction_on_irreducible a
  (λ h, (h rfl).elim)
  (λ u hu _, ⟨0, λ _ h, h.elim, hu.unit, one_mul _⟩)
  (λ a i ha0 hi ih _,
    let ⟨s, hs⟩ := ih ha0 in
    ⟨i ::ₘ s, λ b H, (multiset.mem_cons.1 H).elim (λ h, h.symm ▸ hi) (hs.1 b),
      by { rw s.prod_cons i, exact hs.2.mul_left i }⟩)

lemma not_unit_iff_exists_factors_eq (a : α) (hn0 : a ≠ 0) :
  ¬ is_unit a ↔ ∃ f : multiset α, (∀ b ∈ f, irreducible b) ∧ f.prod = a ∧ f ≠ ∅ :=
⟨λ hnu, begin
  obtain ⟨f, hi, u, rfl⟩ := exists_factors a hn0,
  obtain ⟨b, h⟩ := multiset.exists_mem_of_ne_zero (λ h : f = 0, hnu $ by simp [h]),
  classical, refine ⟨(f.erase b).cons (b * u), λ a ha, _, _, multiset.cons_ne_zero⟩,
  { obtain (rfl|ha) := multiset.mem_cons.1 ha,
    exacts [associated.irreducible ⟨u,rfl⟩ (hi b h), hi a (multiset.mem_of_mem_erase ha)] },
  { rw [multiset.prod_cons, mul_comm b, mul_assoc, multiset.prod_erase h, mul_comm] },
end,
λ ⟨f, hi, he, hne⟩, let ⟨b, h⟩ := multiset.exists_mem_of_ne_zero hne in
  not_is_unit_of_not_is_unit_dvd (hi b h).not_unit $ he ▸ multiset.dvd_prod h⟩

end wf_dvd_monoid

theorem wf_dvd_monoid.of_well_founded_associates [cancel_comm_monoid_with_zero α]
  (h : well_founded ((<) : associates α → associates α → Prop)) : wf_dvd_monoid α :=
wf_dvd_monoid.of_wf_dvd_monoid_associates
  ⟨by { convert h, ext, exact associates.dvd_not_unit_iff_lt }⟩

theorem wf_dvd_monoid.iff_well_founded_associates [cancel_comm_monoid_with_zero α] :
  wf_dvd_monoid α ↔ well_founded ((<) : associates α → associates α → Prop) :=
⟨by apply wf_dvd_monoid.well_founded_associates, wf_dvd_monoid.of_well_founded_associates⟩
section prio
set_option default_priority 100 -- see Note [default priority]
/-- unique factorization monoids.

These are defined as `cancel_comm_monoid_with_zero`s with well-founded strict divisibility
relations, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_exists_unique_irreducible_factors`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factors`

-/
class unique_factorization_monoid (α : Type*) [cancel_comm_monoid_with_zero α]
  extends wf_dvd_monoid α : Prop :=
(irreducible_iff_prime : ∀ {a : α}, irreducible a ↔ prime a)

/-- Can't be an instance because it would cause a loop `ufm → wf_dvd_monoid → ufm → ...`. -/
@[reducible] lemma ufm_of_gcd_of_wf_dvd_monoid [cancel_comm_monoid_with_zero α]
  [wf_dvd_monoid α] [gcd_monoid α] : unique_factorization_monoid α :=
{ irreducible_iff_prime := λ _, gcd_monoid.irreducible_iff_prime
  .. ‹wf_dvd_monoid α› }

instance associates.ufm [cancel_comm_monoid_with_zero α]
  [unique_factorization_monoid α] : unique_factorization_monoid (associates α) :=
{ irreducible_iff_prime := by { rw ← associates.irreducible_iff_prime_iff,
    apply unique_factorization_monoid.irreducible_iff_prime, }
  .. (wf_dvd_monoid.wf_dvd_monoid_associates : wf_dvd_monoid (associates α)) }

end prio

namespace unique_factorization_monoid
variables [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]

theorem exists_prime_factors (a : α) : a ≠ 0 →
  ∃ f : multiset α, (∀b ∈ f, prime b) ∧ f.prod ~ᵤ a :=
by { simp_rw ← unique_factorization_monoid.irreducible_iff_prime,
     apply wf_dvd_monoid.exists_factors a }

@[elab_as_eliminator] lemma induction_on_prime {P : α → Prop}
  (a : α) (h₁ : P 0) (h₂ : ∀ x : α, is_unit x → P x)
  (h₃ : ∀ a p : α, a ≠ 0 → prime p → P a → P (p * a)) : P a :=
begin
  simp_rw ← unique_factorization_monoid.irreducible_iff_prime at h₃,
  exact wf_dvd_monoid.induction_on_irreducible a h₁ h₂ h₃,
end

end unique_factorization_monoid

lemma prime_factors_unique [cancel_comm_monoid_with_zero α] : ∀ {f g : multiset α},
  (∀ x ∈ f, prime x) → (∀ x ∈ g, prime x) → f.prod ~ᵤ g.prod →
  multiset.rel associated f g :=
by haveI := classical.dec_eq α; exact
λ f, multiset.induction_on f
  (λ g _ hg h,
    multiset.rel_zero_left.2 $
    multiset.eq_zero_of_forall_not_mem $ λ x hx,
    have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
    (hg x hx).not_unit $ is_unit_iff_dvd_one.2 $
    (multiset.dvd_prod hx).trans (is_unit_iff_dvd_one.1 this))
  (λ p f ih g hf hg hfg,
    let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
      (hf p (by simp)) (λ q hq, hg _ hq) $
        hfg.dvd_iff_dvd_right.1
          (show p ∣ (p ::ₘ f).prod, by simp) in
    begin
      rw ← multiset.cons_erase hbg,
      exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
        (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
        (associated.of_mul_left
          (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
        (hf p (by simp)).ne_zero)),
    end)

namespace unique_factorization_monoid
variables [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]

lemma factors_unique {f g : multiset α} (hf : ∀ x ∈ f, irreducible x) (hg : ∀ x ∈ g, irreducible x)
  (h : f.prod ~ᵤ g.prod) : multiset.rel associated f g :=
prime_factors_unique
  (λ x hx, irreducible_iff_prime.mp (hf x hx))
  (λ x hx, irreducible_iff_prime.mp (hg x hx))
  h

end unique_factorization_monoid

/-- If an irreducible has a prime factorization,
  then it is an associate of one of its prime factors. -/
lemma prime_factors_irreducible [cancel_comm_monoid_with_zero α] {a : α} {f : multiset α}
  (ha : irreducible a) (pfa : (∀ b ∈ f, prime b) ∧ f.prod ~ᵤ a) :
  ∃ p, a ~ᵤ p ∧ f = {p} :=
begin
  haveI := classical.dec_eq α,
  refine multiset.induction_on f (λ h, (ha.not_unit
    (associated_one_iff_is_unit.1 (associated.symm h))).elim) _ pfa.2 pfa.1,
  rintros p s _ ⟨u, hu⟩ hs,
  use p,
  have hs0 : s = 0,
  { by_contra hs0,
    obtain ⟨q, hq⟩ := multiset.exists_mem_of_ne_zero hs0,
    apply (hs q (by simp [hq])).2.1,
    refine (ha.is_unit_or_is_unit (_ : _ = ((p * ↑u) * (s.erase q).prod) * _)).resolve_left _,
    { rw [mul_right_comm _ _ q, mul_assoc, ← multiset.prod_cons, multiset.cons_erase hq, ← hu,
        mul_comm, mul_comm p _, mul_assoc],
      simp, },
    apply mt is_unit_of_mul_is_unit_left (mt is_unit_of_mul_is_unit_left _),
    apply (hs p (multiset.mem_cons_self _ _)).2.1 },
  simp only [mul_one, multiset.prod_cons, multiset.prod_zero, hs0] at *,
  exact ⟨associated.symm ⟨u, hu⟩, rfl⟩,
end

section exists_prime_factors

variables [cancel_comm_monoid_with_zero α]
variables (pf : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, prime b) ∧ f.prod ~ᵤ a)

include pf

lemma wf_dvd_monoid.of_exists_prime_factors : wf_dvd_monoid α :=
⟨begin
  classical,
  refine rel_hom_class.well_founded
    (rel_hom.mk _ _ : (dvd_not_unit : α → α → Prop) →r ((<) : ℕ∞ → ℕ∞ → Prop))
    (with_top.well_founded_lt nat.lt_wf),
  { intro a,
    by_cases h : a = 0, { exact ⊤ },
    exact (classical.some (pf a h)).card },

  rintros a b ⟨ane0, ⟨c, hc, b_eq⟩⟩,
  rw dif_neg ane0,
  by_cases h : b = 0, { simp [h, lt_top_iff_ne_top] },
  rw [dif_neg h, with_top.coe_lt_coe],
  have cne0 : c ≠ 0, { refine mt (λ con, _) h, rw [b_eq, con, mul_zero] },
  calc multiset.card (classical.some (pf a ane0))
      < _ + multiset.card (classical.some (pf c cne0)) :
    lt_add_of_pos_right _ (multiset.card_pos.mpr (λ con, hc (associated_one_iff_is_unit.mp _)))
  ... = multiset.card (classical.some (pf a ane0) + classical.some (pf c cne0)) :
    (multiset.card_add _ _).symm
  ... = multiset.card (classical.some (pf b h)) :
    multiset.card_eq_card_of_rel (prime_factors_unique _ (classical.some_spec (pf _ h)).1 _),
  { convert (classical.some_spec (pf c cne0)).2.symm,
    rw [con, multiset.prod_zero] },
  { intros x hadd,
    rw multiset.mem_add at hadd,
    cases hadd; apply (classical.some_spec (pf _ _)).1 _ hadd },
  { rw multiset.prod_add,
    transitivity a * c,
    { apply associated.mul_mul; apply (classical.some_spec (pf _ _)).2 },
    { rw ← b_eq,
      apply (classical.some_spec (pf _ _)).2.symm, } }
end⟩

lemma irreducible_iff_prime_of_exists_prime_factors {p : α} : irreducible p ↔ prime p :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0] },
  refine ⟨λ h, _, prime.irreducible⟩,
  obtain ⟨f, hf⟩ := pf p hp0,
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf,
  rw hq.prime_iff,
  exact hf.1 q (multiset.mem_singleton_self _)
end

theorem unique_factorization_monoid.of_exists_prime_factors :
  unique_factorization_monoid α :=
{ irreducible_iff_prime := λ _, irreducible_iff_prime_of_exists_prime_factors pf,
  .. wf_dvd_monoid.of_exists_prime_factors pf }

end exists_prime_factors

theorem unique_factorization_monoid.iff_exists_prime_factors [cancel_comm_monoid_with_zero α] :
  unique_factorization_monoid α ↔
    (∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, prime b) ∧ f.prod ~ᵤ a) :=
⟨λ h, @unique_factorization_monoid.exists_prime_factors _ _ h,
  unique_factorization_monoid.of_exists_prime_factors⟩

section
variables {β : Type*} [cancel_comm_monoid_with_zero α] [cancel_comm_monoid_with_zero β]

lemma mul_equiv.unique_factorization_monoid (e : α ≃* β)
  (hα : unique_factorization_monoid α) : unique_factorization_monoid β :=
begin
  rw unique_factorization_monoid.iff_exists_prime_factors at hα ⊢, intros a ha,
  obtain ⟨w,hp,u,h⟩ := hα (e.symm a) (λ h, ha $ by { convert ← map_zero e, simp [← h] }),
  exact ⟨ w.map e,
    λ b hb, let ⟨c,hc,he⟩ := multiset.mem_map.1 hb in he ▸ e.prime_iff.1 (hp c hc),
    units.map e.to_monoid_hom u,
    by { erw [multiset.prod_hom, ← e.map_mul, h], simp } ⟩,
end

lemma mul_equiv.unique_factorization_monoid_iff (e : α ≃* β) :
  unique_factorization_monoid α ↔ unique_factorization_monoid β :=
⟨ e.unique_factorization_monoid, e.symm.unique_factorization_monoid ⟩

end

theorem irreducible_iff_prime_of_exists_unique_irreducible_factors [cancel_comm_monoid_with_zero α]
  (eif : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, irreducible b) ∧ f.prod ~ᵤ a)
  (uif : ∀ (f g : multiset α),
  (∀ x ∈ f, irreducible x) → (∀ x ∈ g, irreducible x) → f.prod ~ᵤ g.prod →
    multiset.rel associated f g)
  (p : α) : irreducible p ↔ prime p :=
⟨by letI := classical.dec_eq α; exact λ hpi,
    ⟨hpi.ne_zero, hpi.1,
      λ a b ⟨x, hx⟩,
      if hab0 : a * b = 0
      then (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim
        (λ ha0, by simp [ha0])
        (λ hb0, by simp [hb0])
      else
        have hx0 : x ≠ 0, from λ hx0, by simp * at *,
        have ha0 : a ≠ 0, from left_ne_zero_of_mul hab0,
        have hb0 : b ≠ 0, from right_ne_zero_of_mul hab0,
        begin
          cases eif x hx0 with fx hfx,
          cases eif a ha0 with fa hfa,
          cases eif b hb0 with fb hfb,
          have h : multiset.rel associated (p ::ₘ fx) (fa + fb),
          { apply uif,
            { exact λ i hi, (multiset.mem_cons.1 hi).elim (λ hip, hip.symm ▸ hpi) (hfx.1 _), },
            { exact λ i hi, (multiset.mem_add.1 hi).elim (hfa.1 _) (hfb.1 _), },
            calc multiset.prod (p ::ₘ fx)
                  ~ᵤ a * b : by rw [hx, multiset.prod_cons];
                    exact hfx.2.mul_left _
              ... ~ᵤ (fa).prod * (fb).prod :
                hfa.2.symm.mul_mul hfb.2.symm
              ... = _ : by rw multiset.prod_add, },
          exact let ⟨q, hqf, hq⟩ := multiset.exists_mem_of_rel_of_mem h
          (multiset.mem_cons_self p _) in
        (multiset.mem_add.1 hqf).elim
          (λ hqa, or.inl $ hq.dvd_iff_dvd_left.2 $
            hfa.2.dvd_iff_dvd_right.1
              (multiset.dvd_prod hqa))
          (λ hqb, or.inr $ hq.dvd_iff_dvd_left.2 $
            hfb.2.dvd_iff_dvd_right.1
              (multiset.dvd_prod hqb))
        end⟩, prime.irreducible⟩

theorem unique_factorization_monoid.of_exists_unique_irreducible_factors
  [cancel_comm_monoid_with_zero α]
  (eif : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, irreducible b) ∧ f.prod ~ᵤ a)
  (uif : ∀ (f g : multiset α),
  (∀ x ∈ f, irreducible x) → (∀ x ∈ g, irreducible x) → f.prod ~ᵤ g.prod →
    multiset.rel associated f g) :
  unique_factorization_monoid α :=
unique_factorization_monoid.of_exists_prime_factors (by
  { convert eif,
    simp_rw irreducible_iff_prime_of_exists_unique_irreducible_factors eif uif })

namespace unique_factorization_monoid
variables [cancel_comm_monoid_with_zero α] [decidable_eq α]
variables [unique_factorization_monoid α]
/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def factors (a : α) : multiset α := if h : a = 0 then 0 else
classical.some (unique_factorization_monoid.exists_prime_factors a h)

theorem factors_prod {a : α} (ane0 : a ≠ 0) : associated (factors a).prod a :=
begin
  rw [factors, dif_neg ane0],
  exact (classical.some_spec (exists_prime_factors a ane0)).2
end

lemma ne_zero_of_mem_factors {p a : α} (h : p ∈ factors a) : a ≠ 0 :=
begin
  intro ha,
  rw [factors, dif_pos ha] at h,
  exact multiset.not_mem_zero _ h
end

lemma dvd_of_mem_factors {p a : α} (h : p ∈ factors a) : p ∣ a :=
dvd_trans (multiset.dvd_prod h) (associated.dvd (factors_prod (ne_zero_of_mem_factors h)))

theorem prime_of_factor {a : α} (x : α) (hx : x ∈ factors a) : prime x :=
begin
  have ane0 := ne_zero_of_mem_factors hx,
  rw [factors, dif_neg ane0] at hx,
  exact (classical.some_spec (unique_factorization_monoid.exists_prime_factors a ane0)).1 x hx,
end

theorem irreducible_of_factor {a : α} : ∀ (x : α), x ∈ factors a → irreducible x :=
λ x h, (prime_of_factor x h).irreducible

@[simp] lemma factors_zero : factors (0 : α) = 0 :=
by simp [factors]

@[simp] lemma factors_one : factors (1 : α) = 0 :=
begin
  nontriviality α using [factors],
  rw ← multiset.rel_zero_right,
  refine factors_unique irreducible_of_factor (λ x hx, (multiset.not_mem_zero x hx).elim) _,
  rw multiset.prod_zero,
  exact factors_prod one_ne_zero,
end

lemma exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) : p ∣ a →
  ∃ q ∈ factors a, p ~ᵤ q :=
λ ⟨b, hb⟩,
have hb0 : b ≠ 0, from λ hb0, by simp * at *,
have multiset.rel associated (p ::ₘ factors b) (factors a),
  from factors_unique
    (λ x hx, (multiset.mem_cons.1 hx).elim (λ h, h.symm ▸ hp) (irreducible_of_factor _))
    irreducible_of_factor
    (associated.symm $ calc multiset.prod (factors a) ~ᵤ a : factors_prod ha0
      ... = p * b : hb
      ... ~ᵤ multiset.prod (p ::ₘ factors b) :
        by rw multiset.prod_cons; exact (factors_prod hb0).symm.mul_left _),
multiset.exists_mem_of_rel_of_mem this (by simp)

lemma exists_mem_factors {x : α} (hx : x ≠ 0) (h : ¬ is_unit x) : ∃ p, p ∈ factors x :=
begin
  obtain ⟨p', hp', hp'x⟩ := wf_dvd_monoid.exists_irreducible_factor h hx,
  obtain ⟨p, hp, hpx⟩ := exists_mem_factors_of_dvd hx hp' hp'x,
  exact ⟨p, hp⟩
end

lemma factors_mul {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  multiset.rel associated (factors (x * y)) (factors x + factors y) :=
begin
  refine factors_unique irreducible_of_factor
    (λ a ha, (multiset.mem_add.mp ha).by_cases (irreducible_of_factor _) (irreducible_of_factor _))
    ((factors_prod (mul_ne_zero hx hy)).trans _),
  rw multiset.prod_add,
  exact (associated.mul_mul (factors_prod hx) (factors_prod hy)).symm,
end

lemma factors_pow {x : α} (n : ℕ) :
  multiset.rel associated (factors (x ^ n)) (n • factors x) :=
begin
  induction n with n ih,
  { simp },
  by_cases h0 : x = 0,
  { simp [h0, zero_pow n.succ_pos, smul_zero] },
  rw [pow_succ, succ_nsmul],
  refine multiset.rel.trans _ (factors_mul h0 (pow_ne_zero n h0)) _,
  refine multiset.rel.add _ ih,
  exact multiset.rel_refl_of_refl_on (λ y hy, associated.refl _),
end

@[simp] lemma factors_pos (x : α) (hx : x ≠ 0) : 0 < factors x ↔ ¬ is_unit x :=
begin
  split,
  { intros h hx,
    obtain ⟨p, hp⟩ := multiset.exists_mem_of_ne_zero h.ne',
    exact (prime_of_factor _ hp).not_unit (is_unit_of_dvd_unit (dvd_of_mem_factors hp) hx) },
  { intros h,
    obtain ⟨p, hp⟩ := exists_mem_factors hx h,
    exact bot_lt_iff_ne_bot.mpr (mt multiset.eq_zero_iff_forall_not_mem.mp
      (not_forall.mpr ⟨p, not_not.mpr hp⟩)) },
end

end unique_factorization_monoid

namespace unique_factorization_monoid
variables [cancel_comm_monoid_with_zero α] [decidable_eq α] [normalization_monoid α]
variables [unique_factorization_monoid α]

/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def normalized_factors (a : α) : multiset α :=
multiset.map normalize $ factors a

/-- An arbitrary choice of factors of `x : M` is exactly the (unique) normalized set of factors,
if `M` has a trivial group of units. -/
@[simp] lemma factors_eq_normalized_factors {M : Type*} [cancel_comm_monoid_with_zero M]
  [decidable_eq M] [unique_factorization_monoid M] [unique (Mˣ)] (x : M) :
  factors x = normalized_factors x :=
begin
  unfold normalized_factors,
  convert (multiset.map_id (factors x)).symm,
  ext p,
  exact normalize_eq p
end

theorem normalized_factors_prod {a : α} (ane0 : a ≠ 0) : associated (normalized_factors a).prod a :=
begin
  rw [normalized_factors, factors, dif_neg ane0],
  refine associated.trans _ (classical.some_spec (exists_prime_factors a ane0)).2,
  rw [← associates.mk_eq_mk_iff_associated, ← associates.prod_mk, ← associates.prod_mk,
      multiset.map_map],
  congr' 2,
  ext,
  rw [function.comp_apply, associates.mk_normalize],
end

theorem prime_of_normalized_factor {a : α} : ∀ (x : α), x ∈ normalized_factors a → prime x :=
begin
  rw [normalized_factors, factors],
  split_ifs with ane0, { simp },
  intros x hx, rcases multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩,
  rw (normalize_associated _).prime_iff,
  exact (classical.some_spec (unique_factorization_monoid.exists_prime_factors a ane0)).1 y hy,
end

theorem irreducible_of_normalized_factor {a : α} :
  ∀ (x : α), x ∈ normalized_factors a → irreducible x :=
λ x h, (prime_of_normalized_factor x h).irreducible

theorem normalize_normalized_factor {a : α} :
  ∀ (x : α), x ∈ normalized_factors a → normalize x = x :=
begin
  rw [normalized_factors, factors],
  split_ifs with h, { simp },
  intros x hx,
  obtain ⟨y, hy, rfl⟩ := multiset.mem_map.1 hx,
  apply normalize_idem
end

lemma normalized_factors_irreducible {a : α} (ha : irreducible a) :
  normalized_factors a = {normalize a} :=
begin
  obtain ⟨p, a_assoc, hp⟩ := prime_factors_irreducible ha
    ⟨prime_of_normalized_factor, normalized_factors_prod ha.ne_zero⟩,
  have p_mem : p ∈ normalized_factors a,
  { rw hp, exact multiset.mem_singleton_self _ },
  convert hp,
  rwa [← normalize_normalized_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]
end

lemma normalized_factors_eq_of_dvd (a : α) : ∀ (p q ∈ normalized_factors a), p ∣ q → p = q :=
begin
  intros p hp q hq hdvd,
  convert normalize_eq_normalize hdvd
    (((prime_of_normalized_factor _ hp).irreducible).dvd_symm
      ((prime_of_normalized_factor _ hq).irreducible) hdvd);
    apply (normalize_normalized_factor _ _).symm; assumption
end

lemma exists_mem_normalized_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) : p ∣ a →
  ∃ q ∈ normalized_factors a, p ~ᵤ q :=
λ ⟨b, hb⟩,
have hb0 : b ≠ 0, from λ hb0, by simp * at *,
have multiset.rel associated (p ::ₘ normalized_factors b) (normalized_factors a),
  from factors_unique
    (λ x hx, (multiset.mem_cons.1 hx).elim (λ h, h.symm ▸ hp)
      (irreducible_of_normalized_factor _))
    irreducible_of_normalized_factor
    (associated.symm $ calc multiset.prod (normalized_factors a) ~ᵤ a : normalized_factors_prod ha0
      ... = p * b : hb
      ... ~ᵤ multiset.prod (p ::ₘ normalized_factors b) :
        by rw multiset.prod_cons; exact (normalized_factors_prod hb0).symm.mul_left _),
multiset.exists_mem_of_rel_of_mem this (by simp)

lemma exists_mem_normalized_factors {x : α} (hx : x ≠ 0) (h : ¬ is_unit x) :
  ∃ p, p ∈ normalized_factors x :=
begin
  obtain ⟨p', hp', hp'x⟩ := wf_dvd_monoid.exists_irreducible_factor h hx,
  obtain ⟨p, hp, hpx⟩ := exists_mem_normalized_factors_of_dvd hx hp' hp'x,
  exact ⟨p, hp⟩
end

@[simp] lemma normalized_factors_zero : normalized_factors (0 : α) = 0 :=
by simp [normalized_factors, factors]

@[simp] lemma normalized_factors_one : normalized_factors (1 : α) = 0 :=
begin
  nontriviality α using [normalized_factors, factors],
  rw ← multiset.rel_zero_right,
  apply factors_unique irreducible_of_normalized_factor,
  { intros x hx,
    exfalso,
    apply multiset.not_mem_zero x hx },
  { simp [normalized_factors_prod one_ne_zero] },
  apply_instance
end

@[simp] lemma normalized_factors_mul {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  normalized_factors (x * y) = normalized_factors x + normalized_factors y :=
begin
  have h : (normalize : α → α) = associates.out ∘ associates.mk,
  { ext, rw [function.comp_apply, associates.out_mk], },
  rw [← multiset.map_id' (normalized_factors (x * y)), ← multiset.map_id' (normalized_factors x),
    ← multiset.map_id' (normalized_factors y), ← multiset.map_congr rfl normalize_normalized_factor,
    ← multiset.map_congr rfl normalize_normalized_factor,
    ← multiset.map_congr rfl normalize_normalized_factor,
    ← multiset.map_add, h, ← multiset.map_map associates.out, eq_comm,
    ← multiset.map_map associates.out],
  refine congr rfl _,
  apply multiset.map_mk_eq_map_mk_of_rel,
  apply factors_unique,
  { intros x hx,
    rcases multiset.mem_add.1 hx with hx | hx;
    exact irreducible_of_normalized_factor x hx },
  { exact irreducible_of_normalized_factor },
  { rw multiset.prod_add,
    exact ((normalized_factors_prod hx).mul_mul (normalized_factors_prod hy)).trans
      (normalized_factors_prod (mul_ne_zero hx hy)).symm }
end

@[simp] lemma normalized_factors_pow {x : α} (n : ℕ) :
  normalized_factors (x ^ n) = n • normalized_factors x :=
begin
  induction n with n ih,
  { simp },
  by_cases h0 : x = 0,
  { simp [h0, zero_pow n.succ_pos, smul_zero] },
  rw [pow_succ, succ_nsmul, normalized_factors_mul h0 (pow_ne_zero _ h0), ih],
end

theorem _root_.irreducible.normalized_factors_pow {p : α} (hp : irreducible p) (k : ℕ) :
  normalized_factors (p ^ k) = multiset.replicate k (normalize p) :=
by rw [normalized_factors_pow, normalized_factors_irreducible hp, multiset.nsmul_singleton]

theorem normalized_factors_prod_eq (s : multiset α) (hs : ∀ a ∈ s, irreducible a) :
  normalized_factors s.prod = s.map normalize :=
begin
  induction s using multiset.induction with a s ih,
  { rw [multiset.prod_zero, normalized_factors_one, multiset.map_zero] },
  { have ia := hs a (multiset.mem_cons_self a _),
    have ib := λ b h, hs b (multiset.mem_cons_of_mem h),
    obtain rfl | ⟨b, hb⟩ := s.empty_or_exists_mem,
    { rw [multiset.cons_zero, multiset.prod_singleton,
          multiset.map_singleton, normalized_factors_irreducible ia] },
    haveI := nontrivial_of_ne b 0 (ib b hb).ne_zero,
    rw [multiset.prod_cons, multiset.map_cons, normalized_factors_mul ia.ne_zero,
      normalized_factors_irreducible ia, ih],
    exacts [rfl, ib, multiset.prod_ne_zero (λ h, (ib 0 h).ne_zero rfl)] },
end

lemma dvd_iff_normalized_factors_le_normalized_factors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  x ∣ y ↔ normalized_factors x ≤ normalized_factors y :=
begin
  split,
  { rintro ⟨c, rfl⟩,
    simp [hx, right_ne_zero_of_mul hy] },
  { rw [← (normalized_factors_prod hx).dvd_iff_dvd_left,
      ← (normalized_factors_prod hy).dvd_iff_dvd_right],
    apply multiset.prod_dvd_prod_of_le }
end

lemma associated_iff_normalized_factors_eq_normalized_factors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  x ~ᵤ y ↔ normalized_factors x = normalized_factors y :=
begin
  refine ⟨λ h, _,
    λ h, (normalized_factors_prod hx).symm.trans (trans (by rw h) (normalized_factors_prod hy))⟩,
  apply le_antisymm; rw [← dvd_iff_normalized_factors_le_normalized_factors],
  all_goals { simp [*, h.dvd, h.symm.dvd], },
end

theorem normalized_factors_of_irreducible_pow {p : α} (hp : irreducible p) (k : ℕ) :
  normalized_factors (p ^ k) = multiset.replicate k (normalize p) :=
by rw [normalized_factors_pow, normalized_factors_irreducible hp, multiset.nsmul_singleton]

lemma zero_not_mem_normalized_factors (x : α) : (0 : α) ∉ normalized_factors x :=
λ h, prime.ne_zero (prime_of_normalized_factor _ h) rfl

lemma dvd_of_mem_normalized_factors {a p : α} (H : p ∈ normalized_factors a) : p ∣ a :=
begin
  by_cases hcases : a = 0,
  { rw hcases,
    exact dvd_zero p },
  { exact dvd_trans (multiset.dvd_prod H) (associated.dvd (normalized_factors_prod hcases)) },
end

lemma exists_associated_prime_pow_of_unique_normalized_factor {p r : α}
  (h : ∀ {m}, m ∈ normalized_factors r → m = p) (hr : r ≠ 0) : ∃ (i : ℕ), associated (p ^ i) r :=
begin
  use (normalized_factors r).card,
  have := unique_factorization_monoid.normalized_factors_prod hr,
  rwa [multiset.eq_replicate_of_mem (λ b, h), multiset.prod_replicate] at this
end

lemma normalized_factors_prod_of_prime [nontrivial α] [unique αˣ] {m : multiset α}
  (h : ∀ p ∈ m, prime p) : (normalized_factors m.prod) = m :=
by simpa only [←multiset.rel_eq, ←associated_eq_eq] using prime_factors_unique
  (prime_of_normalized_factor) h (normalized_factors_prod (m.prod_ne_zero_of_prime h))

lemma mem_normalized_factors_eq_of_associated {a b c : α} (ha : a ∈ normalized_factors c)
  (hb : b ∈ normalized_factors c) (h : associated a b) : a = b :=
begin
  rw [← normalize_normalized_factor a ha, ← normalize_normalized_factor b hb,
    normalize_eq_normalize_iff],
  apply associated.dvd_dvd h,
end

@[simp] lemma normalized_factors_pos (x : α) (hx : x ≠ 0) :
  0 < normalized_factors x ↔ ¬ is_unit x :=
begin
  split,
  { intros h hx,
    obtain ⟨p, hp⟩ := multiset.exists_mem_of_ne_zero h.ne',
    exact (prime_of_normalized_factor _ hp).not_unit
      (is_unit_of_dvd_unit (dvd_of_mem_normalized_factors hp) hx) },
  { intros h,
    obtain ⟨p, hp⟩ := exists_mem_normalized_factors hx h,
    exact bot_lt_iff_ne_bot.mpr (mt multiset.eq_zero_iff_forall_not_mem.mp
      (not_forall.mpr ⟨p, not_not.mpr hp⟩)) },
end

lemma dvd_not_unit_iff_normalized_factors_lt_normalized_factors
  {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  dvd_not_unit x y ↔ normalized_factors x < normalized_factors y :=
begin
  split,
  { rintro ⟨_, c, hc, rfl⟩,
    simp only [hx, right_ne_zero_of_mul hy, normalized_factors_mul, ne.def, not_false_iff,
      lt_add_iff_pos_right, normalized_factors_pos, hc] },
  { intro h,
    exact dvd_not_unit_of_dvd_of_not_dvd
      ((dvd_iff_normalized_factors_le_normalized_factors hx hy).mpr h.le)
      (mt (dvd_iff_normalized_factors_le_normalized_factors hy hx).mp h.not_le) }
end

end unique_factorization_monoid

namespace unique_factorization_monoid

open_locale classical
open multiset associates
noncomputable theory

variables [cancel_comm_monoid_with_zero α] [nontrivial α] [unique_factorization_monoid α]

/-- Noncomputably defines a `normalization_monoid` structure on a `unique_factorization_monoid`. -/
protected def normalization_monoid : normalization_monoid α :=
normalization_monoid_of_monoid_hom_right_inverse
{ to_fun := λ a : associates α, if a = 0 then 0 else ((normalized_factors a).map
    (classical.some mk_surjective.has_right_inverse : associates α → α)).prod,
  map_one' := by simp,
  map_mul' := λ x y, by
  { by_cases hx : x = 0, { simp [hx] },
    by_cases hy : y = 0, { simp [hy] },
    simp [hx, hy] } } begin
  intro x,
  dsimp,
  by_cases hx : x = 0, { simp [hx] },
  have h : associates.mk_monoid_hom ∘ (classical.some mk_surjective.has_right_inverse) =
           (id : associates α → associates α),
  { ext x,
    rw [function.comp_apply, mk_monoid_hom_apply,
      classical.some_spec mk_surjective.has_right_inverse x],
    refl },
  rw [if_neg hx, ← mk_monoid_hom_apply, monoid_hom.map_multiset_prod, map_map, h, map_id,
      ← associated_iff_eq],
  apply normalized_factors_prod hx
end

instance : inhabited (normalization_monoid α) := ⟨unique_factorization_monoid.normalization_monoid⟩

end unique_factorization_monoid

namespace unique_factorization_monoid

variables {R : Type*} [cancel_comm_monoid_with_zero R] [unique_factorization_monoid R]

lemma no_factors_of_no_prime_factors {a b : R} (ha : a ≠ 0)
  (h : (∀ {d}, d ∣ a → d ∣ b → ¬ prime d)) : ∀ {d}, d ∣ a → d ∣ b → is_unit d :=
λ d, induction_on_prime d
  (by { simp only [zero_dvd_iff], intros, contradiction })
  (λ x hx _ _, hx)
  (λ d q hp hq ih dvd_a dvd_b,
    absurd hq (h (dvd_of_mul_right_dvd dvd_a) (dvd_of_mul_right_dvd dvd_b)))

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `is_coprime.dvd_of_dvd_mul_left`. -/
lemma dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0) :
  (∀ {d}, d ∣ a → d ∣ c → ¬ prime d) → a ∣ b * c → a ∣ b :=
begin
  refine induction_on_prime c _ _ _,
  { intro no_factors,
    simp only [dvd_zero, mul_zero, forall_prop_of_true],
    haveI := classical.prop_decidable,
    exact is_unit_iff_forall_dvd.mp
      (no_factors_of_no_prime_factors ha @no_factors (dvd_refl a) (dvd_zero a)) _ },
  { rintros _ ⟨x, rfl⟩ _ a_dvd_bx,
    apply units.dvd_mul_right.mp a_dvd_bx },
  { intros c p hc hp ih no_factors a_dvd_bpc,
    apply ih (λ q dvd_a dvd_c hq, no_factors dvd_a (dvd_c.mul_left _) hq),
    rw mul_left_comm at a_dvd_bpc,
    refine or.resolve_left (hp.left_dvd_or_dvd_right_of_dvd_mul a_dvd_bpc) (λ h, _),
    exact no_factors h (dvd_mul_right p c) hp }
end

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `is_coprime.dvd_of_dvd_mul_right`. -/
lemma dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
  (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬ prime d) : a ∣ b * c → a ∣ c :=
by simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
lemma exists_reduced_factors : ∀ (a ≠ (0 : R)) b,
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
begin
  haveI := classical.prop_decidable,
  intros a,
  refine induction_on_prime a _ _ _,
  { intros, contradiction },
  { intros a a_unit a_ne_zero b,
    use [a, b, 1],
    split,
    { intros p p_dvd_a _,
      exact is_unit_of_dvd_unit p_dvd_a a_unit },
    { simp } },
  { intros a p a_ne_zero p_prime ih_a pa_ne_zero b,
    by_cases p ∣ b,
    { rcases h with ⟨b, rfl⟩,
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b,
      refine ⟨a', b', p * c', @no_factor, _, _⟩,
      { rw [mul_assoc, ha'] },
      { rw [mul_assoc, hb'] } },
    { obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b,
      refine ⟨p * a', b', c', _, mul_left_comm _ _ _, rfl⟩,
      intros q q_dvd_pa' q_dvd_b',
      cases p_prime.left_dvd_or_dvd_right_of_dvd_mul q_dvd_pa' with p_dvd_q q_dvd_a',
      { have : p ∣ c' * b' := dvd_mul_of_dvd_right (p_dvd_q.trans q_dvd_b') _,
        contradiction },
      exact coprime q_dvd_a' q_dvd_b' } }
end

lemma exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
in ⟨a', b', c', λ _ hpb hpa, no_factor hpa hpb, ha, hb⟩

lemma pow_right_injective {a : R} (ha0 : a ≠ 0) (ha1 : ¬ is_unit a) :
  function.injective ((^) a : ℕ → R) :=
begin
  letI := classical.dec_eq R,
  intros i j hij,
  letI : nontrivial R := ⟨⟨a, 0, ha0⟩⟩,
  letI : normalization_monoid R := unique_factorization_monoid.normalization_monoid,
  obtain ⟨p', hp', dvd'⟩ := wf_dvd_monoid.exists_irreducible_factor ha1 ha0,
  obtain ⟨p, mem, _⟩ := exists_mem_normalized_factors_of_dvd ha0 hp' dvd',
  have := congr_arg (λ x, multiset.count p (normalized_factors x)) hij,
  simp only [normalized_factors_pow, multiset.count_nsmul] at this,
  exact mul_right_cancel₀ (multiset.count_ne_zero.mpr mem) this
end

lemma pow_eq_pow_iff {a : R} (ha0 : a ≠ 0) (ha1 : ¬ is_unit a) {i j : ℕ} :
  a ^ i = a ^ j ↔ i = j :=
(pow_right_injective ha0 ha1).eq_iff

section multiplicity
variables [nontrivial R] [normalization_monoid R]
variables [dec_dvd : decidable_rel (has_dvd.dvd : R → R → Prop)]
open multiplicity multiset

include dec_dvd
lemma le_multiplicity_iff_replicate_le_normalized_factors [decidable_eq R] {a b : R} {n : ℕ}
  (ha : irreducible a) (hb : b ≠ 0) :
  ↑n ≤ multiplicity a b ↔ replicate n (normalize a) ≤ normalized_factors b :=
begin
  rw ← pow_dvd_iff_le_multiplicity,
  revert b,
  induction n with n ih, { simp },
  intros b hb,
  split,
  { rintro ⟨c, rfl⟩,
    rw [ne.def, pow_succ, mul_assoc, mul_eq_zero, decidable.not_or_iff_and_not] at hb,
    rw [pow_succ, mul_assoc, normalized_factors_mul hb.1 hb.2, replicate_succ,
      normalized_factors_irreducible ha, singleton_add, cons_le_cons_iff, ← ih hb.2],
    apply dvd.intro _ rfl },
  { rw [multiset.le_iff_exists_add],
    rintro ⟨u, hu⟩,
    rw [← (normalized_factors_prod hb).dvd_iff_dvd_right, hu, prod_add, prod_replicate],
    exact (associated.pow_pow $ associated_normalize a).dvd.trans (dvd.intro u.prod rfl) }
end

/-- The multiplicity of an irreducible factor of a nonzero element is exactly the number of times
the normalized factor occurs in the `normalized_factors`.

See also `count_normalized_factors_eq` which expands the definition of `multiplicity`
to produce a specification for `count (normalized_factors _) _`..
-/
lemma multiplicity_eq_count_normalized_factors [decidable_eq R] {a b : R} (ha : irreducible a)
 (hb : b ≠ 0) : multiplicity a b = (normalized_factors b).count (normalize a) :=
begin
  apply le_antisymm,
  { apply part_enat.le_of_lt_add_one,
    rw [← nat.cast_one, ← nat.cast_add, lt_iff_not_ge, ge_iff_le,
      le_multiplicity_iff_replicate_le_normalized_factors ha hb, ← le_count_iff_replicate_le],
    simp },
  rw [le_multiplicity_iff_replicate_le_normalized_factors ha hb, ← le_count_iff_replicate_le],
end

omit dec_dvd

/-- The number of times an irreducible factor `p` appears in `normalized_factors x` is defined by
the number of times it divides `x`.

See also `multiplicity_eq_count_normalized_factors` if `n` is given by `multiplicity p x`.
-/
lemma count_normalized_factors_eq [decidable_eq R] {p x : R} (hp : irreducible p)
  (hnorm : normalize p = p) {n : ℕ} (hle : p^n ∣ x) (hlt : ¬ (p^(n+1) ∣ x)) :
  (normalized_factors x).count p = n :=
begin
  letI : decidable_rel ((∣) : R → R → Prop) := λ _ _, classical.prop_decidable _,
  by_cases hx0 : x = 0,
  { simp [hx0] at hlt, contradiction },
  rw [← part_enat.coe_inj],
  convert (multiplicity_eq_count_normalized_factors hp hx0).symm,
  { exact hnorm.symm },
  exact (multiplicity.eq_coe_iff.mpr ⟨hle, hlt⟩).symm
end

/-- The number of times an irreducible factor `p` appears in `normalized_factors x` is defined by
the number of times it divides `x`. This is a slightly more general version of
`unique_factorization_monoid.count_normalized_factors_eq` that allows `p = 0`.

See also `multiplicity_eq_count_normalized_factors` if `n` is given by `multiplicity p x`.
-/
lemma count_normalized_factors_eq' [decidable_eq R] {p x : R} (hp : p = 0 ∨ irreducible p)
  (hnorm : normalize p = p) {n : ℕ} (hle : p^n ∣ x) (hlt : ¬ (p^(n+1) ∣ x)) :
  (normalized_factors x).count p = n :=
begin
  rcases hp with rfl|hp,
  { cases n,
    { exact count_eq_zero.2 (zero_not_mem_normalized_factors _) },
    { rw [zero_pow (nat.succ_pos _)] at hle hlt,
      exact absurd hle hlt } },
  { exact count_normalized_factors_eq hp hnorm hle hlt }
end

lemma max_power_factor {a₀ : R} {x : R} (h : a₀ ≠ 0) (hx : irreducible x) :
  ∃ n : ℕ, ∃ a : R, ¬ x ∣ a ∧ a₀ = x ^ n * a :=
begin
  classical,
  let n := (normalized_factors a₀).count (normalize x),
  obtain ⟨a, ha1, ha2⟩ := (@exists_eq_pow_mul_and_not_dvd R _ _ x a₀
    (ne_top_iff_finite.mp (part_enat.ne_top_iff.mpr _))),
  simp_rw [← (multiplicity_eq_count_normalized_factors hx h).symm] at ha1,
  use [n, a, ha2, ha1],
  use [n, (multiplicity_eq_count_normalized_factors hx h)],
end

end multiplicity

section multiplicative

variables [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
variables {β : Type*} [cancel_comm_monoid_with_zero β]

open_locale big_operators

lemma prime_pow_coprime_prod_of_coprime_insert [decidable_eq α] {s : finset α} (i : α → ℕ) (p : α)
  (hps : p ∉ s) (is_prime : ∀ q ∈ insert p s, prime q)
  (is_coprime : ∀ (q q' ∈ insert p s), q ∣ q' → q = q') :
  ∀ (q : α), q ∣ p ^ i p → q ∣ ∏ p' in s, p' ^ i p' → is_unit q :=
begin
  have hp := is_prime _ (finset.mem_insert_self _ _),
  refine λ _, no_factors_of_no_prime_factors (pow_ne_zero _ hp.ne_zero) _,
  intros d hdp hdprod hd,
  apply hps,
  replace hdp := hd.dvd_of_dvd_pow hdp,
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod,
  obtain ⟨q, q_mem, rfl⟩ := multiset.mem_map.mp q_mem',
  replace hdq := hd.dvd_of_dvd_pow hdq,
  have : p ∣ q := dvd_trans
    (hd.irreducible.dvd_symm hp.irreducible hdp)
    hdq,
  convert q_mem,
  exact is_coprime _  (finset.mem_insert_self p s) _ (finset.mem_insert_of_mem q_mem) this,
end

/-- If `P` holds for units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on a product of powers of distinct primes. -/
@[elab_as_eliminator]
theorem induction_on_prime_power
  {P : α → Prop} (s : finset α) (i : α → ℕ)
  (is_prime : ∀ p ∈ s, prime p) (is_coprime : ∀ p q ∈ s, p ∣ q → p = q)
  (h1 : ∀ {x}, is_unit x → P x) (hpr : ∀ {p} (i : ℕ), prime p → P (p ^ i))
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → P x → P y → P (x * y)) :
  P (∏ p in s, p ^ (i p)) :=
begin
  letI := classical.dec_eq α,
  induction s using finset.induction_on with p f' hpf' ih,
  { simpa using h1 is_unit_one },
  rw finset.prod_insert hpf',
  exact hcp
    (prime_pow_coprime_prod_of_coprime_insert i p hpf' is_prime is_coprime)
    (hpr (i p) (is_prime _ (finset.mem_insert_self _ _)))
    (ih (λ q hq, is_prime _ (finset.mem_insert_of_mem hq))
    (λ q hq q' hq', is_coprime _ (finset.mem_insert_of_mem hq) _ (finset.mem_insert_of_mem hq')))
end

/-- If `P` holds for `0`, units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on all `a : α`. -/
@[elab_as_eliminator]
theorem induction_on_coprime
  {P : α → Prop} (a : α) (h0 : P 0) (h1 : ∀ {x}, is_unit x → P x)
  (hpr : ∀ {p} (i : ℕ), prime p → P (p ^ i))
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → P x → P y → P (x * y)) :
  P a :=
begin
  letI := classical.dec_eq α,
  have P_of_associated : ∀ {x y}, associated x y → P x → P y,
  { rintros x y ⟨u, rfl⟩ hx,
    exact hcp (λ p _ hpx, is_unit_of_dvd_unit hpx u.is_unit) hx (h1 u.is_unit) },
  by_cases ha0 : a = 0, { rwa ha0 },
  haveI : nontrivial α := ⟨⟨_, _, ha0⟩⟩,
  letI : normalization_monoid α := unique_factorization_monoid.normalization_monoid,
  refine P_of_associated (normalized_factors_prod ha0) _,
  rw [← (normalized_factors a).map_id, finset.prod_multiset_map_count],
  refine induction_on_prime_power _ _ _ _ @h1 @hpr @hcp;
    simp only [multiset.mem_to_finset],
  { apply prime_of_normalized_factor },
  { apply normalized_factors_eq_of_dvd },
end

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative on all products of primes. -/
@[elab_as_eliminator]
theorem multiplicative_prime_power
  {f : α → β} (s : finset α) (i j : α → ℕ)
  (is_prime : ∀ p ∈ s, prime p) (is_coprime : ∀ p q ∈ s, p ∣ q → p = q)
  (h1 : ∀ {x y}, is_unit y → f (x * y) = f x * f y)
  (hpr : ∀ {p} (i : ℕ), prime p → f (p ^ i) = (f p) ^ i)
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → f (x * y) = f x * f y) :
  f (∏ p in s, p ^ (i p + j p)) = f (∏ p in s, p ^ i p) * f (∏ p in s, p ^ j p) :=
begin
  letI := classical.dec_eq α,
  induction s using finset.induction_on with p s hps ih,
  { simpa using h1 is_unit_one },
  have hpr_p := is_prime _ (finset.mem_insert_self _ _),
  have hpr_s : ∀ p ∈ s, prime p := λ p hp, is_prime _ (finset.mem_insert_of_mem hp),
  have hcp_p := λ i, (prime_pow_coprime_prod_of_coprime_insert i p hps is_prime is_coprime),
  have hcp_s : ∀ (p q ∈ s), p ∣ q → p = q := λ p hp q hq, is_coprime p
    (finset.mem_insert_of_mem hp) q
    (finset.mem_insert_of_mem hq),
  rw [finset.prod_insert hps, finset.prod_insert hps, finset.prod_insert hps,
      hcp (hcp_p _), hpr _ hpr_p, hcp (hcp_p _), hpr _ hpr_p, hcp (hcp_p _), hpr _ hpr_p,
      ih hpr_s hcp_s,
      pow_add, mul_assoc, mul_left_comm (f p ^ j p), mul_assoc],
end

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative everywhere. -/
theorem multiplicative_of_coprime
  (f : α → β) (a b : α) (h0 : f 0 = 0) (h1 : ∀ {x y}, is_unit y → f (x * y) = f x * f y)
  (hpr : ∀ {p} (i : ℕ), prime p → f (p ^ i) = (f p) ^ i)
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → f (x * y) = f x * f y) :
  f (a * b) = f a * f b :=
begin
  letI := classical.dec_eq α,
  by_cases ha0 : a = 0, { rw [ha0, zero_mul, h0, zero_mul] },
  by_cases hb0 : b = 0, { rw [hb0, mul_zero, h0, mul_zero] },
  by_cases hf1 : f 1 = 0,
  { calc f (a * b) = f ((a * b) * 1) : by rw mul_one
               ... = 0 : by simp only [h1 is_unit_one, hf1, mul_zero]
               ... = f a * f (b * 1) : by simp only [h1 is_unit_one, hf1, mul_zero]
               ... = f a * f b : by rw mul_one },
  have h1' : f 1 = 1 := (mul_left_inj' hf1).mp (by rw [← h1 is_unit_one, one_mul, one_mul]),
  haveI : nontrivial α := ⟨⟨_, _, ha0⟩⟩,
  letI : normalization_monoid α := unique_factorization_monoid.normalization_monoid,
  suffices : f (∏ p in (normalized_factors a).to_finset ∪ (normalized_factors b).to_finset,
        p ^ ((normalized_factors a).count p + (normalized_factors b).count p))
    = f (∏ p in (normalized_factors a).to_finset ∪ (normalized_factors b).to_finset,
        p ^ (normalized_factors a).count p) *
      f (∏ (p : α) in (normalized_factors a).to_finset ∪ (normalized_factors b).to_finset,
        p ^ (normalized_factors b).count p),
  { obtain ⟨ua, a_eq⟩ := normalized_factors_prod ha0,
    obtain ⟨ub, b_eq⟩ := normalized_factors_prod hb0,
    rw [← a_eq, ← b_eq, mul_right_comm _ ↑ua, h1 ua.is_unit, h1 ub.is_unit, h1 ua.is_unit,
        ← mul_assoc, h1 ub.is_unit, mul_right_comm _ (f ua), ← mul_assoc],
    congr,
    rw [← (normalized_factors a).map_id, ← (normalized_factors b).map_id,
        finset.prod_multiset_map_count, finset.prod_multiset_map_count,
        finset.prod_subset (finset.subset_union_left _ (normalized_factors b).to_finset),
        finset.prod_subset (finset.subset_union_right _ (normalized_factors b).to_finset),
        ← finset.prod_mul_distrib],
    simp_rw [id.def, ← pow_add, this],
    all_goals { simp only [multiset.mem_to_finset] },
    { intros p hpab hpb, simp [hpb] },
    { intros p hpab hpa, simp [hpa] } },
  refine multiplicative_prime_power _ _ _ _ _ @h1 @hpr @hcp,
  all_goals { simp only [multiset.mem_to_finset, finset.mem_union] },
  { rintros p (hpa | hpb); apply prime_of_normalized_factor; assumption },
  { rintro p (hp | hp) q (hq | hq) hdvd;
      rw [← normalize_normalized_factor _ hp, ← normalize_normalized_factor _ hq];
      exact normalize_eq_normalize hdvd
        ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
          (prime_of_normalized_factor _ hq).irreducible
          hdvd) },
end

end multiplicative

end unique_factorization_monoid

namespace associates
open unique_factorization_monoid associated multiset
variables [cancel_comm_monoid_with_zero α]

/-- `factor_set α` representation elements of unique factorization domain as multisets.
`multiset α` produced by `normalized_factors` are only unique up to associated elements, while the
multisets in `factor_set α` are unique by equality and restricted to irreducible elements. This
gives us a representation of each element as a unique multisets (or the added ⊤ for 0), which has a
complete lattice struture. Infimum is the greatest common divisor and supremum is the least common
multiple.
-/
@[reducible] def {u} factor_set (α : Type u) [cancel_comm_monoid_with_zero α] :
  Type u :=
with_top (multiset { a : associates α // irreducible a })

local attribute [instance] associated.setoid

theorem factor_set.coe_add {a b : multiset { a : associates α // irreducible a }} :
  (↑(a + b) : factor_set α) = a + b :=
by norm_cast

lemma factor_set.sup_add_inf_eq_add [decidable_eq (associates α)] :
  ∀(a b : factor_set α), a ⊔ b + a ⊓ b = a + b
| none     b        := show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b, by simp
| a        none     := show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤, by simp
| (some a) (some b) := show (a : factor_set α) ⊔ b + a ⊓ b = a + b, from
  begin
    rw [← with_top.coe_sup, ← with_top.coe_inf, ← with_top.coe_add, ← with_top.coe_add,
      with_top.coe_eq_coe],
    exact multiset.union_add_inter _ _
  end

/-- Evaluates the product of a `factor_set` to be the product of the corresponding multiset,
  or `0` if there is none. -/
def factor_set.prod : factor_set α → associates α
| none     := 0
| (some s) := (s.map coe).prod

@[simp] theorem prod_top : (⊤ : factor_set α).prod = 0 := rfl

@[simp] theorem prod_coe {s : multiset { a : associates α // irreducible a }} :
  (s : factor_set α).prod = (s.map coe).prod :=
rfl

@[simp] theorem prod_add : ∀(a b : factor_set α), (a + b).prod = a.prod * b.prod
| none b    := show (⊤ + b).prod = (⊤:factor_set α).prod * b.prod, by simp
| a    none := show (a + ⊤).prod = a.prod * (⊤:factor_set α).prod, by simp
| (some a) (some b) :=
  show (↑a + ↑b:factor_set α).prod = (↑a:factor_set α).prod * (↑b:factor_set α).prod,
    by rw [← factor_set.coe_add, prod_coe, prod_coe, prod_coe, multiset.map_add, multiset.prod_add]

theorem prod_mono : ∀{a b : factor_set α}, a ≤ b → a.prod ≤ b.prod
| none b h := have b = ⊤, from top_unique h, by rw [this, prod_top]; exact le_rfl
| a none h := show a.prod ≤ (⊤ : factor_set α).prod, by simp; exact le_top
| (some a) (some b) h := prod_le_prod $ multiset.map_le_map $ with_top.coe_le_coe.1 $ h

theorem factor_set.prod_eq_zero_iff [nontrivial α] (p : factor_set α) :
  p.prod = 0 ↔ p = ⊤ :=
begin
  induction p using with_top.rec_top_coe,
  { simp only [iff_self, eq_self_iff_true, associates.prod_top] },
  simp only [prod_coe, with_top.coe_ne_top, iff_false, prod_eq_zero_iff, multiset.mem_map],
  rintro ⟨⟨a, ha⟩, -, eq⟩,
  rw [subtype.coe_mk] at eq,
  exact ha.ne_zero eq,
end

/-- `bcount p s` is the multiplicity of `p` in the factor_set `s` (with bundled `p`)-/
def bcount [decidable_eq (associates α)] (p : {a : associates α // irreducible a}) :
  factor_set α → ℕ
| none := 0
| (some s) := s.count p

variables [dec_irr : Π (p : associates α), decidable (irreducible p)]
include dec_irr

/-- `count p s` is the multiplicity of the irreducible `p` in the factor_set `s`.

If `p` is not irreducible, `count p s` is defined to be `0`. -/
def count [decidable_eq (associates α)] (p : associates α) :
  factor_set α → ℕ :=
if hp : irreducible p then bcount ⟨p, hp⟩  else 0

@[simp] lemma count_some [decidable_eq (associates α)] {p : associates α} (hp : irreducible p)
  (s : multiset _) : count p (some s) = s.count ⟨p, hp⟩:=
by { dunfold count, split_ifs, refl }

@[simp] lemma count_zero [decidable_eq (associates α)] {p : associates α} (hp : irreducible p) :
  count p (0 : factor_set α) = 0 :=
by { dunfold count, split_ifs, refl }

lemma count_reducible [decidable_eq (associates α)] {p : associates α} (hp : ¬ irreducible p) :
  count p = 0 := dif_neg hp

omit dec_irr

/-- membership in a factor_set (bundled version) -/
def bfactor_set_mem : {a : associates α // irreducible a} → (factor_set α) → Prop
| _ ⊤ := true
| p (some l) := p ∈ l

include dec_irr

/-- `factor_set_mem p s` is the predicate that the irreducible `p` is a member of
`s : factor_set α`.

If `p` is not irreducible, `p` is not a member of any `factor_set`. -/
def factor_set_mem (p : associates α) (s : factor_set α) : Prop :=
if hp : irreducible p then bfactor_set_mem ⟨p, hp⟩ s else false

instance : has_mem (associates α) (factor_set α) := ⟨factor_set_mem⟩

@[simp] lemma factor_set_mem_eq_mem (p : associates α) (s : factor_set α) :
  factor_set_mem p s = (p ∈ s) := rfl

lemma mem_factor_set_top {p : associates α} {hp : irreducible p} :
  p ∈ (⊤ : factor_set α) :=
begin
  dunfold has_mem.mem, dunfold factor_set_mem, split_ifs, exact trivial
end

lemma mem_factor_set_some {p : associates α} {hp : irreducible p}
   {l : multiset {a : associates α // irreducible a }} :
  p ∈ (l : factor_set α) ↔ subtype.mk p hp ∈ l :=
begin
  dunfold has_mem.mem, dunfold factor_set_mem, split_ifs, refl
end

lemma reducible_not_mem_factor_set {p : associates α} (hp : ¬ irreducible p)
  (s : factor_set α) : ¬ p ∈ s :=
λ (h : if hp : irreducible p then bfactor_set_mem ⟨p, hp⟩ s else false),
  by rwa [dif_neg hp] at h

omit dec_irr

variable [unique_factorization_monoid α]

theorem unique' {p q : multiset (associates α)} :
  (∀a∈p, irreducible a) → (∀a∈q, irreducible a) → p.prod = q.prod → p = q :=
begin
  apply multiset.induction_on_multiset_quot p,
  apply multiset.induction_on_multiset_quot q,
  assume s t hs ht eq,
  refine multiset.map_mk_eq_map_mk_of_rel (unique_factorization_monoid.factors_unique _ _ _),
  { exact assume a ha, ((irreducible_mk _).1 $ hs _ $ multiset.mem_map_of_mem _ ha) },
  { exact assume a ha, ((irreducible_mk _).1 $ ht _ $ multiset.mem_map_of_mem _ ha) },
  simpa [quot_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated] using eq
end

theorem factor_set.unique [nontrivial α] {p q : factor_set α} (h : p.prod = q.prod) : p = q :=
begin
  induction p using with_top.rec_top_coe;
  induction q using with_top.rec_top_coe,
  { refl },
  { rw [eq_comm, ←factor_set.prod_eq_zero_iff, ←h, associates.prod_top] },
  { rw [←factor_set.prod_eq_zero_iff, h, associates.prod_top] },
  { congr' 1,
    rw  ←multiset.map_eq_map subtype.coe_injective,
    apply unique' _ _ h;
    { intros a ha,
      obtain ⟨⟨a', irred⟩, -, rfl⟩ := multiset.mem_map.mp ha,
      rwa [subtype.coe_mk] } },
end

theorem prod_le_prod_iff_le [nontrivial α] {p q : multiset (associates α)}
  (hp : ∀a∈p, irreducible a) (hq : ∀a∈q, irreducible a) :
  p.prod ≤ q.prod ↔ p ≤ q :=
iff.intro
  begin
    classical,
    rintros ⟨c, eqc⟩,
    refine multiset.le_iff_exists_add.2 ⟨factors c, unique' hq (λ x hx, _) _⟩,
    { obtain h|h := multiset.mem_add.1 hx,
      { exact hp x h },
      { exact irreducible_of_factor _ h } },
    { rw [eqc, multiset.prod_add],
      congr,
      refine associated_iff_eq.mp (factors_prod (λ hc, _)).symm,
      refine not_irreducible_zero (hq _ _),
      rw [←prod_eq_zero_iff, eqc, hc, mul_zero] }
  end
  prod_le_prod

variables [dec : decidable_eq α] [dec' : decidable_eq (associates α)]
include dec

/-- This returns the multiset of irreducible factors as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/
noncomputable def factors' (a : α) :
  multiset { a : associates α // irreducible a } :=
(factors a).pmap (λa ha, ⟨associates.mk a, (irreducible_mk _).2 ha⟩)
  (irreducible_of_factor)

@[simp] theorem map_subtype_coe_factors' {a : α} :
  (factors' a).map coe = (factors a).map associates.mk :=
by simp [factors', multiset.map_pmap, multiset.pmap_eq_map]

theorem factors'_cong {a b : α} (h : a ~ᵤ b) :
  factors' a = factors' b :=
begin
  obtain rfl|hb := eq_or_ne b 0,
  { rw associated_zero_iff_eq_zero at h, rw h },
  have ha : a ≠ 0,
  { contrapose! hb with ha,
    rw [←associated_zero_iff_eq_zero, ←ha],
    exact h.symm },
  rw [←multiset.map_eq_map subtype.coe_injective, map_subtype_coe_factors',
    map_subtype_coe_factors', ←rel_associated_iff_map_eq_map],
  exact factors_unique irreducible_of_factor irreducible_of_factor
    ((factors_prod ha).trans $ h.trans $ (factors_prod hb).symm),
end

include dec'

/-- This returns the multiset of irreducible factors of an associate as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/
noncomputable def factors (a : associates α) :
  factor_set α :=
begin
  refine (if h : a = 0 then ⊤ else
    quotient.hrec_on a (λx h, some $ factors' x) _ h),
  assume a b hab,
  apply function.hfunext,
  { have : a ~ᵤ 0 ↔ b ~ᵤ 0, from
      iff.intro (assume ha0, hab.symm.trans ha0) (assume hb0, hab.trans hb0),
    simp only [associated_zero_iff_eq_zero] at this,
    simp only [quotient_mk_eq_mk, this, mk_eq_zero] },
  exact (assume ha hb eq, heq_of_eq $ congr_arg some $ factors'_cong hab)
end

@[simp] theorem factors_0 : (0 : associates α).factors = ⊤ :=
dif_pos rfl

@[simp] theorem factors_mk (a : α) (h : a ≠ 0) :
  (associates.mk a).factors = factors' a :=
by { classical, apply dif_neg, apply (mt mk_eq_zero.1 h) }

@[simp]
theorem factors_prod (a : associates α) : a.factors.prod = a :=
quotient.induction_on a $ assume a, decidable.by_cases
  (assume : associates.mk a = 0, by simp [quotient_mk_eq_mk, this])
  (assume : associates.mk a ≠ 0,
    have a ≠ 0, by simp * at *,
    by simp [this, quotient_mk_eq_mk, prod_mk,
      mk_eq_mk_iff_associated.2 (factors_prod this)])

theorem prod_factors [nontrivial α] (s : factor_set α) : s.prod.factors = s :=
factor_set.unique $ factors_prod _

@[nontriviality] lemma factors_subsingleton [subsingleton α] {a : associates α} :
  a.factors = option.none :=
by { convert factors_0; apply_instance }

lemma factors_eq_none_iff_zero {a : associates α} :
  a.factors = option.none ↔ a = 0 :=
begin
  nontriviality α,
  exact ⟨λ h, by rwa [← factors_prod a, factor_set.prod_eq_zero_iff], λ h, h.symm ▸ factors_0⟩
end

lemma factors_eq_some_iff_ne_zero {a : associates α} :
  (∃ (s : multiset {p : associates α // irreducible p}), a.factors = some s) ↔ a ≠ 0 :=
by rw [← option.is_some_iff_exists, ← option.ne_none_iff_is_some, ne.def, ne.def,
  factors_eq_none_iff_zero]

theorem eq_of_factors_eq_factors {a b : associates α} (h : a.factors = b.factors) : a = b :=
have a.factors.prod = b.factors.prod, by rw h,
by rwa [factors_prod, factors_prod] at this

omit dec dec'

theorem eq_of_prod_eq_prod [nontrivial α] {a b : factor_set α} (h : a.prod = b.prod) : a = b :=
begin
  classical,
  have : a.prod.factors = b.prod.factors, by rw h,
  rwa [prod_factors, prod_factors] at this
end

include dec dec' dec_irr

theorem eq_factors_of_eq_counts {a b : associates α} (ha : a ≠ 0) (hb : b ≠ 0)
  (h : ∀ (p : associates α) (hp : irreducible p), p.count a.factors = p.count b.factors) :
  a.factors = b.factors :=
begin
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha,
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb,
  rw [h_sa, h_sb] at h ⊢,
  rw option.some_inj,
  have h_count : ∀ (p : associates α) (hp : irreducible p), sa.count ⟨p, hp⟩ = sb.count ⟨p, hp⟩,
  { intros p hp, rw [← count_some, ← count_some, h p hp] },
  apply multiset.to_finsupp.injective,
  ext ⟨p, hp⟩,
  rw [multiset.to_finsupp_apply, multiset.to_finsupp_apply, h_count p hp]
end

theorem eq_of_eq_counts {a b : associates α} (ha : a ≠ 0) (hb  : b ≠ 0)
  (h : ∀ (p : associates α), irreducible p → p.count a.factors = p.count b.factors) : a = b :=
eq_of_factors_eq_factors (eq_factors_of_eq_counts ha hb h)

lemma count_le_count_of_factors_le {a b p : associates α} (hb : b ≠ 0)
  (hp : irreducible p) (h : a.factors ≤ b.factors) : p.count a.factors ≤ p.count b.factors :=
begin
  by_cases ha : a = 0,
  { simp [*] at *, },
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha,
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb,
  rw [h_sa, h_sb] at h ⊢,
  rw [count_some hp, count_some hp], rw with_top.some_le_some at h,
  exact multiset.count_le_of_le _ h
end

omit dec_irr

@[simp] theorem factors_mul (a b : associates α) :
  (a * b).factors = a.factors + b.factors :=
begin
  casesI subsingleton_or_nontrivial α,
  { simp [subsingleton.elim a 0], },
  refine (eq_of_prod_eq_prod (eq_of_factors_eq_factors _)),
  rw [prod_add, factors_prod, factors_prod, factors_prod],
end

theorem factors_mono : ∀{a b : associates α}, a ≤ b → a.factors ≤ b.factors
| s t ⟨d, rfl⟩ := by rw [factors_mul] ; exact le_add_of_nonneg_right bot_le

theorem factors_le {a b : associates α} : a.factors ≤ b.factors ↔ a ≤ b :=
iff.intro
  (assume h, have a.factors.prod ≤ b.factors.prod, from prod_mono h,
    by rwa [factors_prod, factors_prod] at this)
  factors_mono

include dec_irr

lemma count_le_count_of_le {a b p : associates α} (hb : b ≠ 0)
  (hp : irreducible p) (h : a ≤ b) : p.count a.factors ≤ p.count b.factors :=
count_le_count_of_factors_le hb hp $ factors_mono h

omit dec dec' dec_irr

theorem prod_le [nontrivial α] {a b : factor_set α} : a.prod ≤ b.prod ↔ a ≤ b :=
begin
  classical,
  exact iff.intro
  (assume h, have a.prod.factors ≤ b.prod.factors, from factors_mono h,
    by rwa [prod_factors, prod_factors] at this)
  prod_mono
end

include dec dec'

noncomputable instance : has_sup (associates α) := ⟨λa b, (a.factors ⊔ b.factors).prod⟩
noncomputable instance : has_inf (associates α) := ⟨λa b, (a.factors ⊓ b.factors).prod⟩

noncomputable instance : lattice (associates α) :=
{ sup          := (⊔),
  inf          := (⊓),
  sup_le       :=
    assume a b c hac hbc, factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc)),
  le_sup_left  := assume a b,
    le_trans (le_of_eq (factors_prod a).symm) $ prod_mono $ le_sup_left,
  le_sup_right := assume a b,
    le_trans (le_of_eq (factors_prod b).symm) $ prod_mono $ le_sup_right,
  le_inf :=
    assume a b c hac hbc, factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc)),
  inf_le_left  := assume a b,
    le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a)),
  inf_le_right := assume a b,
    le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)),
  .. associates.partial_order }

lemma sup_mul_inf (a b : associates α) : (a ⊔ b) * (a ⊓ b) = a * b :=
show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b,
begin
  nontriviality α,
  refine eq_of_factors_eq_factors _,
  rw [← prod_add, prod_factors, factors_mul, factor_set.sup_add_inf_eq_add]
end

include dec_irr

lemma dvd_of_mem_factors {a p : associates α} {hp : irreducible p}
  (hm : p ∈ factors a) : p ∣ a :=
begin
  by_cases ha0 : a = 0, { rw ha0, exact dvd_zero p },
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0,
  rw [← associates.factors_prod a],
  rw [← ha', factors_mk a0 nza] at hm ⊢,
  erw prod_coe,
  apply multiset.dvd_prod, apply multiset.mem_map.mpr,
  exact ⟨⟨p, hp⟩, mem_factor_set_some.mp hm, rfl⟩
end

omit dec'

lemma dvd_of_mem_factors' {a : α} {p : associates α} {hp : irreducible p} {hz : a ≠ 0}
  (h_mem : subtype.mk p hp ∈ factors' a) : p ∣ associates.mk a :=
by { haveI := classical.dec_eq (associates α),
  apply @dvd_of_mem_factors _ _ _ _ _ _ _ _ hp,
  rw factors_mk _ hz,
  apply mem_factor_set_some.2 h_mem }

omit dec_irr

lemma mem_factors'_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) (hd : p ∣ a) :
  subtype.mk (associates.mk p) ((irreducible_mk _).2 hp) ∈ factors' a :=
begin
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd,
  apply multiset.mem_pmap.mpr, use q, use hq,
  exact subtype.eq (eq.symm (mk_eq_mk_iff_associated.mpr hpq))
end

include dec_irr

lemma mem_factors'_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) :
  subtype.mk (associates.mk p) ((irreducible_mk _).2 hp) ∈ factors' a ↔ p ∣ a :=
begin
  split,
  { rw ← mk_dvd_mk, apply dvd_of_mem_factors', apply ha0 },
  { apply mem_factors'_of_dvd ha0 }
end

include dec'

lemma mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) (hd : p ∣ a) :
  (associates.mk p) ∈ factors (associates.mk a) :=
begin
  rw factors_mk _ ha0, exact mem_factor_set_some.mpr (mem_factors'_of_dvd ha0 hp hd)
end

lemma mem_factors_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) :
  (associates.mk p) ∈ factors (associates.mk a) ↔ p ∣ a :=
begin
  split,
  { rw ← mk_dvd_mk, apply dvd_of_mem_factors, exact (irreducible_mk p).mpr hp },
  { apply mem_factors_of_dvd ha0 hp }
end

lemma exists_prime_dvd_of_not_inf_one {a b : α}
  (ha : a ≠ 0) (hb : b ≠ 0) (h : (associates.mk a) ⊓ (associates.mk b) ≠ 1)  :
  ∃ (p : α), prime p ∧ p ∣ a ∧ p ∣ b :=
begin
  have hz : (factors (associates.mk a)) ⊓ (factors (associates.mk b)) ≠ 0,
  { contrapose! h with hf,
    change ((factors (associates.mk a)) ⊓ (factors (associates.mk b))).prod = 1,
    rw hf,
    exact multiset.prod_zero },
  rw [factors_mk a ha, factors_mk b hb, ← with_top.coe_inf] at hz,
  obtain ⟨⟨p0, p0_irr⟩, p0_mem⟩ := multiset.exists_mem_of_ne_zero ((mt with_top.coe_eq_coe.mpr) hz),
  rw multiset.inf_eq_inter at p0_mem,
  obtain ⟨p, rfl⟩ : ∃ p, associates.mk p = p0 := quot.exists_rep p0,
  refine ⟨p, _, _, _⟩,
  { rw [← irreducible_iff_prime, ← irreducible_mk],
    exact p0_irr },
  { apply dvd_of_mk_le_mk,
    apply dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).left,
    apply ha, },
  { apply dvd_of_mk_le_mk,
    apply dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).right,
    apply hb }
end

theorem coprime_iff_inf_one {a b : α} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
  (associates.mk a) ⊓ (associates.mk b) = 1 ↔ ∀ {d : α}, d ∣ a → d ∣ b → ¬ prime d :=
begin
  split,
  { intros hg p ha hb hp,
    refine ((associates.prime_mk _).mpr hp).not_unit (is_unit_of_dvd_one _ _),
    rw ← hg,
    exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb) },
  { contrapose,
    intros hg hc,
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg,
    exact hc hpa hpb hp }
end

omit dec_irr

theorem factors_self [nontrivial α] {p : associates α}  (hp : irreducible p) :
  p.factors = some ({⟨p, hp⟩}) :=
eq_of_prod_eq_prod (by rw [factors_prod, factor_set.prod, map_singleton, prod_singleton,
                            subtype.coe_mk])

theorem factors_prime_pow [nontrivial α] {p : associates α} (hp : irreducible p)
  (k : ℕ) : factors (p ^ k) = some (multiset.replicate k ⟨p, hp⟩) :=
eq_of_prod_eq_prod (by rw [associates.factors_prod, factor_set.prod, multiset.map_replicate,
                           multiset.prod_replicate, subtype.coe_mk])

include dec_irr

theorem prime_pow_dvd_iff_le [nontrivial α] {m p : associates α} (h₁ : m ≠ 0)
  (h₂ : irreducible p) {k : ℕ} : p ^ k ≤ m ↔ k ≤ count p m.factors :=
begin
  obtain ⟨a, nz, rfl⟩ := associates.exists_non_zero_rep h₁,
  rw [factors_mk _ nz, ← with_top.some_eq_coe, count_some, multiset.le_count_iff_replicate_le,
      ← factors_le, factors_prime_pow h₂, factors_mk _ nz],
  exact with_top.coe_le_coe
end

theorem le_of_count_ne_zero {m p : associates α} (h0 : m ≠ 0)
  (hp : irreducible p) : count p m.factors ≠ 0 → p ≤ m :=
begin
  nontriviality α,
  rw [← pos_iff_ne_zero],
  intro h,
  rw [← pow_one p],
  apply (prime_pow_dvd_iff_le h0 hp).2,
  simpa only
end

theorem count_ne_zero_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) :
  (associates.mk p).count (associates.mk a).factors ≠ 0 ↔ p ∣ a :=
begin
  nontriviality α,
  rw ← associates.mk_le_mk_iff_dvd_iff,
  refine ⟨λ h, associates.le_of_count_ne_zero (associates.mk_ne_zero.mpr ha0)
    ((associates.irreducible_mk p).mpr hp) h, λ h, _⟩,
  { rw [← pow_one (associates.mk p), associates.prime_pow_dvd_iff_le
      (associates.mk_ne_zero.mpr ha0) ((associates.irreducible_mk p).mpr hp)] at h,
    exact (zero_lt_one.trans_le h).ne' }
end

theorem count_self [nontrivial α] {p : associates α} (hp : irreducible p) :
  p.count p.factors = 1 :=
by simp [factors_self hp, associates.count_some hp]

lemma count_eq_zero_of_ne {p q : associates α} (hp : irreducible p) (hq : irreducible q)
  (h : p ≠ q) : p.count q.factors = 0 :=
not_ne_iff.mp $ λ h', h $ associated_iff_eq.mp $ hp.associated_of_dvd hq $
by { nontriviality α, exact le_of_count_ne_zero hq.ne_zero hp h' }

theorem count_mul {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0)
  {p : associates α} (hp : irreducible p) :
  count p (factors (a * b)) = count p a.factors + count p b.factors :=
begin
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha,
  obtain ⟨b0, nzb, hb'⟩ := exists_non_zero_rep hb,
  rw [factors_mul, ← ha', ← hb', factors_mk a0 nza, factors_mk b0 nzb, ← factor_set.coe_add,
      ← with_top.some_eq_coe, ← with_top.some_eq_coe, ← with_top.some_eq_coe, count_some hp,
      multiset.count_add, count_some hp, count_some hp]
end

theorem count_of_coprime {a : associates α} (ha : a ≠ 0) {b : associates α}
  (hb : b ≠ 0)
  (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) {p : associates α} (hp : irreducible p) :
  count p a.factors = 0 ∨ count p b.factors = 0 :=
begin
  rw [or_iff_not_imp_left, ← ne.def],
  intro hca,
  contrapose! hab with hcb,
  exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb,
    (irreducible_iff_prime.mp hp)⟩,
end

theorem count_mul_of_coprime {a : associates α} {b : associates α}
  (hb : b ≠ 0)
  {p : associates α} (hp : irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) :
  count p a.factors = 0 ∨ count p a.factors = count p (a * b).factors :=
begin
  by_cases ha : a = 0,
  { simp [ha], },
  cases count_of_coprime ha hb hab hp with hz hb0, { tauto },
  apply or.intro_right,
  rw [count_mul ha hb hp, hb0, add_zero]
end

theorem count_mul_of_coprime' {a b : associates α}
  {p : associates α} (hp : irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) :
  count p (a * b).factors = count p a.factors
  ∨ count p (a * b).factors = count p b.factors :=
begin
  by_cases ha : a = 0, { simp [ha], },
  by_cases hb : b = 0, { simp [hb], },
  rw [count_mul ha hb hp],
  cases count_of_coprime ha hb hab hp with ha0 hb0,
  { apply or.intro_right, rw [ha0, zero_add] },
  { apply or.intro_left, rw [hb0, add_zero] }
end

theorem dvd_count_of_dvd_count_mul {a b : associates α} (hb : b ≠ 0)
  {p : associates α} (hp : irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d)
  {k : ℕ} (habk : k ∣ count p (a * b).factors) : k ∣ count p a.factors :=
begin
  by_cases ha : a = 0, { simpa [*] using habk, },
  cases count_of_coprime ha hb hab hp with hz h,
  { rw hz, exact dvd_zero k },
  { rw [count_mul ha hb hp, h] at habk, exact habk }
end

omit dec_irr

@[simp] lemma factors_one [nontrivial α] : factors (1 : associates α) = 0 :=
begin
  apply eq_of_prod_eq_prod,
  rw associates.factors_prod,
  exact multiset.prod_zero,
end

@[simp] theorem pow_factors [nontrivial α] {a : associates α} {k : ℕ} :
  (a ^ k).factors = k • a.factors :=
begin
  induction k with n h,
  { rw [zero_nsmul, pow_zero], exact factors_one },
  { rw [pow_succ, succ_nsmul, factors_mul, h] }
end

include dec_irr

lemma count_pow [nontrivial α] {a : associates α} (ha : a ≠ 0) {p : associates α}
  (hp : irreducible p)
  (k : ℕ) : count p (a ^ k).factors = k * count p a.factors :=
begin
  induction k with n h,
  { rw [pow_zero, factors_one, zero_mul, count_zero hp] },
  { rw [pow_succ, count_mul ha (pow_ne_zero _ ha) hp, h, nat.succ_eq_add_one], ring }
end

theorem dvd_count_pow [nontrivial α] {a : associates α} (ha : a ≠ 0) {p : associates α}
  (hp : irreducible p)
  (k : ℕ) : k ∣ count p (a ^ k).factors := by { rw count_pow ha hp, apply dvd_mul_right }

theorem is_pow_of_dvd_count [nontrivial α] {a : associates α} (ha : a ≠ 0) {k : ℕ}
  (hk : ∀ (p : associates α) (hp : irreducible p), k ∣ count p a.factors) :
  ∃ (b : associates α), a = b ^ k :=
begin
  obtain ⟨a0, hz, rfl⟩ := exists_non_zero_rep ha,
  rw [factors_mk a0 hz] at hk,
  have hk' : ∀ p, p ∈ (factors' a0) → k ∣ (factors' a0).count p,
  { rintros p -,
    have pp : p = ⟨p.val, p.2⟩, { simp only [subtype.coe_eta, subtype.val_eq_coe] },
    rw [pp, ← count_some p.2], exact hk p.val p.2 },
  obtain ⟨u, hu⟩ := multiset.exists_smul_of_dvd_count _ hk',
  use (u : factor_set α).prod,
  apply eq_of_factors_eq_factors,
  rw [pow_factors, prod_factors, factors_mk a0 hz, ← with_top.some_eq_coe, hu],
  exact with_bot.coe_nsmul u k
end

/-- The only divisors of prime powers are prime powers. See `eq_pow_find_of_dvd_irreducible_pow`
for an explicit expression as a p-power (without using `count`). -/
theorem eq_pow_count_factors_of_dvd_pow {p a : associates α} (hp : irreducible p)
  {n : ℕ} (h : a ∣ p ^ n) : a = p ^ p.count a.factors :=
begin
  nontriviality α,
  have hph := pow_ne_zero n hp.ne_zero,
  have ha := ne_zero_of_dvd_ne_zero hph h,
  apply eq_of_eq_counts ha (pow_ne_zero _ hp.ne_zero),
  have eq_zero_of_ne : ∀ (q : associates α), irreducible q → q ≠ p → _ = 0 :=
  λ q hq h', nat.eq_zero_of_le_zero $ by
  { convert count_le_count_of_le hph hq h, symmetry,
    rw [count_pow hp.ne_zero hq, count_eq_zero_of_ne hq hp h', mul_zero] },
  intros q hq,
  rw count_pow hp.ne_zero hq,
  by_cases h : q = p,
  { rw [h, count_self hp, mul_one] },
  { rw [count_eq_zero_of_ne hq hp h, mul_zero, eq_zero_of_ne q hq h] }
end

lemma count_factors_eq_find_of_dvd_pow {a p : associates α} (hp : irreducible p)
  [∀ n : ℕ, decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) : nat.find ⟨n, h⟩ = p.count a.factors :=
begin
  apply le_antisymm,
  { refine nat.find_le ⟨1, _⟩, rw mul_one, symmetry, exact eq_pow_count_factors_of_dvd_pow hp h },
  { have hph := pow_ne_zero (nat.find ⟨n, h⟩) hp.ne_zero,
    casesI (subsingleton_or_nontrivial α) with hα hα,
    { simpa using hph, },
    convert count_le_count_of_le hph hp (nat.find_spec ⟨n, h⟩),
    rw [count_pow hp.ne_zero hp, count_self hp, mul_one] }
end

omit dec
omit dec_irr
omit dec'

theorem eq_pow_of_mul_eq_pow [nontrivial α] {a b c : associates α} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) {k : ℕ} (h : a * b = c ^ k) :
  ∃ (d : associates α), a = d ^ k :=
begin
  classical,
  by_cases hk0 : k = 0,
  { use 1,
    rw [hk0, pow_zero] at h ⊢,
    apply (mul_eq_one_iff.1 h).1 },
  { refine is_pow_of_dvd_count ha _,
    intros p hp,
    apply dvd_count_of_dvd_count_mul hb hp hab,
    rw h,
    apply dvd_count_pow _ hp,
    rintros rfl,
    rw zero_pow' _ hk0 at h,
    cases mul_eq_zero.mp h; contradiction }
end

/-- The only divisors of prime powers are prime powers. -/
theorem eq_pow_find_of_dvd_irreducible_pow {a p : associates α} (hp : irreducible p)
  [∀ n : ℕ, decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) : a = p ^ nat.find ⟨n, h⟩ :=
by { classical, rw [count_factors_eq_find_of_dvd_pow hp, ← eq_pow_count_factors_of_dvd_pow hp h] }

end associates

section
open associates unique_factorization_monoid

lemma associates.quot_out {α : Type*} [comm_monoid α] (a : associates α):
associates.mk (quot.out (a)) = a :=
by rw [←quot_mk_eq_mk, quot.out_eq]

/-- `to_gcd_monoid` constructs a GCD monoid out of a unique factorization domain. -/
noncomputable def unique_factorization_monoid.to_gcd_monoid
  (α : Type*) [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
  [decidable_eq (associates α)] [decidable_eq α] : gcd_monoid α :=
{ gcd := λa b, quot.out (associates.mk a ⊓ associates.mk b : associates α),
  lcm := λa b, quot.out (associates.mk a ⊔ associates.mk b : associates α),
  gcd_dvd_left := λ a b, by
  { rw [←mk_dvd_mk, (associates.mk a ⊓ associates.mk b).quot_out, dvd_eq_le],
    exact inf_le_left },
  gcd_dvd_right := λ a b, by
  { rw [←mk_dvd_mk, (associates.mk a ⊓ associates.mk b).quot_out, dvd_eq_le],
    exact inf_le_right },
  dvd_gcd := λ a b c hac hab, by
  { rw [←mk_dvd_mk, (associates.mk c ⊓ associates.mk b).quot_out, dvd_eq_le,
      le_inf_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff],
    exact ⟨hac, hab⟩ },
  lcm_zero_left := λ a, by
  { have : associates.mk (0 : α) = ⊤ := rfl,
    rw [this, top_sup_eq, ←this, ←associated_zero_iff_eq_zero, ←mk_eq_mk_iff_associated,
      ←associated_iff_eq, associates.quot_out] },
  lcm_zero_right := λ a, by
  { have : associates.mk (0 : α) = ⊤ := rfl,
    rw [this, sup_top_eq, ←this, ←associated_zero_iff_eq_zero, ←mk_eq_mk_iff_associated,
      ←associated_iff_eq, associates.quot_out] },
  gcd_mul_lcm := λ a b, by
  { rw [←mk_eq_mk_iff_associated, ←associates.mk_mul_mk, ←associated_iff_eq, associates.quot_out,
      associates.quot_out, mul_comm, sup_mul_inf, associates.mk_mul_mk] } }

/-- `to_normalized_gcd_monoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
noncomputable def unique_factorization_monoid.to_normalized_gcd_monoid
  (α : Type*) [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
  [normalization_monoid α] [decidable_eq (associates α)] [decidable_eq α] :
  normalized_gcd_monoid α :=
{ gcd := λa b, (associates.mk a ⊓ associates.mk b).out,
  lcm := λa b, (associates.mk a ⊔ associates.mk b).out,
  gcd_dvd_left := assume a b, (out_dvd_iff a (associates.mk a ⊓ associates.mk b)).2 $ inf_le_left,
  gcd_dvd_right := assume a b, (out_dvd_iff b (associates.mk a ⊓ associates.mk b)).2 $ inf_le_right,
  dvd_gcd := assume a b c hac hab, show a ∣ (associates.mk c ⊓ associates.mk b).out,
    by rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff]; exact ⟨hac, hab⟩,
  lcm_zero_left := assume a, show (⊤ ⊔ associates.mk a).out = 0, by simp,
  lcm_zero_right := assume a, show (associates.mk a ⊔ ⊤).out = 0, by simp,
  gcd_mul_lcm := assume a b, by
  { rw [← out_mul, mul_comm, sup_mul_inf, mk_mul_mk, out_mk],
    exact normalize_associated (a * b) },
  normalize_gcd := assume a b, by convert normalize_out _,
  normalize_lcm := assume a b, by convert normalize_out _,
  .. ‹normalization_monoid α› }

end

namespace unique_factorization_monoid

/-- If `y` is a nonzero element of a unique factorization monoid with finitely
many units (e.g. `ℤ`, `ideal (ring_of_integers K)`), it has finitely many divisors. -/
noncomputable def fintype_subtype_dvd {M : Type*} [cancel_comm_monoid_with_zero M]
  [unique_factorization_monoid M] [fintype Mˣ]
  (y : M) (hy : y ≠ 0) :
  fintype {x // x ∣ y} :=
begin
  haveI : nontrivial M := ⟨⟨y, 0, hy⟩⟩,
  haveI : normalization_monoid M := unique_factorization_monoid.normalization_monoid,
  haveI := classical.dec_eq M,
  haveI := classical.dec_eq (associates M),
  -- We'll show `λ (u : Mˣ) (f ⊆ factors y) → u * Π f` is injective
  -- and has image exactly the divisors of `y`.
  refine fintype.of_finset
    (((normalized_factors y).powerset.to_finset.product (finset.univ : finset Mˣ)).image
      (λ s, (s.snd : M) * s.fst.prod))
    (λ x, _),
  simp only [exists_prop, finset.mem_image, finset.mem_product, finset.mem_univ, and_true,
    multiset.mem_to_finset, multiset.mem_powerset, exists_eq_right, multiset.mem_map],
  split,
  { rintros ⟨s, hs, rfl⟩,
    have prod_s_ne : s.fst.prod ≠ 0,
    { intro hz,
      apply hy (eq_zero_of_zero_dvd _),
      have hz := (@multiset.prod_eq_zero_iff M _ _ _ s.fst).mp hz,
      rw ← (normalized_factors_prod hy).dvd_iff_dvd_right,
      exact multiset.dvd_prod (multiset.mem_of_le hs hz) },
    show (s.snd : M) * s.fst.prod ∣ y,
    rw [(unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left, one_mul,
        ← (normalized_factors_prod hy).dvd_iff_dvd_right],
    exact multiset.prod_dvd_prod_of_le hs },
  { rintro (h : x ∣ y),
    have hx : x ≠ 0, { refine mt (λ hx, _) hy, rwa [hx, zero_dvd_iff] at h },
    obtain ⟨u, hu⟩ := normalized_factors_prod hx,
    refine ⟨⟨normalized_factors x, u⟩, _, (mul_comm _ _).trans hu⟩,
    exact (dvd_iff_normalized_factors_le_normalized_factors hx hy).mp h }
end

end unique_factorization_monoid

section finsupp
variables [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
variables [normalization_monoid α] [decidable_eq α]

open unique_factorization_monoid

/-- This returns the multiset of irreducible factors as a `finsupp` -/
noncomputable def factorization (n : α) : α →₀ ℕ := (normalized_factors n).to_finsupp

lemma factorization_eq_count {n p : α} :
  factorization n p = multiset.count p (normalized_factors n) :=
by simp [factorization]

@[simp] lemma factorization_zero : factorization (0 : α) = 0 := by simp [factorization]

@[simp] lemma factorization_one : factorization (1 : α) = 0 := by simp [factorization]

/-- The support of `factorization n` is exactly the finset of normalized factors -/
@[simp] lemma support_factorization {n : α} :
  (factorization n).support = (normalized_factors n).to_finset :=
by simp [factorization, multiset.to_finsupp_support]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp] lemma factorization_mul {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
  factorization (a * b) = factorization a + factorization b :=
by simp [factorization, normalized_factors_mul ha hb]

/-- For any `p`, the power of `p` in `x^n` is `n` times the power in `x` -/
lemma factorization_pow {x : α} {n : ℕ} :
  factorization (x^n) = n • factorization x :=
by { ext, simp [factorization] }

lemma associated_of_factorization_eq (a b: α) (ha: a ≠ 0) (hb: b ≠ 0)
  (h: factorization a = factorization b) : associated a b :=
begin
  simp_rw [factorization, add_equiv.apply_eq_iff_eq] at h,
  rwa [associated_iff_normalized_factors_eq_normalized_factors ha hb],
end

end finsupp
