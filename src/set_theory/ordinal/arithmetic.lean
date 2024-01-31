/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import set_theory.ordinal.basic
import tactic.by_contra

/-!
# Ordinal arithmetic

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Ordinals have an addition (corresponding to disjoint union) that turns them into an additive
monoid, and a multiplication (corresponding to the lexicographic order on the product) that turns
them into a monoid. One can also define correspondingly a subtraction, a division, a successor
function, a power function and a logarithm function.

We also define limit ordinals and prove the basic induction principle on ordinals separating
successor ordinals and limit ordinals, in `limit_rec_on`.

## Main definitions and results

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
* `o₁ - o₂` is the unique ordinal `o` such that `o₂ + o = o₁`, when `o₂ ≤ o₁`.
* `o₁ * o₂` is the lexicographic order on `o₂ × o₁`.
* `o₁ / o₂` is the ordinal `o` such that `o₁ = o₂ * o + o'` with `o' < o₂`. We also define the
  divisibility predicate, and a modulo operation.
* `order.succ o = o + 1` is the successor of `o`.
* `pred o` if the predecessor of `o`. If `o` is not a successor, we set `pred o = o`.

We discuss the properties of casts of natural numbers of and of `ω` with respect to these
operations.

Some properties of the operations are also used to discuss general tools on ordinals:

* `is_limit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `limit_rec_on` is the main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals.
* `is_normal`: a function `f : ordinal → ordinal` satisfies `is_normal` if it is strictly increasing
  and order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.
* `enum_ord`: enumerates an unbounded set of ordinals by the ordinals themselves.
* `sup`, `lsub`: the supremum / least strict upper bound of an indexed family of ordinals in
  `Type u`, as an ordinal in `Type u`.
* `bsup`, `blsub`: the supremum / least strict upper bound of a set of ordinals indexed by ordinals
  less than a given ordinal `o`.

Various other basic arithmetic results are given in `principal.lean` instead.
-/

noncomputable theory

open function cardinal set equiv order
open_locale classical cardinal ordinal

universes u v w

namespace ordinal
variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Further properties of addition on ordinals -/

@[simp] theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩,
quotient.sound ⟨(rel_iso.preimage equiv.ulift _).trans
 (rel_iso.sum_lex_congr (rel_iso.preimage equiv.ulift _)
   (rel_iso.preimage equiv.ulift _)).symm⟩

@[simp] theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
by { rw [←add_one_eq_succ, lift_add, lift_one], refl }

instance add_contravariant_class_le : contravariant_class ordinal.{u} ordinal.{u} (+) (≤) :=
⟨λ a b c, induction_on a $ λ α r hr, induction_on b $ λ β₁ s₁ hs₁, induction_on c $ λ β₂ s₂ hs₂ ⟨f⟩,
  ⟨have fl : ∀ a, f (sum.inl a) = sum.inl a := λ a,
    by simpa only [initial_seg.trans_apply, initial_seg.le_add_apply]
      using @initial_seg.eq _ _ _ _ (@sum.lex.is_well_order _ _ _ _ hr hs₂)
        ((initial_seg.le_add r s₁).trans f) (initial_seg.le_add r s₂) a,
  have ∀ b, {b' // f (sum.inr b) = sum.inr b'}, begin
    intro b, cases e : f (sum.inr b),
    { rw ← fl at e, have := f.inj' e, contradiction },
    { exact ⟨_, rfl⟩ }
  end,
  let g (b) := (this b).1 in
  have fr : ∀ b, f (sum.inr b) = sum.inr (g b), from λ b, (this b).2,
  ⟨⟨⟨g, λ x y h, by injection f.inj'
    (by rw [fr, fr, h] : f (sum.inr x) = f (sum.inr y))⟩,
    λ a b, by simpa only [sum.lex_inr_inr, fr, rel_embedding.coe_fn_to_embedding,
        initial_seg.coe_fn_to_rel_embedding, embedding.coe_fn_mk]
      using @rel_embedding.map_rel_iff _ _ _ _ f.to_rel_embedding (sum.inr a) (sum.inr b)⟩,
    λ a b H, begin
      rcases f.init (by rw fr; exact sum.lex_inr_inr.2 H) with ⟨a'|a', h⟩,
      { rw fl at h, cases h },
      { rw fr at h, exact ⟨a', sum.inr.inj h⟩ }
    end⟩⟩⟩

theorem add_left_cancel (a) {b c : ordinal} : a + b = a + c ↔ b = c :=
by simp only [le_antisymm_iff, add_le_add_iff_left]

private theorem add_lt_add_iff_left' (a) {b c : ordinal} : a + b < a + c ↔ b < c :=
by rw [← not_le, ← not_le, add_le_add_iff_left]

instance add_covariant_class_lt : covariant_class ordinal.{u} ordinal.{u} (+) (<) :=
⟨λ a b c, (add_lt_add_iff_left' a).2⟩

instance add_contravariant_class_lt : contravariant_class ordinal.{u} ordinal.{u} (+) (<) :=
⟨λ a b c, (add_lt_add_iff_left' a).1⟩

instance add_swap_contravariant_class_lt :
  contravariant_class ordinal.{u} ordinal.{u} (swap (+)) (<) :=
⟨λ a b c, lt_imp_lt_of_le_imp_le (λ h, add_le_add_right h _)⟩

theorem add_le_add_iff_right {a b : ordinal} : ∀ n : ℕ, a + n ≤ b + n ↔ a ≤ b
| 0     := by simp
| (n+1) := by rw [nat_cast_succ, add_succ, add_succ, succ_le_succ_iff, add_le_add_iff_right]

theorem add_right_cancel {a b : ordinal} (n : ℕ) : a + n = b + n ↔ a = b :=
by simp only [le_antisymm_iff, add_le_add_iff_right]

theorem add_eq_zero_iff {a b : ordinal} : a + b = 0 ↔ (a = 0 ∧ b = 0) :=
induction_on a $ λ α r _, induction_on b $ λ β s _, begin
  simp_rw [←type_sum_lex, type_eq_zero_iff_is_empty],
  exact is_empty_sum
end

theorem left_eq_zero_of_add_eq_zero {a b : ordinal} (h : a + b = 0) : a = 0 :=
(add_eq_zero_iff.1 h).1

theorem right_eq_zero_of_add_eq_zero {a b : ordinal} (h : a + b = 0) : b = 0 :=
(add_eq_zero_iff.1 h).2

/-! ### The predecessor of an ordinal -/

/-- The ordinal predecessor of `o` is `o'` if `o = succ o'`,
  and `o` otherwise. -/
def pred (o : ordinal) : ordinal :=
if h : ∃ a, o = succ a then classical.some h else o

@[simp] theorem pred_succ (o) : pred (succ o) = o :=
by have h : ∃ a, succ o = succ a := ⟨_, rfl⟩;
   simpa only [pred, dif_pos h] using (succ_injective $ classical.some_spec h).symm

theorem pred_le_self (o) : pred o ≤ o :=
if h : ∃ a, o = succ a then let ⟨a, e⟩ := h in
by rw [e, pred_succ]; exact le_succ a
else by rw [pred, dif_neg h]

theorem pred_eq_iff_not_succ {o} : pred o = o ↔ ¬ ∃ a, o = succ a :=
⟨λ e ⟨a, e'⟩, by rw [e', pred_succ] at e; exact (lt_succ a).ne e,
 λ h, dif_neg h⟩

theorem pred_eq_iff_not_succ' {o} : pred o = o ↔ ∀ a, o ≠ succ a :=
by simpa using pred_eq_iff_not_succ

theorem pred_lt_iff_is_succ {o} : pred o < o ↔ ∃ a, o = succ a :=
iff.trans (by simp only [le_antisymm_iff, pred_le_self, true_and, not_le])
  (iff_not_comm.1 pred_eq_iff_not_succ).symm

@[simp] theorem pred_zero : pred 0 = 0 :=
pred_eq_iff_not_succ'.2 $ λ a, (succ_ne_zero a).symm

theorem succ_pred_iff_is_succ {o} : succ (pred o) = o ↔ ∃ a, o = succ a :=
⟨λ e, ⟨_, e.symm⟩, λ ⟨a, e⟩, by simp only [e, pred_succ]⟩

theorem succ_lt_of_not_succ {o b : ordinal} (h : ¬ ∃ a, o = succ a) : succ b < o ↔ b < o :=
⟨(lt_succ b).trans, λ l, lt_of_le_of_ne (succ_le_of_lt l) (λ e, h ⟨_, e.symm⟩)⟩

theorem lt_pred {a b} : a < pred b ↔ succ a < b :=
if h : ∃ a, b = succ a then let ⟨c, e⟩ := h in
by rw [e, pred_succ, succ_lt_succ_iff]
else by simp only [pred, dif_neg h, succ_lt_of_not_succ h]

theorem pred_le {a b} : pred a ≤ b ↔ a ≤ succ b :=
le_iff_le_iff_lt_iff_lt.2 lt_pred

@[simp] theorem lift_is_succ {o} : (∃ a, lift o = succ a) ↔ (∃ a, o = succ a) :=
⟨λ ⟨a, h⟩,
  let ⟨b, e⟩ := lift_down $ show a ≤ lift o, from le_of_lt $
    h.symm ▸ lt_succ a in
  ⟨b, lift_inj.1 $ by rw [h, ← e, lift_succ]⟩,
 λ ⟨a, h⟩, ⟨lift a, by simp only [h, lift_succ]⟩⟩

@[simp] theorem lift_pred (o) : lift (pred o) = pred (lift o) :=
if h : ∃ a, o = succ a then
by cases h with a e; simp only [e, pred_succ, lift_succ]
else by rw [pred_eq_iff_not_succ.2 h,
            pred_eq_iff_not_succ.2 (mt lift_is_succ.1 h)]

/-! ### Limit ordinals -/

/-- A limit ordinal is an ordinal which is not zero and not a successor. -/
def is_limit (o : ordinal) : Prop := o ≠ 0 ∧ ∀ a < o, succ a < o

theorem is_limit.succ_lt {o a : ordinal} (h : is_limit o) : a < o → succ a < o :=
h.2 a

theorem not_zero_is_limit : ¬ is_limit 0
| ⟨h, _⟩ := h rfl

theorem not_succ_is_limit (o) : ¬ is_limit (succ o)
| ⟨_, h⟩ := lt_irrefl _ (h _ (lt_succ o))

theorem not_succ_of_is_limit {o} (h : is_limit o) : ¬ ∃ a, o = succ a
| ⟨a, e⟩ := not_succ_is_limit a (e ▸ h)

theorem succ_lt_of_is_limit {o a : ordinal} (h : is_limit o) : succ a < o ↔ a < o :=
⟨(lt_succ a).trans, h.2 _⟩

theorem le_succ_of_is_limit {o} (h : is_limit o) {a} : o ≤ succ a ↔ o ≤ a :=
le_iff_le_iff_lt_iff_lt.2 $ succ_lt_of_is_limit h

theorem limit_le {o} (h : is_limit o) {a} : o ≤ a ↔ ∀ x < o, x ≤ a :=
⟨λ h x l, l.le.trans h,
 λ H, (le_succ_of_is_limit h).1 $ le_of_not_lt $ λ hn,
  not_lt_of_le (H _ hn) (lt_succ a)⟩

theorem lt_limit {o} (h : is_limit o) {a} : a < o ↔ ∃ x < o, a < x :=
by simpa only [not_ball, not_le] using not_congr (@limit_le _ h a)

@[simp] theorem lift_is_limit (o) : is_limit (lift o) ↔ is_limit o :=
and_congr (not_congr $ by simpa only [lift_zero] using @lift_inj o 0)
⟨λ H a h, lift_lt.1 $ by simpa only [lift_succ] using H _ (lift_lt.2 h),
 λ H a h, begin
   obtain ⟨a', rfl⟩ := lift_down h.le,
   rw [←lift_succ, lift_lt],
   exact H a' (lift_lt.1 h)
 end⟩

theorem is_limit.pos {o : ordinal} (h : is_limit o) : 0 < o :=
lt_of_le_of_ne (ordinal.zero_le _) h.1.symm

theorem is_limit.one_lt {o : ordinal} (h : is_limit o) : 1 < o :=
by simpa only [succ_zero] using h.2 _ h.pos

theorem is_limit.nat_lt {o : ordinal} (h : is_limit o) : ∀ n : ℕ, (n : ordinal) < o
| 0     := h.pos
| (n+1) := h.2 _ (is_limit.nat_lt n)

theorem zero_or_succ_or_limit (o : ordinal) :
  o = 0 ∨ (∃ a, o = succ a) ∨ is_limit o :=
if o0 : o = 0 then or.inl o0 else
if h : ∃ a, o = succ a then or.inr (or.inl h) else
or.inr $ or.inr ⟨o0, λ a, (succ_lt_of_not_succ h).2⟩

/-- Main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals. -/
@[elab_as_eliminator] def limit_rec_on {C : ordinal → Sort*}
  (o : ordinal) (H₁ : C 0) (H₂ : ∀ o, C o → C (succ o))
  (H₃ : ∀ o, is_limit o → (∀ o' < o, C o') → C o) : C o :=
lt_wf.fix (λ o IH,
  if o0 : o = 0 then by rw o0; exact H₁ else
  if h : ∃ a, o = succ a then
    by rw ← succ_pred_iff_is_succ.2 h; exact
    H₂ _ (IH _ $ pred_lt_iff_is_succ.2 h)
  else H₃ _ ⟨o0, λ a, (succ_lt_of_not_succ h).2⟩ IH) o

@[simp] theorem limit_rec_on_zero {C} (H₁ H₂ H₃) : @limit_rec_on C 0 H₁ H₂ H₃ = H₁ :=
by rw [limit_rec_on, lt_wf.fix_eq, dif_pos rfl]; refl

@[simp] theorem limit_rec_on_succ {C} (o H₁ H₂ H₃) :
  @limit_rec_on C (succ o) H₁ H₂ H₃ = H₂ o (@limit_rec_on C o H₁ H₂ H₃) :=
begin
  have h : ∃ a, succ o = succ a := ⟨_, rfl⟩,
  rw [limit_rec_on, lt_wf.fix_eq, dif_neg (succ_ne_zero o), dif_pos h],
  generalize : limit_rec_on._proof_2 (succ o) h = h₂,
  generalize : limit_rec_on._proof_3 (succ o) h = h₃,
  revert h₂ h₃, generalize e : pred (succ o) = o', intros,
  rw pred_succ at e, subst o', refl
end

@[simp] theorem limit_rec_on_limit {C} (o H₁ H₂ H₃ h) :
  @limit_rec_on C o H₁ H₂ H₃ = H₃ o h (λ x h, @limit_rec_on C x H₁ H₂ H₃) :=
by rw [limit_rec_on, lt_wf.fix_eq, dif_neg h.1, dif_neg (not_succ_of_is_limit h)]; refl

instance order_top_out_succ (o : ordinal) : order_top (succ o).out.α :=
⟨_, le_enum_succ⟩

theorem enum_succ_eq_top {o : ordinal} :
  enum (<) o (by { rw type_lt, exact lt_succ o }) = (⊤ : (succ o).out.α) :=
rfl

lemma has_succ_of_type_succ_lt {α} {r : α → α → Prop} [wo : is_well_order α r]
  (h : ∀ a < type r, succ a < type r) (x : α) : ∃ y, r x y :=
begin
  use enum r (succ (typein r x)) (h _ (typein_lt_type r x)),
  convert (enum_lt_enum (typein_lt_type r x) _).mpr (lt_succ _), rw [enum_typein]
end

theorem out_no_max_of_succ_lt {o : ordinal} (ho : ∀ a < o, succ a < o) : no_max_order o.out.α :=
⟨has_succ_of_type_succ_lt (by rwa type_lt)⟩

lemma bounded_singleton {r : α → α → Prop} [is_well_order α r] (hr : (type r).is_limit) (x) :
  bounded r {x} :=
begin
  refine ⟨enum r (succ (typein r x)) (hr.2 _ (typein_lt_type r x)), _⟩,
  intros b hb,
  rw mem_singleton_iff.1 hb,
  nth_rewrite 0 ←enum_typein r x,
  rw @enum_lt_enum _ r,
  apply lt_succ
end

lemma type_subrel_lt (o : ordinal.{u}) :
  type (subrel (<) {o' : ordinal | o' < o}) = ordinal.lift.{u+1} o :=
begin
  refine quotient.induction_on o _,
  rintro ⟨α, r, wo⟩, resetI, apply quotient.sound,
  constructor, symmetry, refine (rel_iso.preimage equiv.ulift r).trans (enum_iso r).symm
end

lemma mk_initial_seg (o : ordinal.{u}) :
  #{o' : ordinal | o' < o} = cardinal.lift.{u+1} o.card :=
by rw [lift_card, ←type_subrel_lt, card_type]

/-! ### Normal ordinal functions -/

/-- A normal ordinal function is a strictly increasing function which is
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.  -/
def is_normal (f : ordinal → ordinal) : Prop :=
(∀ o, f o < f (succ o)) ∧ ∀ o, is_limit o → ∀ a, f o ≤ a ↔ ∀ b < o, f b ≤ a

theorem is_normal.limit_le {f} (H : is_normal f) : ∀ {o}, is_limit o →
  ∀ {a}, f o ≤ a ↔ ∀ b < o, f b ≤ a := H.2

theorem is_normal.limit_lt {f} (H : is_normal f) {o} (h : is_limit o) {a} :
  a < f o ↔ ∃ b < o, a < f b :=
not_iff_not.1 $ by simpa only [exists_prop, not_exists, not_and, not_lt] using H.2 _ h a

theorem is_normal.strict_mono {f} (H : is_normal f) : strict_mono f :=
λ a b, limit_rec_on b (not.elim (not_lt_of_le $ ordinal.zero_le _))
  (λ b IH h, (lt_or_eq_of_le (le_of_lt_succ h)).elim
    (λ h, (IH h).trans (H.1 _))
    (λ e, e ▸ H.1 _))
  (λ b l IH h, lt_of_lt_of_le (H.1 a)
    ((H.2 _ l _).1 le_rfl _ (l.2 _ h)))

theorem is_normal.monotone {f} (H : is_normal f) : monotone f :=
H.strict_mono.monotone

theorem is_normal_iff_strict_mono_limit (f : ordinal → ordinal) :
  is_normal f ↔ (strict_mono f ∧ ∀ o, is_limit o → ∀ a, (∀ b < o, f b ≤ a) → f o ≤ a) :=
⟨λ hf, ⟨hf.strict_mono, λ a ha c, (hf.2 a ha c).2⟩, λ ⟨hs, hl⟩, ⟨λ a, hs (lt_succ a),
  λ a ha c, ⟨λ hac b hba, ((hs hba).trans_le hac).le, hl a ha c⟩⟩⟩

theorem is_normal.lt_iff {f} (H : is_normal f) {a b} : f a < f b ↔ a < b :=
strict_mono.lt_iff_lt $ H.strict_mono

theorem is_normal.le_iff {f} (H : is_normal f) {a b} : f a ≤ f b ↔ a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 H.lt_iff

theorem is_normal.inj {f} (H : is_normal f) {a b} : f a = f b ↔ a = b :=
by simp only [le_antisymm_iff, H.le_iff]

theorem is_normal.self_le {f} (H : is_normal f) (a) : a ≤ f a :=
lt_wf.self_le_of_strict_mono H.strict_mono a

theorem is_normal.le_set {f o} (H : is_normal f) (p : set ordinal) (p0 : p.nonempty) (b)
  (H₂ : ∀ o, b ≤ o ↔ ∀ a ∈ p, a ≤ o) : f b ≤ o ↔ ∀ a ∈ p, f a ≤ o :=
⟨λ h a pa, (H.le_iff.2 ((H₂ _).1 le_rfl _ pa)).trans h,
λ h, begin
  revert H₂, refine limit_rec_on b (λ H₂, _) (λ S _ H₂, _) (λ S L _ H₂, (H.2 _ L _).2 (λ a h', _)),
  { cases p0 with x px,
    have := ordinal.le_zero.1 ((H₂ _).1 (ordinal.zero_le _) _ px),
    rw this at px, exact h _ px },
  { rcases not_ball.1 (mt (H₂ S).2 $ (lt_succ S).not_le) with ⟨a, h₁, h₂⟩,
    exact (H.le_iff.2 $ succ_le_of_lt $ not_le.1 h₂).trans (h _ h₁) },
  { rcases not_ball.1 (mt (H₂ a).2 h'.not_le) with ⟨b, h₁, h₂⟩,
    exact (H.le_iff.2 $ (not_le.1 h₂).le).trans (h _ h₁) }
end⟩

theorem is_normal.le_set' {f o} (H : is_normal f) (p : set α) (p0 : p.nonempty) (g : α → ordinal)
  (b) (H₂ : ∀ o, b ≤ o ↔ ∀ a ∈ p, g a ≤ o) : f b ≤ o ↔ ∀ a ∈ p, f (g a) ≤ o :=
by simpa [H₂] using H.le_set (g '' p) (p0.image g) b

theorem is_normal.refl : is_normal id := ⟨lt_succ, λ o l a, limit_le l⟩

theorem is_normal.trans {f g} (H₁ : is_normal f) (H₂ : is_normal g) : is_normal (f ∘ g) :=
⟨λ x, H₁.lt_iff.2 (H₂.1 _), λ o l a, H₁.le_set' (< o) ⟨_, l.pos⟩ g _ (λ c, H₂.2 _ l _)⟩

theorem is_normal.is_limit {f} (H : is_normal f) {o} (l : is_limit o) : is_limit (f o) :=
⟨ne_of_gt $ (ordinal.zero_le _).trans_lt $ H.lt_iff.2 l.pos,
λ a h, let ⟨b, h₁, h₂⟩ := (H.limit_lt l).1 h in
  (succ_le_of_lt h₂).trans_lt (H.lt_iff.2 h₁)⟩

theorem is_normal.le_iff_eq {f} (H : is_normal f) {a} : f a ≤ a ↔ f a = a := (H.self_le a).le_iff_eq

theorem add_le_of_limit {a b c : ordinal} (h : is_limit b) : a + b ≤ c ↔ ∀ b' < b, a + b' ≤ c :=
⟨λ h b' l, (add_le_add_left l.le _).trans h,
λ H, le_of_not_lt $
induction_on a (λ α r _, induction_on b $ λ β s _ h H l, begin
  resetI,
  suffices : ∀ x : β, sum.lex r s (sum.inr x) (enum _ _ l),
  { cases enum _ _ l with x x,
    { cases this (enum s 0 h.pos) },
    { exact irrefl _ (this _) } },
  intros x,
  rw [←typein_lt_typein (sum.lex r s), typein_enum],
  have := H _ (h.2 _ (typein_lt_type s x)),
  rw [add_succ, succ_le_iff] at this,
  refine (rel_embedding.of_monotone (λ a, _) (λ a b, _)).ordinal_type_le.trans_lt this,
  { rcases a with ⟨a | b, h⟩,
    { exact sum.inl a },
    { exact sum.inr ⟨b, by cases h; assumption⟩ } },
  { rcases a with ⟨a | a, h₁⟩; rcases b with ⟨b | b, h₂⟩; cases h₁; cases h₂;
      rintro ⟨⟩; constructor; assumption }
end) h H⟩

theorem add_is_normal (a : ordinal) : is_normal ((+) a) :=
⟨λ b, (add_lt_add_iff_left a).2 (lt_succ b),
 λ b l c, add_le_of_limit l⟩

theorem add_is_limit (a) {b} : is_limit b → is_limit (a + b) :=
(add_is_normal a).is_limit

alias add_is_limit ← is_limit.add

/-! ### Subtraction on ordinals-/

/-- The set in the definition of subtraction is nonempty. -/
theorem sub_nonempty {a b : ordinal} : {o | a ≤ b + o}.nonempty :=
⟨a, le_add_left _ _⟩

/-- `a - b` is the unique ordinal satisfying `b + (a - b) = a` when `b ≤ a`. -/
instance : has_sub ordinal := ⟨λ a b, Inf {o | a ≤ b + o}⟩

theorem le_add_sub (a b : ordinal) : a ≤ b + (a - b) :=
Inf_mem sub_nonempty

theorem sub_le {a b c : ordinal} : a - b ≤ c ↔ a ≤ b + c :=
⟨λ h, (le_add_sub a b).trans (add_le_add_left h _), λ h, cInf_le' h⟩

theorem lt_sub {a b c : ordinal} : a < b - c ↔ c + a < b :=
lt_iff_lt_of_le_iff_le sub_le

theorem add_sub_cancel (a b : ordinal) : a + b - a = b :=
le_antisymm (sub_le.2 $ le_rfl)
  ((add_le_add_iff_left a).1 $ le_add_sub _ _)

theorem sub_eq_of_add_eq {a b c : ordinal} (h : a + b = c) : c - a = b :=
h ▸ add_sub_cancel _ _

theorem sub_le_self (a b : ordinal) : a - b ≤ a :=
sub_le.2 $ le_add_left _ _

protected theorem add_sub_cancel_of_le {a b : ordinal} (h : b ≤ a) : b + (a - b) = a :=
(le_add_sub a b).antisymm' begin
  rcases zero_or_succ_or_limit (a-b) with e|⟨c,e⟩|l,
  { simp only [e, add_zero, h] },
  { rw [e, add_succ, succ_le_iff, ← lt_sub, e], exact lt_succ c },
  { exact (add_le_of_limit l).2 (λ c l, (lt_sub.1 l).le) }
end

theorem le_sub_of_le {a b c : ordinal} (h : b ≤ a) : c ≤ a - b ↔ b + c ≤ a :=
by rw [←add_le_add_iff_left b, ordinal.add_sub_cancel_of_le h]

theorem sub_lt_of_le {a b c : ordinal} (h : b ≤ a) : a - b < c ↔ a < b + c :=
lt_iff_lt_of_le_iff_le (le_sub_of_le h)

instance : has_exists_add_of_le ordinal :=
⟨λ a b h, ⟨_, (ordinal.add_sub_cancel_of_le h).symm⟩⟩

@[simp] theorem sub_zero (a : ordinal) : a - 0 = a :=
by simpa only [zero_add] using add_sub_cancel 0 a

@[simp] theorem zero_sub (a : ordinal) : 0 - a = 0 :=
by rw ← ordinal.le_zero; apply sub_le_self

@[simp] theorem sub_self (a : ordinal) : a - a = 0 :=
by simpa only [add_zero] using add_sub_cancel a 0

protected theorem sub_eq_zero_iff_le {a b : ordinal} : a - b = 0 ↔ a ≤ b :=
⟨λ h, by simpa only [h, add_zero] using le_add_sub a b,
 λ h, by rwa [← ordinal.le_zero, sub_le, add_zero]⟩

theorem sub_sub (a b c : ordinal) : a - b - c = a - (b + c) :=
eq_of_forall_ge_iff $ λ d, by rw [sub_le, sub_le, sub_le, add_assoc]

@[simp] theorem add_sub_add_cancel (a b c : ordinal) : a + b - (a + c) = b - c :=
by rw [← sub_sub, add_sub_cancel]

theorem sub_is_limit {a b} (l : is_limit a) (h : b < a) : is_limit (a - b) :=
⟨ne_of_gt $ lt_sub.2 $ by rwa add_zero,
 λ c h, by rw [lt_sub, add_succ]; exact l.2 _ (lt_sub.1 h)⟩

@[simp] theorem one_add_omega : 1 + ω = ω :=
begin
  refine le_antisymm _ (le_add_left _ _),
  rw [omega, ← lift_one.{0}, ← lift_add, lift_le, ← type_unit, ← type_sum_lex],
  refine ⟨rel_embedding.collapse (rel_embedding.of_monotone _ _)⟩,
  { apply sum.rec, exact λ _, 0, exact nat.succ },
  { intros a b, cases a; cases b; intro H; cases H with _ _ H _ _ H;
    [cases H, exact nat.succ_pos _, exact nat.succ_lt_succ H] }
end

@[simp, priority 990]
theorem one_add_of_omega_le {o} (h : ω ≤ o) : 1 + o = o :=
by rw [← ordinal.add_sub_cancel_of_le h, ← add_assoc, one_add_omega]

/-! ### Multiplication of ordinals-/

/-- The multiplication of ordinals `o₁` and `o₂` is the (well founded) lexicographic order on
`o₂ × o₁`. -/
instance : monoid ordinal.{u} :=
{ mul := λ a b, quotient.lift_on₂ a b
      (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, ⟦⟨β × α, prod.lex s r, by exactI prod.lex.is_well_order⟩⟧
        : Well_order → Well_order → ordinal) $
    λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
    quot.sound ⟨rel_iso.prod_lex_congr g f⟩,
  one := 1,
  mul_assoc := λ a b c, quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩,
    eq.symm $ quotient.sound ⟨⟨prod_assoc _ _ _, λ a b, begin
      rcases a with ⟨⟨a₁, a₂⟩, a₃⟩,
      rcases b with ⟨⟨b₁, b₂⟩, b₃⟩,
      simp [prod.lex_def, and_or_distrib_left, or_assoc, and_assoc]
    end⟩⟩,
  mul_one := λ a, induction_on a $ λ α r _, quotient.sound
    ⟨⟨punit_prod _, λ a b, by rcases a with ⟨⟨⟨⟩⟩, a⟩; rcases b with ⟨⟨⟨⟩⟩, b⟩;
    simp only [prod.lex_def, empty_relation, false_or];
    simp only [eq_self_iff_true, true_and]; refl⟩⟩,
  one_mul := λ a, induction_on a $ λ α r _, quotient.sound
    ⟨⟨prod_punit _, λ a b, by rcases a with ⟨a, ⟨⟨⟩⟩⟩; rcases b with ⟨b, ⟨⟨⟩⟩⟩;
    simp only [prod.lex_def, empty_relation, and_false, or_false]; refl⟩⟩ }

@[simp] theorem type_prod_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop)
  [is_well_order α r] [is_well_order β s] : type (prod.lex s r) = type r * type s := rfl

private theorem mul_eq_zero' {a b : ordinal} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
induction_on a $ λ α _ _, induction_on b $ λ β _ _, begin
  simp_rw [←type_prod_lex, type_eq_zero_iff_is_empty],
  rw or_comm,
  exact is_empty_prod
end

instance : monoid_with_zero ordinal :=
{ zero := 0,
  mul_zero := λ a, mul_eq_zero'.2 $ or.inr rfl,
  zero_mul := λ a, mul_eq_zero'.2 $ or.inl rfl,
  ..ordinal.monoid }

instance : no_zero_divisors ordinal :=
⟨λ a b, mul_eq_zero'.1⟩

@[simp] theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩,
quotient.sound ⟨(rel_iso.preimage equiv.ulift _).trans
 (rel_iso.prod_lex_congr (rel_iso.preimage equiv.ulift _)
   (rel_iso.preimage equiv.ulift _)).symm⟩

@[simp] theorem card_mul (a b) : card (a * b) = card a * card b :=
quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩,
mul_comm (mk β) (mk α)

instance : left_distrib_class ordinal.{u} :=
⟨λ a b c, quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩,
quotient.sound ⟨⟨sum_prod_distrib _ _ _, begin
  rintro ⟨a₁|a₁, a₂⟩ ⟨b₁|b₁, b₂⟩;
  simp only [prod.lex_def,
    sum.lex_inl_inl, sum.lex.sep, sum.lex_inr_inl, sum.lex_inr_inr,
    sum_prod_distrib_apply_left, sum_prod_distrib_apply_right];
  simp only [sum.inl.inj_iff, true_or, false_and, false_or]
end⟩⟩⟩

theorem mul_succ (a b : ordinal) : a * succ b = a * b + a := mul_add_one a b

instance mul_covariant_class_le : covariant_class ordinal.{u} ordinal.{u} (*) (≤) :=
⟨λ c a b, quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩, begin
  resetI,
  refine (rel_embedding.of_monotone (λ a : α × γ, (f a.1, a.2)) (λ a b h, _)).ordinal_type_le,
  clear_,
  cases h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h',
  { exact prod.lex.left _ _ (f.to_rel_embedding.map_rel_iff.2 h') },
  { exact prod.lex.right _ h' }
end⟩

instance mul_swap_covariant_class_le : covariant_class ordinal.{u} ordinal.{u} (swap (*)) (≤) :=
⟨λ c a b, quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩, begin
  resetI,
  refine (rel_embedding.of_monotone (λ a : γ × α, (a.1, f a.2)) (λ a b h, _)).ordinal_type_le,
  cases h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h',
  { exact prod.lex.left _ _ h' },
  { exact prod.lex.right _ (f.to_rel_embedding.map_rel_iff.2 h') }
end⟩

theorem le_mul_left (a : ordinal) {b : ordinal} (hb : 0 < b) : a ≤ a * b :=
by { convert mul_le_mul_left' (one_le_iff_pos.2 hb) a, rw mul_one a }

theorem le_mul_right (a : ordinal) {b : ordinal} (hb : 0 < b) : a ≤ b * a :=
by { convert mul_le_mul_right' (one_le_iff_pos.2 hb) a, rw one_mul a }

private lemma mul_le_of_limit_aux {α β r s} [is_well_order α r] [is_well_order β s]
  {c} (h : is_limit (type s)) (H : ∀ b' < type s, type r * b' ≤ c)
  (l : c < type r * type s) : false :=
begin
  suffices : ∀ a b, prod.lex s r (b, a) (enum _ _ l),
  { cases enum _ _ l with b a, exact irrefl _ (this _ _) },
  intros a b,
  rw [←typein_lt_typein (prod.lex s r), typein_enum],
  have := H _ (h.2 _ (typein_lt_type s b)),
  rw mul_succ at this,
  have := ((add_lt_add_iff_left _).2 (typein_lt_type _ a)).trans_le this,
  refine (rel_embedding.of_monotone (λ a, _) (λ a b, _)).ordinal_type_le.trans_lt this,
  { rcases a with ⟨⟨b', a'⟩, h⟩,
    by_cases e : b = b',
    { refine sum.inr ⟨a', _⟩,
      subst e, cases h with _ _ _ _ h _ _ _ h,
      { exact (irrefl _ h).elim },
      { exact h } },
    { refine sum.inl (⟨b', _⟩, a'),
      cases h with _ _ _ _ h _ _ _ h,
      { exact h }, { exact (e rfl).elim } } },
  { rcases a with ⟨⟨b₁, a₁⟩, h₁⟩,
    rcases b with ⟨⟨b₂, a₂⟩, h₂⟩,
    intro h, by_cases e₁ : b = b₁; by_cases e₂ : b = b₂,
    { substs b₁ b₂,
      simpa only [subrel_val, prod.lex_def, @irrefl _ s _ b, true_and, false_or, eq_self_iff_true,
        dif_pos, sum.lex_inr_inr] using h },
    { subst b₁,
      simp only [subrel_val, prod.lex_def, e₂, prod.lex_def, dif_pos, subrel_val, eq_self_iff_true,
        or_false, dif_neg, not_false_iff, sum.lex_inr_inl, false_and] at h ⊢,
      cases h₂; [exact asymm h h₂_h, exact e₂ rfl] },
    { simp [e₂, dif_neg e₁, show b₂ ≠ b₁, by cc] },
    { simpa only [dif_neg e₁, dif_neg e₂, prod.lex_def, subrel_val, subtype.mk_eq_mk,
        sum.lex_inl_inl] using h } }
end

theorem mul_le_of_limit {a b c : ordinal} (h : is_limit b) : a * b ≤ c ↔ ∀ b' < b, a * b' ≤ c :=
⟨λ h b' l, (mul_le_mul_left' l.le _).trans h,
λ H, le_of_not_lt $ induction_on a (λ α r _, induction_on b $ λ β s _,
  by exactI mul_le_of_limit_aux) h H⟩

theorem mul_is_normal {a : ordinal} (h : 0 < a) : is_normal ((*) a) :=
⟨λ b, by rw mul_succ; simpa only [add_zero] using (add_lt_add_iff_left (a*b)).2 h,
 λ b l c, mul_le_of_limit l⟩

theorem lt_mul_of_limit {a b c : ordinal}
  (h : is_limit c) : a < b * c ↔ ∃ c' < c, a < b * c' :=
by simpa only [not_ball, not_le] using not_congr (@mul_le_of_limit b c a h)

theorem mul_lt_mul_iff_left {a b c : ordinal} (a0 : 0 < a) : a * b < a * c ↔ b < c :=
(mul_is_normal a0).lt_iff

theorem mul_le_mul_iff_left {a b c : ordinal} (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
(mul_is_normal a0).le_iff

theorem mul_lt_mul_of_pos_left {a b c : ordinal}
  (h : a < b) (c0 : 0 < c) : c * a < c * b :=
(mul_lt_mul_iff_left c0).2 h

theorem mul_pos {a b : ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b :=
by simpa only [mul_zero] using mul_lt_mul_of_pos_left h₂ h₁

theorem mul_ne_zero {a b : ordinal} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
by simpa only [ordinal.pos_iff_ne_zero] using mul_pos

theorem le_of_mul_le_mul_left {a b c : ordinal}
  (h : c * a ≤ c * b) (h0 : 0 < c) : a ≤ b :=
le_imp_le_of_lt_imp_lt (λ h', mul_lt_mul_of_pos_left h' h0) h

theorem mul_right_inj {a b c : ordinal} (a0 : 0 < a) : a * b = a * c ↔ b = c :=
(mul_is_normal a0).inj

theorem mul_is_limit {a b : ordinal}
  (a0 : 0 < a) : is_limit b → is_limit (a * b) :=
(mul_is_normal a0).is_limit

theorem mul_is_limit_left {a b : ordinal}
  (l : is_limit a) (b0 : 0 < b) : is_limit (a * b) :=
begin
  rcases zero_or_succ_or_limit b with rfl|⟨b,rfl⟩|lb,
  { exact b0.false.elim },
  { rw mul_succ, exact add_is_limit _ l },
  { exact mul_is_limit l.pos lb }
end

theorem smul_eq_mul : ∀ (n : ℕ) (a : ordinal), n • a = a * n
| 0       a := by rw [zero_smul, nat.cast_zero, mul_zero]
| (n + 1) a := by rw [succ_nsmul', nat.cast_add, mul_add, nat.cast_one, mul_one, smul_eq_mul]

/-! ### Division on ordinals -/

/-- The set in the definition of division is nonempty. -/
theorem div_nonempty {a b : ordinal} (h : b ≠ 0) : {o | a < b * succ o}.nonempty :=
⟨a, succ_le_iff.1 $
  by simpa only [succ_zero, one_mul]
    using mul_le_mul_right' (succ_le_of_lt (ordinal.pos_iff_ne_zero.2 h)) (succ a)⟩

/-- `a / b` is the unique ordinal `o` satisfying `a = b * o + o'` with `o' < b`. -/
instance : has_div ordinal := ⟨λ a b, if h : b = 0 then 0 else Inf {o | a < b * succ o}⟩

@[simp] theorem div_zero (a : ordinal) : a / 0 = 0 :=
dif_pos rfl

lemma div_def (a) {b : ordinal} (h : b ≠ 0) : a / b = Inf {o | a < b * succ o} :=
dif_neg h

theorem lt_mul_succ_div (a) {b : ordinal} (h : b ≠ 0) : a < b * succ (a / b) :=
by rw div_def a h; exact Inf_mem (div_nonempty h)

theorem lt_mul_div_add (a) {b : ordinal} (h : b ≠ 0) : a < b * (a / b) + b :=
by simpa only [mul_succ] using lt_mul_succ_div a h

theorem div_le {a b c : ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b * succ c :=
⟨λ h, (lt_mul_succ_div a b0).trans_le (mul_le_mul_left' (succ_le_succ_iff.2 h) _),
 λ h, by rw div_def a b0; exact cInf_le' h⟩

theorem lt_div {a b c : ordinal} (h : c ≠ 0) : a < b / c ↔ c * succ a ≤ b :=
by rw [← not_le, div_le h, not_lt]

theorem div_pos {b c : ordinal} (h : c ≠ 0) : 0 < b / c ↔ c ≤ b := by simp [lt_div h]

theorem le_div {a b c : ordinal} (c0 : c ≠ 0) :
  a ≤ b / c ↔ c * a ≤ b :=
begin
  apply limit_rec_on a,
  { simp only [mul_zero, ordinal.zero_le] },
  { intros, rw [succ_le_iff, lt_div c0] },
  { simp only [mul_le_of_limit, limit_le, iff_self, forall_true_iff] {contextual := tt} }
end

theorem div_lt {a b c : ordinal} (b0 : b ≠ 0) :
  a / b < c ↔ a < b * c :=
lt_iff_lt_of_le_iff_le $ le_div b0

theorem div_le_of_le_mul {a b c : ordinal} (h : a ≤ b * c) : a / b ≤ c :=
if b0 : b = 0 then by simp only [b0, div_zero, ordinal.zero_le] else
(div_le b0).2 $ h.trans_lt $ mul_lt_mul_of_pos_left (lt_succ c) (ordinal.pos_iff_ne_zero.2 b0)

theorem mul_lt_of_lt_div {a b c : ordinal} : a < b / c → c * a < b :=
lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp] theorem zero_div (a : ordinal) : 0 / a = 0 :=
ordinal.le_zero.1 $ div_le_of_le_mul $ ordinal.zero_le _

theorem mul_div_le (a b : ordinal) : b * (a / b) ≤ a :=
if b0 : b = 0 then by simp only [b0, zero_mul, ordinal.zero_le] else (le_div b0).1 le_rfl

theorem mul_add_div (a) {b : ordinal} (b0 : b ≠ 0) (c) : (b * a + c) / b = a + c / b :=
begin
  apply le_antisymm,
  { apply (div_le b0).2,
    rw [mul_succ, mul_add, add_assoc, add_lt_add_iff_left],
    apply lt_mul_div_add _ b0 },
  { rw [le_div b0, mul_add, add_le_add_iff_left],
    apply mul_div_le }
end

theorem div_eq_zero_of_lt {a b : ordinal} (h : a < b) : a / b = 0 :=
begin
  rw [←ordinal.le_zero, div_le $ ordinal.pos_iff_ne_zero.1 $ (ordinal.zero_le _).trans_lt h],
  simpa only [succ_zero, mul_one] using h
end

@[simp] theorem mul_div_cancel (a) {b : ordinal} (b0 : b ≠ 0) : b * a / b = a :=
by simpa only [add_zero, zero_div] using mul_add_div a b0 0

@[simp] theorem div_one (a : ordinal) : a / 1 = a :=
by simpa only [one_mul] using mul_div_cancel a ordinal.one_ne_zero

@[simp] theorem div_self {a : ordinal} (h : a ≠ 0) : a / a = 1 :=
by simpa only [mul_one] using mul_div_cancel 1 h

theorem mul_sub (a b c : ordinal) : a * (b - c) = a * b - a * c :=
if a0 : a = 0 then by simp only [a0, zero_mul, sub_self] else
eq_of_forall_ge_iff $ λ d,
by rw [sub_le, ← le_div a0, sub_le, ← le_div a0, mul_add_div _ a0]

theorem is_limit_add_iff {a b} : is_limit (a + b) ↔ is_limit b ∨ (b = 0 ∧ is_limit a) :=
begin
  split; intro h,
  { by_cases h' : b = 0,
    { rw [h', add_zero] at h, right, exact ⟨h', h⟩ },
      left, rw [←add_sub_cancel a b], apply sub_is_limit h,
      suffices : a + 0 < a + b, simpa only [add_zero],
      rwa [add_lt_add_iff_left, ordinal.pos_iff_ne_zero] },
  rcases h with h|⟨rfl, h⟩, exact add_is_limit a h, simpa only [add_zero]
end

theorem dvd_add_iff : ∀ {a b c : ordinal}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
| a _ c ⟨b, rfl⟩ :=
 ⟨λ ⟨d, e⟩, ⟨d - b, by rw [mul_sub, ← e, add_sub_cancel]⟩,
  λ ⟨d, e⟩, by { rw [e, ← mul_add], apply dvd_mul_right }⟩

theorem div_mul_cancel : ∀ {a b : ordinal}, a ≠ 0 → a ∣ b → a * (b / a) = b
| a _ a0 ⟨b, rfl⟩ := by rw [mul_div_cancel _ a0]

theorem le_of_dvd : ∀ {a b : ordinal}, b ≠ 0 → a ∣ b → a ≤ b
| a _ b0 ⟨b, rfl⟩ := by simpa only [mul_one] using mul_le_mul_left'
  (one_le_iff_ne_zero.2 (λ h : b = 0, by simpa only [h, mul_zero] using b0)) a

theorem dvd_antisymm {a b : ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
if a0 : a = 0 then by subst a; exact (eq_zero_of_zero_dvd h₁).symm else
if b0 : b = 0 then by subst b; exact eq_zero_of_zero_dvd h₂ else
(le_of_dvd b0 h₁).antisymm (le_of_dvd a0 h₂)

instance : is_antisymm ordinal (∣) := ⟨@dvd_antisymm⟩

/-- `a % b` is the unique ordinal `o'` satisfying
  `a = b * o + o'` with `o' < b`. -/
instance : has_mod ordinal := ⟨λ a b, a - b * (a / b)⟩

theorem mod_def (a b : ordinal) : a % b = a - b * (a / b) := rfl

theorem mod_le (a b : ordinal) : a % b ≤ a := sub_le_self a _

@[simp] theorem mod_zero (a : ordinal) : a % 0 = a :=
by simp only [mod_def, div_zero, zero_mul, sub_zero]

theorem mod_eq_of_lt {a b : ordinal} (h : a < b) : a % b = a :=
by simp only [mod_def, div_eq_zero_of_lt h, mul_zero, sub_zero]

@[simp] theorem zero_mod (b : ordinal) : 0 % b = 0 :=
by simp only [mod_def, zero_div, mul_zero, sub_self]

theorem div_add_mod (a b : ordinal) : b * (a / b) + a % b = a :=
ordinal.add_sub_cancel_of_le $ mul_div_le _ _

theorem mod_lt (a) {b : ordinal} (h : b ≠ 0) : a % b < b :=
(add_lt_add_iff_left (b * (a / b))).1 $
by rw div_add_mod; exact lt_mul_div_add a h

@[simp] theorem mod_self (a : ordinal) : a % a = 0 :=
if a0 : a = 0 then by simp only [a0, zero_mod] else
by simp only [mod_def, div_self a0, mul_one, sub_self]

@[simp] theorem mod_one (a : ordinal) : a % 1 = 0 :=
by simp only [mod_def, div_one, one_mul, sub_self]

theorem dvd_of_mod_eq_zero {a b : ordinal} (H : a % b = 0) : b ∣ a :=
⟨a / b, by simpa [H] using (div_add_mod a b).symm⟩

theorem mod_eq_zero_of_dvd {a b : ordinal} (H : b ∣ a) : a % b = 0 :=
begin
  rcases H with ⟨c, rfl⟩,
  rcases eq_or_ne b 0 with rfl | hb,
  { simp },
  { simp [mod_def, hb] }
end

theorem dvd_iff_mod_eq_zero {a b : ordinal} : b ∣ a ↔ a % b = 0 :=
⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

@[simp] theorem mul_add_mod_self (x y z : ordinal) : (x * y + z) % x = z % x :=
begin
  rcases eq_or_ne x 0 with rfl | hx,
  { simp },
  { rwa [mod_def, mul_add_div, mul_add, ←sub_sub, add_sub_cancel, mod_def] }
end

@[simp] theorem mul_mod (x y : ordinal) : x * y % x = 0 := by simpa using mul_add_mod_self x y 0

theorem mod_mod_of_dvd (a : ordinal) {b c : ordinal} (h : c ∣ b) : a % b % c = a % c :=
begin
  nth_rewrite_rhs 0 ←div_add_mod a b,
  rcases h with ⟨d, rfl⟩,
  rw [mul_assoc, mul_add_mod_self]
end

@[simp] theorem mod_mod (a b : ordinal) : a % b % b = a % b := mod_mod_of_dvd a dvd_rfl

/-! ### Families of ordinals

There are two kinds of indexed families that naturally arise when dealing with ordinals: those
indexed by some type in the appropriate universe, and those indexed by ordinals less than another.
The following API allows one to convert from one kind of family to the other.

In many cases, this makes it easy to prove claims about one kind of family via the corresponding
claim on the other. -/

/-- Converts a family indexed by a `Type u` to one indexed by an `ordinal.{u}` using a specified
well-ordering. -/
def bfamily_of_family' {ι : Type u} (r : ι → ι → Prop) [is_well_order ι r] (f : ι → α) :
  Π a < type r, α :=
λ a ha, f (enum r a ha)

/-- Converts a family indexed by a `Type u` to one indexed by an `ordinal.{u}` using a well-ordering
given by the axiom of choice. -/
def bfamily_of_family {ι : Type u} : (ι → α) → Π a < type (@well_ordering_rel ι), α :=
bfamily_of_family' well_ordering_rel

/-- Converts a family indexed by an `ordinal.{u}` to one indexed by an `Type u` using a specified
well-ordering. -/
def family_of_bfamily' {ι : Type u} (r : ι → ι → Prop) [is_well_order ι r] {o} (ho : type r = o)
  (f : Π a < o, α) : ι → α :=
λ i, f (typein r i) (by { rw ←ho, exact typein_lt_type r i })

/-- Converts a family indexed by an `ordinal.{u}` to one indexed by a `Type u` using a well-ordering
given by the axiom of choice. -/
def family_of_bfamily (o : ordinal) (f : Π a < o, α) : o.out.α → α :=
family_of_bfamily' (<) (type_lt o) f

@[simp] theorem bfamily_of_family'_typein {ι} (r : ι → ι → Prop) [is_well_order ι r] (f : ι → α)
  (i) : bfamily_of_family' r f (typein r i) (typein_lt_type r i) = f i :=
by simp only [bfamily_of_family', enum_typein]

@[simp] theorem bfamily_of_family_typein {ι} (f : ι → α) (i) :
  bfamily_of_family f (typein _ i) (typein_lt_type _ i) = f i :=
bfamily_of_family'_typein  _ f i

@[simp] theorem family_of_bfamily'_enum {ι : Type u} (r : ι → ι → Prop) [is_well_order ι r] {o}
  (ho : type r = o) (f : Π a < o, α) (i hi) :
  family_of_bfamily' r ho f (enum r i (by rwa ho)) = f i hi :=
by simp only [family_of_bfamily', typein_enum]

@[simp] theorem family_of_bfamily_enum (o : ordinal) (f : Π a < o, α) (i hi) :
  family_of_bfamily o f (enum (<) i (by { convert hi, exact type_lt _ })) = f i hi :=
family_of_bfamily'_enum _ (type_lt o) f _ _

/-- The range of a family indexed by ordinals. -/
def brange (o : ordinal) (f : Π a < o, α) : set α :=
{a | ∃ i hi, f i hi = a}

theorem mem_brange {o : ordinal} {f : Π a < o, α} {a} : a ∈ brange o f ↔ ∃ i hi, f i hi = a :=
iff.rfl

theorem mem_brange_self {o} (f : Π a < o, α) (i hi) : f i hi ∈ brange o f :=
⟨i, hi, rfl⟩

@[simp] theorem range_family_of_bfamily' {ι : Type u} (r : ι → ι → Prop) [is_well_order ι r] {o}
  (ho : type r = o) (f : Π a < o, α) : range (family_of_bfamily' r ho f) = brange o f :=
begin
  refine set.ext (λ a, ⟨_, _⟩),
  { rintro ⟨b, rfl⟩,
    apply mem_brange_self },
  { rintro ⟨i, hi, rfl⟩,
    exact ⟨_, family_of_bfamily'_enum _ _ _ _ _⟩ }
end

@[simp] theorem range_family_of_bfamily {o} (f : Π a < o, α) :
  range (family_of_bfamily o f) = brange o f :=
range_family_of_bfamily' _ _ f

@[simp] theorem brange_bfamily_of_family' {ι : Type u} (r : ι → ι → Prop) [is_well_order ι r]
  (f : ι → α) : brange _ (bfamily_of_family' r f) = range f :=
begin
  refine set.ext (λ a, ⟨_, _⟩),
  { rintro ⟨i, hi, rfl⟩,
    apply mem_range_self },
  { rintro ⟨b, rfl⟩,
    exact ⟨_, _, bfamily_of_family'_typein _ _ _⟩ },
end

@[simp] theorem brange_bfamily_of_family {ι : Type u} (f : ι → α) :
  brange _ (bfamily_of_family f) = range f :=
brange_bfamily_of_family' _ _

@[simp] theorem brange_const {o : ordinal} (ho : o ≠ 0) {c : α} : brange o (λ _ _, c) = {c} :=
begin
  rw ←range_family_of_bfamily,
  exact @set.range_const _ o.out.α (out_nonempty_iff_ne_zero.2 ho) c
end

theorem comp_bfamily_of_family' {ι : Type u} (r : ι → ι → Prop) [is_well_order ι r] (f : ι → α)
  (g : α → β) : (λ i hi, g (bfamily_of_family' r f i hi)) = bfamily_of_family' r (g ∘ f) :=
rfl

theorem comp_bfamily_of_family {ι : Type u} (f : ι → α) (g : α → β) :
  (λ i hi, g (bfamily_of_family f i hi)) = bfamily_of_family (g ∘ f) :=
rfl

theorem comp_family_of_bfamily' {ι : Type u} (r : ι → ι → Prop) [is_well_order ι r] {o}
  (ho : type r = o) (f : Π a < o, α) (g : α → β) :
  g ∘ (family_of_bfamily' r ho f) = family_of_bfamily' r ho (λ i hi, g (f i hi)) :=
rfl

theorem comp_family_of_bfamily {o} (f : Π a < o, α) (g : α → β) :
  g ∘ (family_of_bfamily o f) = family_of_bfamily o (λ i hi, g (f i hi)) :=
rfl

/-! ### Supremum of a family of ordinals -/

/-- The supremum of a family of ordinals -/
def sup {ι : Type u} (f : ι → ordinal.{max u v}) : ordinal.{max u v} :=
supr f

@[simp] theorem Sup_eq_sup {ι : Type u} (f : ι → ordinal.{max u v}) : Sup (set.range f) = sup f :=
rfl

/-- The range of an indexed ordinal function, whose outputs live in a higher universe than the
    inputs, is always bounded above. See `ordinal.lsub` for an explicit bound. -/
theorem bdd_above_range {ι : Type u} (f : ι → ordinal.{max u v}) : bdd_above (set.range f) :=
⟨(supr (succ ∘ card ∘ f)).ord, begin
  rintros a ⟨i, rfl⟩,
  exact le_of_lt (cardinal.lt_ord.2 ((lt_succ _).trans_le (le_csupr (bdd_above_range _) _)))
end⟩

theorem le_sup {ι} (f : ι → ordinal) : ∀ i, f i ≤ sup f :=
λ i, le_cSup (bdd_above_range f) (mem_range_self i)

theorem sup_le_iff {ι} {f : ι → ordinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
(cSup_le_iff' (bdd_above_range f)).trans (by simp)

theorem sup_le {ι} {f : ι → ordinal} {a} : (∀ i, f i ≤ a) → sup f ≤ a :=
sup_le_iff.2

theorem lt_sup {ι} {f : ι → ordinal} {a} : a < sup f ↔ ∃ i, a < f i :=
by simpa only [not_forall, not_le] using not_congr (@sup_le_iff _ f a)

theorem ne_sup_iff_lt_sup {ι} {f : ι → ordinal} : (∀ i, f i ≠ sup f) ↔ ∀ i, f i < sup f :=
⟨λ hf _, lt_of_le_of_ne (le_sup _ _) (hf _), λ hf _, ne_of_lt (hf _)⟩

theorem sup_not_succ_of_ne_sup {ι} {f : ι → ordinal} (hf : ∀ i, f i ≠ sup f) {a}
  (hao : a < sup f) : succ a < sup f :=
begin
  by_contra' hoa,
  exact hao.not_le (sup_le $ λ i, le_of_lt_succ $
    (lt_of_le_of_ne (le_sup _ _) (hf i)).trans_le hoa)
end

@[simp] theorem sup_eq_zero_iff {ι} {f : ι → ordinal} : sup f = 0 ↔ ∀ i, f i = 0 :=
begin
  refine ⟨λ h i, _, λ h, le_antisymm
    (sup_le (λ i, ordinal.le_zero.2 (h i))) (ordinal.zero_le _)⟩,
  rw [←ordinal.le_zero, ←h],
  exact le_sup f i
end

theorem is_normal.sup {f} (H : is_normal f) {ι} (g : ι → ordinal) [nonempty ι] :
  f (sup g) = sup (f ∘ g) :=
eq_of_forall_ge_iff $ λ a,
by rw [sup_le_iff, comp, H.le_set' set.univ set.univ_nonempty g]; simp [sup_le_iff]

@[simp] theorem sup_empty {ι} [is_empty ι] (f : ι → ordinal) : sup f = 0 :=
csupr_of_empty f

@[simp] theorem sup_const {ι} [hι : nonempty ι] (o : ordinal) : sup (λ _ : ι, o) = o :=
csupr_const

@[simp] theorem sup_unique {ι} [unique ι] (f : ι → ordinal) : sup f = f default :=
supr_unique

theorem sup_le_of_range_subset {ι ι'} {f : ι → ordinal} {g : ι' → ordinal}
  (h : set.range f ⊆ set.range g) : sup.{u (max v w)} f ≤ sup.{v (max u w)} g :=
sup_le $ λ i, match h (mem_range_self i) with ⟨j, hj⟩ := hj ▸ le_sup _ _ end

theorem sup_eq_of_range_eq {ι ι'} {f : ι → ordinal} {g : ι' → ordinal}
  (h : set.range f = set.range g) : sup.{u (max v w)} f = sup.{v (max u w)} g :=
(sup_le_of_range_subset h.le).antisymm (sup_le_of_range_subset.{v u w} h.ge)

@[simp] theorem sup_sum {α : Type u} {β : Type v} (f : α ⊕ β → ordinal) : sup.{(max u v) w} f =
  max (sup.{u (max v w)} (λ a, f (sum.inl a))) (sup.{v (max u w)} (λ b, f (sum.inr b))) :=
begin
  apply (sup_le_iff.2 _).antisymm (max_le_iff.2 ⟨_, _⟩),
  { rintro (i|i),
    { exact le_max_of_le_left (le_sup _ i) },
    { exact le_max_of_le_right (le_sup _ i) } },
  all_goals
  { apply sup_le_of_range_subset.{_ (max u v) w},
    rintros i ⟨a, rfl⟩,
    apply mem_range_self }
end

lemma unbounded_range_of_sup_ge {α β : Type u} (r : α → α → Prop) [is_well_order α r] (f : β → α)
  (h : type r ≤ sup.{u u} (typein r ∘ f)) : unbounded r (range f) :=
(not_bounded_iff _).1 $ λ ⟨x, hx⟩, not_lt_of_le h $ lt_of_le_of_lt
  (sup_le $ λ y, le_of_lt $ (typein_lt_typein r).2 $ hx _ $ mem_range_self y)
  (typein_lt_type r x)

theorem le_sup_shrink_equiv {s : set ordinal.{u}} (hs : small.{u} s) (a) (ha : a ∈ s) :
  a ≤ sup.{u u} (λ x, ((@equiv_shrink s hs).symm x).val) :=
by { convert le_sup.{u u} _ ((@equiv_shrink s hs) ⟨a, ha⟩), rw symm_apply_apply }

instance small_Iio (o : ordinal.{u}) : small.{u} (set.Iio o) :=
let f : o.out.α → set.Iio o := λ x, ⟨typein (<) x, typein_lt_self x⟩ in
let hf : surjective f := λ b, ⟨enum (<) b.val (by { rw type_lt, exact b.prop }),
  subtype.ext (typein_enum _ _)⟩ in
small_of_surjective hf

instance small_Iic (o : ordinal.{u}) : small.{u} (set.Iic o) :=
by { rw ←Iio_succ, apply_instance }

theorem bdd_above_iff_small {s : set ordinal.{u}} : bdd_above s ↔ small.{u} s :=
⟨λ ⟨a, h⟩, small_subset $ show s ⊆ Iic a, from λ x hx, h hx,
λ h, ⟨sup.{u u} (λ x, ((@equiv_shrink s h).symm x).val), le_sup_shrink_equiv h⟩⟩

theorem bdd_above_of_small (s : set ordinal.{u}) [h : small.{u} s] : bdd_above s :=
bdd_above_iff_small.2 h

theorem sup_eq_Sup {s : set ordinal.{u}} (hs : small.{u} s) :
  sup.{u u} (λ x, (@equiv_shrink s hs).symm x) = Sup s :=
let hs' := bdd_above_iff_small.2 hs in
  ((cSup_le_iff' hs').2 (le_sup_shrink_equiv hs)).antisymm'
  (sup_le (λ x, le_cSup hs' (subtype.mem _)))

theorem Sup_ord {s : set cardinal.{u}} (hs : bdd_above s) : (Sup s).ord = Sup (ord '' s) :=
eq_of_forall_ge_iff $ λ a, begin
  rw [cSup_le_iff' (bdd_above_iff_small.2 (@small_image _ _ _ s
    (cardinal.bdd_above_iff_small.1 hs))), ord_le, cSup_le_iff' hs],
  simp [ord_le]
end

theorem supr_ord {ι} {f : ι → cardinal} (hf : bdd_above (range f)) :
  (supr f).ord = ⨆ i, (f i).ord :=
by { unfold supr, convert Sup_ord hf, rw range_comp }

private theorem sup_le_sup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop)
  [is_well_order ι r] [is_well_order ι' r'] {o} (ho : type r = o) (ho' : type r' = o)
  (f : Π a < o, ordinal) : sup (family_of_bfamily' r ho f) ≤ sup (family_of_bfamily' r' ho' f) :=
sup_le $ λ i, begin
  cases typein_surj r' (by { rw [ho', ←ho], exact typein_lt_type r i }) with j hj,
  simp_rw [family_of_bfamily', ←hj],
  apply le_sup
end

theorem sup_eq_sup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [is_well_order ι r]
  [is_well_order ι' r'] {o : ordinal.{u}} (ho : type r = o) (ho' : type r' = o)
  (f : Π a < o, ordinal.{max u v}) :
  sup (family_of_bfamily' r ho f) = sup (family_of_bfamily' r' ho' f) :=
sup_eq_of_range_eq.{u u v} (by simp)

/-- The supremum of a family of ordinals indexed by the set of ordinals less than some
    `o : ordinal.{u}`. This is a special case of `sup` over the family provided by
    `family_of_bfamily`. -/
def bsup (o : ordinal.{u}) (f : Π a < o, ordinal.{max u v}) : ordinal.{max u v} :=
sup (family_of_bfamily o f)

@[simp] theorem sup_eq_bsup {o} (f : Π a < o, ordinal) : sup (family_of_bfamily o f) = bsup o f :=
rfl

@[simp] theorem sup_eq_bsup' {o ι} (r : ι → ι → Prop) [is_well_order ι r] (ho : type r = o) (f) :
  sup (family_of_bfamily' r ho f) = bsup o f :=
sup_eq_sup r _ ho _ f

@[simp] theorem Sup_eq_bsup {o} (f : Π a < o, ordinal) : Sup (brange o f) = bsup o f :=
by { congr, rw range_family_of_bfamily }

@[simp] theorem bsup_eq_sup' {ι} (r : ι → ι → Prop) [is_well_order ι r] (f : ι → ordinal) :
  bsup _ (bfamily_of_family' r f) = sup f :=
by simp only [←sup_eq_bsup' r, enum_typein, family_of_bfamily', bfamily_of_family']

theorem bsup_eq_bsup {ι : Type u} (r r' : ι → ι → Prop) [is_well_order ι r] [is_well_order ι r']
  (f : ι → ordinal) : bsup _ (bfamily_of_family' r f) = bsup _ (bfamily_of_family' r' f) :=
by rw [bsup_eq_sup', bsup_eq_sup']

@[simp] theorem bsup_eq_sup {ι} (f : ι → ordinal) : bsup _ (bfamily_of_family f) = sup f :=
bsup_eq_sup' _ f

@[congr] lemma bsup_congr {o₁ o₂ : ordinal} (f : Π a < o₁, ordinal) (ho : o₁ = o₂) :
  bsup o₁ f = bsup o₂ (λ a h, f a (h.trans_eq ho.symm)) :=
by subst ho

theorem bsup_le_iff {o f a} : bsup.{u v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
sup_le_iff.trans ⟨λ h i hi, by { rw ←family_of_bfamily_enum o f, exact h _ }, λ h i, h _ _⟩

theorem bsup_le {o : ordinal} {f : Π b < o, ordinal} {a} :
  (∀ i h, f i h ≤ a) → bsup.{u v} o f ≤ a :=
bsup_le_iff.2

theorem le_bsup {o} (f : Π a < o, ordinal) (i h) : f i h ≤ bsup o f :=
bsup_le_iff.1 le_rfl _ _

theorem lt_bsup {o} (f : Π a < o, ordinal) {a} : a < bsup o f ↔ ∃ i hi, a < f i hi :=
by simpa only [not_forall, not_le] using not_congr (@bsup_le_iff _ f a)

theorem is_normal.bsup {f} (H : is_normal f) {o} :
  ∀ (g : Π a < o, ordinal) (h : o ≠ 0), f (bsup o g) = bsup o (λ a h, f (g a h)) :=
induction_on o $ λ α r _ g h, begin
  resetI,
  haveI := type_ne_zero_iff_nonempty.1 h,
  rw [←sup_eq_bsup' r, H.sup, ←sup_eq_bsup' r];
  refl
end

theorem lt_bsup_of_ne_bsup {o : ordinal} {f : Π a < o, ordinal} :
  (∀ i h, f i h ≠ o.bsup f) ↔ ∀ i h, f i h < o.bsup f :=
⟨λ hf _ _, lt_of_le_of_ne (le_bsup _ _ _) (hf _ _), λ hf _ _, ne_of_lt (hf _ _)⟩

theorem bsup_not_succ_of_ne_bsup {o} {f : Π a < o, ordinal}
  (hf : ∀ {i : ordinal} (h : i < o), f i h ≠ o.bsup f) (a) :
  a < bsup o f → succ a < bsup o f :=
by { rw ←sup_eq_bsup at *, exact sup_not_succ_of_ne_sup (λ i, hf _) }

@[simp] theorem bsup_eq_zero_iff {o} {f : Π a < o, ordinal} : bsup o f = 0 ↔ ∀ i hi, f i hi = 0 :=
begin
  refine ⟨λ h i hi, _, λ h, le_antisymm
    (bsup_le (λ i hi, ordinal.le_zero.2 (h i hi))) (ordinal.zero_le _)⟩,
  rw [←ordinal.le_zero, ←h],
  exact le_bsup f i hi,
end

theorem lt_bsup_of_limit {o : ordinal} {f : Π a < o, ordinal}
  (hf : ∀ {a a'} (ha : a < o) (ha' : a' < o), a < a' → f a ha < f a' ha')
  (ho : ∀ a < o, succ a < o) (i h) : f i h < bsup o f :=
(hf _ _ $ lt_succ i).trans_le (le_bsup f (succ i) $ ho _ h)

theorem bsup_succ_of_mono {o : ordinal} {f : Π a < succ o, ordinal}
  (hf : ∀ {i j} hi hj, i ≤ j → f i hi ≤ f j hj) : bsup _ f = f o (lt_succ o) :=
le_antisymm (bsup_le $ λ i hi, hf _ _ $ le_of_lt_succ hi) (le_bsup _ _ _)

@[simp] theorem bsup_zero (f : Π a < (0 : ordinal), ordinal) : bsup 0 f = 0 :=
bsup_eq_zero_iff.2 (λ i hi, (ordinal.not_lt_zero i hi).elim)

theorem bsup_const {o : ordinal} (ho : o ≠ 0) (a : ordinal) : bsup o (λ _ _, a) = a :=
le_antisymm (bsup_le (λ _ _, le_rfl)) (le_bsup _ 0 (ordinal.pos_iff_ne_zero.2 ho))

@[simp] theorem bsup_one (f : Π a < (1 : ordinal), ordinal) : bsup 1 f = f 0 zero_lt_one :=
by simp_rw [←sup_eq_bsup, sup_unique, family_of_bfamily, family_of_bfamily', typein_one_out]

theorem bsup_le_of_brange_subset {o o'} {f : Π a < o, ordinal} {g : Π a < o', ordinal}
  (h : brange o f ⊆ brange o' g) : bsup.{u (max v w)} o f ≤ bsup.{v (max u w)} o' g :=
bsup_le $ λ i hi, begin
  obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩,
  rw ←hj',
  apply le_bsup
end

theorem bsup_eq_of_brange_eq {o o'} {f : Π a < o, ordinal} {g : Π a < o', ordinal}
  (h : brange o f = brange o' g) : bsup.{u (max v w)} o f = bsup.{v (max u w)} o' g :=
(bsup_le_of_brange_subset h.le).antisymm (bsup_le_of_brange_subset.{v u w} h.ge)

/-- The least strict upper bound of a family of ordinals. -/
def lsub {ι} (f : ι → ordinal) : ordinal := sup (succ ∘ f)

@[simp] theorem sup_eq_lsub {ι} (f : ι → ordinal) : sup (succ ∘ f) = lsub f := rfl

theorem lsub_le_iff {ι} {f : ι → ordinal} {a} : lsub f ≤ a ↔ ∀ i, f i < a :=
by { convert sup_le_iff, simp only [succ_le_iff] }

theorem lsub_le {ι} {f : ι → ordinal} {a} : (∀ i, f i < a) → lsub f ≤ a :=
lsub_le_iff.2

theorem lt_lsub {ι} (f : ι → ordinal) (i) : f i < lsub f :=
succ_le_iff.1 (le_sup _ i)

theorem lt_lsub_iff {ι} {f : ι → ordinal} {a} : a < lsub f ↔ ∃ i, a ≤ f i :=
by simpa only [not_forall, not_lt, not_le] using not_congr (@lsub_le_iff _ f a)

theorem sup_le_lsub {ι} (f : ι → ordinal) : sup f ≤ lsub f :=
sup_le $ λ i, (lt_lsub f i).le

theorem lsub_le_sup_succ {ι} (f : ι → ordinal) : lsub f ≤ succ (sup f) :=
lsub_le $ λ i, lt_succ_iff.2 (le_sup f i)

theorem sup_eq_lsub_or_sup_succ_eq_lsub {ι} (f : ι → ordinal) :
  sup f = lsub f ∨ succ (sup f) = lsub f :=
begin
  cases eq_or_lt_of_le (sup_le_lsub f),
  { exact or.inl h },
  { exact or.inr ((succ_le_of_lt h).antisymm (lsub_le_sup_succ f)) }
end

theorem sup_succ_le_lsub {ι} (f : ι → ordinal) : succ (sup f) ≤ lsub f ↔ ∃ i, f i = sup f :=
begin
  refine ⟨λ h, _, _⟩,
  { by_contra' hf,
    exact (succ_le_iff.1 h).ne ((sup_le_lsub f).antisymm
      (lsub_le (ne_sup_iff_lt_sup.1 hf))) },
  rintro ⟨_, hf⟩,
  rw [succ_le_iff, ←hf],
  exact lt_lsub _ _
end

theorem sup_succ_eq_lsub {ι} (f : ι → ordinal) : succ (sup f) = lsub f ↔ ∃ i, f i = sup f :=
(lsub_le_sup_succ f).le_iff_eq.symm.trans (sup_succ_le_lsub f)

theorem sup_eq_lsub_iff_succ {ι} (f : ι → ordinal) :
  sup f = lsub f ↔ ∀ a < lsub f, succ a < lsub f :=
begin
  refine ⟨λ h, _, λ hf, le_antisymm (sup_le_lsub f) (lsub_le (λ i, _))⟩,
  { rw ←h,
    exact λ a, sup_not_succ_of_ne_sup (λ i, (lsub_le_iff.1 (le_of_eq h.symm) i).ne) },
  by_contra' hle,
  have heq := (sup_succ_eq_lsub f).2 ⟨i, le_antisymm (le_sup _ _) hle⟩,
  have := hf _ (by { rw ←heq, exact lt_succ (sup f) }),
  rw heq at this,
  exact this.false
end

theorem sup_eq_lsub_iff_lt_sup {ι} (f : ι → ordinal) : sup f = lsub f ↔ ∀ i, f i < sup f :=
⟨λ h i, (by { rw h, apply lt_lsub }), λ h, le_antisymm (sup_le_lsub f) (lsub_le h)⟩

@[simp] lemma lsub_empty {ι} [h : is_empty ι] (f : ι → ordinal) : lsub f = 0 :=
by { rw [←ordinal.le_zero, lsub_le_iff], exact h.elim }

lemma lsub_pos {ι} [h : nonempty ι] (f : ι → ordinal) : 0 < lsub f :=
h.elim $ λ i, (ordinal.zero_le _).trans_lt (lt_lsub f i)

@[simp] theorem lsub_eq_zero_iff {ι} {f : ι → ordinal} : lsub f = 0 ↔ is_empty ι :=
begin
  refine ⟨λ h, ⟨λ i, _⟩, λ h, @lsub_empty _ h _⟩,
  have := @lsub_pos _ ⟨i⟩ f,
  rw h at this,
  exact this.false
end

@[simp] theorem lsub_const {ι} [hι : nonempty ι] (o : ordinal) : lsub (λ _ : ι, o) = succ o :=
sup_const (succ o)

@[simp] theorem lsub_unique {ι} [hι : unique ι] (f : ι → ordinal) : lsub f = succ (f default) :=
sup_unique _

theorem lsub_le_of_range_subset {ι ι'} {f : ι → ordinal} {g : ι' → ordinal}
  (h : set.range f ⊆ set.range g) : lsub.{u (max v w)} f ≤ lsub.{v (max u w)} g :=
sup_le_of_range_subset (by convert set.image_subset _ h; apply set.range_comp)

theorem lsub_eq_of_range_eq {ι ι'} {f : ι → ordinal} {g : ι' → ordinal}
  (h : set.range f = set.range g) : lsub.{u (max v w)} f = lsub.{v (max u w)} g :=
(lsub_le_of_range_subset h.le).antisymm (lsub_le_of_range_subset.{v u w} h.ge)

@[simp] theorem lsub_sum {α : Type u} {β : Type v} (f : α ⊕ β → ordinal) : lsub.{(max u v) w} f =
  max (lsub.{u (max v w)} (λ a, f (sum.inl a))) (lsub.{v (max u w)} (λ b, f (sum.inr b))) :=
sup_sum _

theorem lsub_not_mem_range {ι} (f : ι → ordinal) : lsub f ∉ set.range f :=
λ ⟨i, h⟩, h.not_lt (lt_lsub f i)

theorem nonempty_compl_range {ι : Type u} (f : ι → ordinal.{max u v}) : (set.range f)ᶜ.nonempty :=
⟨_, lsub_not_mem_range f⟩

@[simp] theorem lsub_typein (o : ordinal) :
  lsub.{u u} (typein ((<) : o.out.α → o.out.α → Prop)) = o :=
(lsub_le.{u u} typein_lt_self).antisymm begin
  by_contra' h,
  nth_rewrite 0 ←type_lt o at h,
  simpa [typein_enum] using lt_lsub.{u u} (typein (<)) (enum (<) _ h)
end

theorem sup_typein_limit {o : ordinal} (ho : ∀ a, a < o → succ a < o) :
  sup.{u u} (typein ((<) : o.out.α → o.out.α → Prop)) = o :=
by rw (sup_eq_lsub_iff_succ.{u u} (typein (<))).2; rwa lsub_typein o

@[simp] theorem sup_typein_succ {o : ordinal} :
  sup.{u u} (typein ((<) : (succ o).out.α → (succ o).out.α → Prop)) = o :=
begin
  cases sup_eq_lsub_or_sup_succ_eq_lsub.{u u}
    (typein ((<) : (succ o).out.α → (succ o).out.α → Prop)) with h h,
  { rw sup_eq_lsub_iff_succ at h,
    simp only [lsub_typein] at h,
    exact (h o (lt_succ o)).false.elim },
  rw [←succ_eq_succ_iff, h],
  apply lsub_typein
end

/-- The least strict upper bound of a family of ordinals indexed by the set of ordinals less than
    some `o : ordinal.{u}`.

    This is to `lsub` as `bsup` is to `sup`. -/
def blsub (o : ordinal.{u}) (f : Π a < o, ordinal.{max u v}) : ordinal.{max u v} :=
o.bsup (λ a ha, succ (f a ha))

@[simp] theorem bsup_eq_blsub (o : ordinal) (f : Π a < o, ordinal) :
  bsup o (λ a ha, succ (f a ha)) = blsub o f :=
rfl

theorem lsub_eq_blsub' {ι} (r : ι → ι → Prop) [is_well_order ι r] {o} (ho : type r = o) (f) :
  lsub (family_of_bfamily' r ho f) = blsub o f :=
sup_eq_bsup' r ho (λ a ha, succ (f a ha))

theorem lsub_eq_lsub {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop)
  [is_well_order ι r] [is_well_order ι' r'] {o} (ho : type r = o) (ho' : type r' = o)
  (f : Π a < o, ordinal) : lsub (family_of_bfamily' r ho f) = lsub (family_of_bfamily' r' ho' f) :=
by rw [lsub_eq_blsub', lsub_eq_blsub']

@[simp] theorem lsub_eq_blsub {o} (f : Π a < o, ordinal) :
  lsub (family_of_bfamily o f) = blsub o f :=
lsub_eq_blsub' _ _ _

@[simp] theorem blsub_eq_lsub' {ι} (r : ι → ι → Prop) [is_well_order ι r] (f : ι → ordinal) :
  blsub _ (bfamily_of_family' r f) = lsub f :=
bsup_eq_sup' r (succ ∘ f)

theorem blsub_eq_blsub {ι : Type u} (r r' : ι → ι → Prop) [is_well_order ι r] [is_well_order ι r']
  (f : ι → ordinal) : blsub _ (bfamily_of_family' r f) = blsub _ (bfamily_of_family' r' f) :=
by rw [blsub_eq_lsub', blsub_eq_lsub']

@[simp] theorem blsub_eq_lsub {ι} (f : ι → ordinal) : blsub _ (bfamily_of_family f) = lsub f :=
blsub_eq_lsub' _ _

@[congr] lemma blsub_congr {o₁ o₂ : ordinal} (f : Π a < o₁, ordinal) (ho : o₁ = o₂) :
  blsub o₁ f = blsub o₂ (λ a h, f a (h.trans_eq ho.symm)) :=
by subst ho

theorem blsub_le_iff {o f a} : blsub o f ≤ a ↔ ∀ i h, f i h < a :=
by { convert bsup_le_iff, simp [succ_le_iff] }

theorem blsub_le {o : ordinal} {f : Π b < o, ordinal} {a} : (∀ i h, f i h < a) → blsub o f ≤ a :=
blsub_le_iff.2

theorem lt_blsub {o} (f : Π a < o, ordinal) (i h) : f i h < blsub o f :=
blsub_le_iff.1 le_rfl _ _

theorem lt_blsub_iff {o f a} : a < blsub o f ↔ ∃ i hi, a ≤ f i hi :=
by simpa only [not_forall, not_lt, not_le] using not_congr (@blsub_le_iff _ f a)

theorem bsup_le_blsub {o} (f : Π a < o, ordinal) : bsup o f ≤ blsub o f :=
bsup_le (λ i h, (lt_blsub f i h).le)

theorem blsub_le_bsup_succ {o} (f : Π a < o, ordinal) : blsub o f ≤ succ (bsup o f) :=
blsub_le (λ i h, lt_succ_iff.2 (le_bsup f i h))

theorem bsup_eq_blsub_or_succ_bsup_eq_blsub {o} (f : Π a < o, ordinal) :
  bsup o f = blsub o f ∨ succ (bsup o f) = blsub o f :=
by { rw [←sup_eq_bsup, ←lsub_eq_blsub], exact sup_eq_lsub_or_sup_succ_eq_lsub _ }

theorem bsup_succ_le_blsub {o} (f : Π a < o, ordinal) :
  succ (bsup o f) ≤ blsub o f ↔ ∃ i hi, f i hi = bsup o f :=
begin
  refine ⟨λ h, _, _⟩,
  { by_contra' hf,
    exact ne_of_lt (succ_le_iff.1 h) (le_antisymm (bsup_le_blsub f)
      (blsub_le (lt_bsup_of_ne_bsup.1 hf))) },
  rintro ⟨_, _, hf⟩,
  rw [succ_le_iff, ←hf],
  exact lt_blsub _ _ _
end

theorem bsup_succ_eq_blsub {o} (f : Π a < o, ordinal) :
  succ (bsup o f) = blsub o f ↔ ∃ i hi, f i hi = bsup o f :=
(blsub_le_bsup_succ f).le_iff_eq.symm.trans (bsup_succ_le_blsub f)

theorem bsup_eq_blsub_iff_succ {o} (f : Π a < o, ordinal) :
  bsup o f = blsub o f ↔ ∀ a < blsub o f, succ a < blsub o f :=
by { rw [←sup_eq_bsup, ←lsub_eq_blsub], apply sup_eq_lsub_iff_succ }

theorem bsup_eq_blsub_iff_lt_bsup {o} (f : Π a < o, ordinal) :
  bsup o f = blsub o f ↔ ∀ i hi, f i hi < bsup o f :=
⟨λ h i, (by { rw h, apply lt_blsub }), λ h, le_antisymm (bsup_le_blsub f) (blsub_le h)⟩

theorem bsup_eq_blsub_of_lt_succ_limit {o} (ho : is_limit o) {f : Π a < o, ordinal}
  (hf : ∀ a ha, f a ha < f (succ a) (ho.2 a ha)) : bsup o f = blsub o f :=
begin
  rw bsup_eq_blsub_iff_lt_bsup,
  exact λ i hi, (hf i hi).trans_le (le_bsup f _ _)
end

theorem blsub_succ_of_mono {o : ordinal} {f : Π a < succ o, ordinal}
  (hf : ∀ {i j} hi hj, i ≤ j → f i hi ≤ f j hj) : blsub _ f = succ (f o (lt_succ o)) :=
bsup_succ_of_mono $ λ i j hi hj h, succ_le_succ (hf hi hj h)

@[simp] theorem blsub_eq_zero_iff {o} {f : Π a < o, ordinal} : blsub o f = 0 ↔ o = 0 :=
by { rw [←lsub_eq_blsub, lsub_eq_zero_iff], exact out_empty_iff_eq_zero }

@[simp] lemma blsub_zero (f : Π a < (0 : ordinal), ordinal) : blsub 0 f = 0 :=
by rwa blsub_eq_zero_iff

lemma blsub_pos {o : ordinal} (ho : 0 < o) (f : Π a < o, ordinal) : 0 < blsub o f :=
(ordinal.zero_le _).trans_lt (lt_blsub f 0 ho)

theorem blsub_type (r : α → α → Prop) [is_well_order α r] (f) :
  blsub (type r) f = lsub (λ a, f (typein r a) (typein_lt_type _ _)) :=
eq_of_forall_ge_iff $ λ o,
by rw [blsub_le_iff, lsub_le_iff]; exact
  ⟨λ H b, H _ _, λ H i h, by simpa only [typein_enum] using H (enum r i h)⟩

theorem blsub_const {o : ordinal} (ho : o ≠ 0) (a : ordinal) : blsub.{u v} o (λ _ _, a) = succ a :=
bsup_const.{u v} ho (succ a)

@[simp] theorem blsub_one (f : Π a < (1 : ordinal), ordinal) : blsub 1 f = succ (f 0 zero_lt_one) :=
bsup_one _

@[simp] theorem blsub_id : ∀ o, blsub.{u u} o (λ x _, x) = o :=
lsub_typein

theorem bsup_id_limit {o : ordinal} : (∀ a < o, succ a < o) → bsup.{u u} o (λ x _, x) = o :=
sup_typein_limit

@[simp] theorem bsup_id_succ (o) : bsup.{u u} (succ o) (λ x _, x) = o :=
sup_typein_succ

theorem blsub_le_of_brange_subset {o o'} {f : Π a < o, ordinal} {g : Π a < o', ordinal}
  (h : brange o f ⊆ brange o' g) : blsub.{u (max v w)} o f ≤ blsub.{v (max u w)} o' g :=
bsup_le_of_brange_subset $ λ a ⟨b, hb, hb'⟩, begin
  obtain ⟨c, hc, hc'⟩ := h ⟨b, hb, rfl⟩,
  simp_rw ←hc' at hb',
  exact ⟨c, hc, hb'⟩
end

theorem blsub_eq_of_brange_eq {o o'} {f : Π a < o, ordinal} {g : Π a < o', ordinal}
  (h : {o | ∃ i hi, f i hi = o} = {o | ∃ i hi, g i hi = o}) :
  blsub.{u (max v w)} o f = blsub.{v (max u w)} o' g :=
(blsub_le_of_brange_subset h.le).antisymm (blsub_le_of_brange_subset.{v u w} h.ge)

theorem bsup_comp {o o' : ordinal} {f : Π a < o, ordinal}
  (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : Π a < o', ordinal} (hg : blsub o' g = o) :
  bsup o' (λ a ha, f (g a ha) (by { rw ←hg, apply lt_blsub })) = bsup o f :=
begin
  apply le_antisymm;
  refine bsup_le (λ i hi, _),
  { apply le_bsup },
  { rw [←hg, lt_blsub_iff] at hi,
    rcases hi with ⟨j, hj, hj'⟩,
    exact (hf _ _ hj').trans (le_bsup _ _ _) }
end

theorem blsub_comp {o o' : ordinal} {f : Π a < o, ordinal}
  (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : Π a < o', ordinal} (hg : blsub o' g = o) :
  blsub o' (λ a ha, f (g a ha) (by { rw ←hg, apply lt_blsub })) = blsub o f :=
@bsup_comp o _ (λ a ha, succ (f a ha)) (λ i j _ _ h, succ_le_succ_iff.2 (hf _ _ h)) g hg

theorem is_normal.bsup_eq {f} (H : is_normal f) {o : ordinal} (h : is_limit o) :
  bsup.{u} o (λ x _, f x) = f o :=
by { rw [←is_normal.bsup.{u u} H (λ x _, x) h.1, bsup_id_limit h.2] }

theorem is_normal.blsub_eq {f} (H : is_normal f) {o : ordinal} (h : is_limit o) :
  blsub.{u} o (λ x _, f x) = f o :=
by { rw [←H.bsup_eq h, bsup_eq_blsub_of_lt_succ_limit h], exact (λ a _, H.1 a) }

theorem is_normal_iff_lt_succ_and_bsup_eq {f} :
  is_normal f ↔ (∀ a, f a < f (succ a)) ∧ ∀ o, is_limit o → bsup o (λ x _, f x) = f o :=
⟨λ h, ⟨h.1, @is_normal.bsup_eq f h⟩, λ ⟨h₁, h₂⟩, ⟨h₁, λ o ho a,
  (by {rw ←h₂ o ho, exact bsup_le_iff})⟩⟩

theorem is_normal_iff_lt_succ_and_blsub_eq {f} :
  is_normal f ↔ (∀ a, f a < f (succ a)) ∧ ∀ o, is_limit o → blsub o (λ x _, f x) = f o :=
begin
  rw [is_normal_iff_lt_succ_and_bsup_eq, and.congr_right_iff],
  intro h,
  split;
  intros H o ho;
  have := H o ho;
  rwa ←bsup_eq_blsub_of_lt_succ_limit ho (λ a _, h a) at *
end

theorem is_normal.eq_iff_zero_and_succ {f g : ordinal.{u} → ordinal.{u}} (hf : is_normal f)
  (hg : is_normal g) : f = g ↔ f 0 = g 0 ∧ ∀ a, f a = g a → f (succ a) = g (succ a) :=
⟨λ h, by simp [h], λ ⟨h₁, h₂⟩, funext (λ a, begin
  apply a.limit_rec_on,
  assumption',
  intros o ho H,
  rw [←is_normal.bsup_eq.{u u} hf ho, ←is_normal.bsup_eq.{u u} hg ho],
  congr,
  ext b hb,
  exact H b hb
end)⟩

/-- A two-argument version of `ordinal.blsub`.

We don't develop a full API for this, since it's only used in a handful of existence results. -/
def blsub₂ (o₁ o₂ : ordinal) (op : Π (a < o₁) (b < o₂), ordinal) : ordinal :=
lsub (λ x : o₁.out.α × o₂.out.α,
  op (typein (<) x.1) (typein_lt_self _) (typein (<) x.2) (typein_lt_self _))

theorem lt_blsub₂ {o₁ o₂ : ordinal} (op : Π (a < o₁) (b < o₂), ordinal) {a b : ordinal}
  (ha : a < o₁) (hb : b < o₂) : op a ha b hb < blsub₂ o₁ o₂ op :=
begin
  convert lt_lsub _ (prod.mk (enum (<) a (by rwa type_lt)) (enum (<) b (by rwa type_lt))),
  simp only [typein_enum]
end

/-! ### Minimum excluded ordinals -/

/-- The minimum excluded ordinal in a family of ordinals. -/
def mex {ι : Type u} (f : ι → ordinal.{max u v}) : ordinal :=
Inf (set.range f)ᶜ

theorem mex_not_mem_range {ι : Type u} (f : ι → ordinal.{max u v}) : mex f ∉ set.range f :=
Inf_mem (nonempty_compl_range f)

theorem le_mex_of_forall {ι : Type u} {f : ι → ordinal.{max u v}} {a : ordinal}
  (H : ∀ b < a, ∃ i, f i = b) : a ≤ mex f :=
by { by_contra' h, exact mex_not_mem_range f (H _ h) }

theorem ne_mex {ι} (f : ι → ordinal) : ∀ i, f i ≠ mex f :=
by simpa using mex_not_mem_range f

theorem mex_le_of_ne {ι} {f : ι → ordinal} {a} (ha : ∀ i, f i ≠ a) : mex f ≤ a :=
cInf_le' (by simp [ha])

theorem exists_of_lt_mex {ι} {f : ι → ordinal} {a} (ha : a < mex f) : ∃ i, f i = a :=
by { by_contra' ha', exact ha.not_le (mex_le_of_ne ha') }

theorem mex_le_lsub {ι} (f : ι → ordinal) : mex f ≤ lsub f :=
cInf_le' (lsub_not_mem_range f)

theorem mex_monotone {α β} {f : α → ordinal} {g : β → ordinal} (h : set.range f ⊆ set.range g) :
  mex f ≤ mex g :=
begin
  refine mex_le_of_ne (λ i hi, _),
  cases h ⟨i, rfl⟩ with j hj,
  rw ←hj at hi,
  exact ne_mex g j hi
end

theorem mex_lt_ord_succ_mk {ι} (f : ι → ordinal) : mex f < (succ (#ι)).ord :=
begin
  by_contra' h,
  apply (lt_succ (#ι)).not_le,
  have H := λ a, exists_of_lt_mex ((typein_lt_self a).trans_le h),
  let g : (succ (#ι)).ord.out.α → ι := λ a, classical.some (H a),
  have hg : injective g := λ a b h', begin
    have Hf : ∀ x, f (g x) = typein (<) x := λ a, classical.some_spec (H a),
    apply_fun f at h',
    rwa [Hf, Hf, typein_inj] at h'
  end,
  convert cardinal.mk_le_of_injective hg,
  rw cardinal.mk_ord_out
end

/-- The minimum excluded ordinal of a family of ordinals indexed by the set of ordinals less than
    some `o : ordinal.{u}`. This is a special case of `mex` over the family provided by
    `family_of_bfamily`.

    This is to `mex` as `bsup` is to `sup`. -/
def bmex (o : ordinal) (f : Π a < o, ordinal) : ordinal :=
mex (family_of_bfamily o f)

theorem bmex_not_mem_brange {o : ordinal} (f : Π a < o, ordinal) : bmex o f ∉ brange o f :=
by { rw ←range_family_of_bfamily, apply mex_not_mem_range }

theorem le_bmex_of_forall {o : ordinal} (f : Π a < o, ordinal) {a : ordinal}
  (H : ∀ b < a, ∃ i hi, f i hi = b) : a ≤ bmex o f :=
by { by_contra' h, exact bmex_not_mem_brange f (H _ h) }

theorem ne_bmex {o : ordinal} (f : Π a < o, ordinal) {i} (hi) : f i hi ≠ bmex o f :=
begin
  convert ne_mex _ (enum (<) i (by rwa type_lt)),
  rw family_of_bfamily_enum
end

theorem bmex_le_of_ne {o : ordinal} {f : Π a < o, ordinal} {a} (ha : ∀ i hi, f i hi ≠ a) :
  bmex o f ≤ a :=
mex_le_of_ne (λ i, ha _ _)

theorem exists_of_lt_bmex {o : ordinal} {f : Π a < o, ordinal} {a} (ha : a < bmex o f) :
  ∃ i hi, f i hi = a :=
begin
  cases exists_of_lt_mex ha with i hi,
  exact ⟨_, typein_lt_self i, hi⟩
end

theorem bmex_le_blsub {o : ordinal} (f : Π a < o, ordinal) : bmex o f ≤ blsub o f :=
mex_le_lsub _

theorem bmex_monotone {o o' : ordinal} {f : Π a < o, ordinal} {g : Π a < o', ordinal}
  (h : brange o f ⊆ brange o' g) : bmex o f ≤ bmex o' g :=
mex_monotone (by rwa [range_family_of_bfamily, range_family_of_bfamily])

theorem bmex_lt_ord_succ_card {o : ordinal} (f : Π a < o, ordinal) :
  bmex o f < (succ o.card).ord :=
by { rw ←mk_ordinal_out, exact (mex_lt_ord_succ_mk (family_of_bfamily o f)) }

end ordinal

/-! ### Results about injectivity and surjectivity -/

lemma not_surjective_of_ordinal {α : Type u} (f : α → ordinal.{u}) : ¬ surjective f :=
λ h, ordinal.lsub_not_mem_range.{u u} f (h _)

lemma not_injective_of_ordinal {α : Type u} (f : ordinal.{u} → α) : ¬ injective f :=
λ h, not_surjective_of_ordinal _ (inv_fun_surjective h)

lemma not_surjective_of_ordinal_of_small {α : Type v} [small.{u} α] (f : α → ordinal.{u}) :
  ¬ surjective f :=
λ h, not_surjective_of_ordinal _ (h.comp (equiv_shrink _).symm.surjective)

lemma not_injective_of_ordinal_of_small {α : Type v} [small.{u} α] (f : ordinal.{u} → α) :
  ¬ injective f :=
λ h, not_injective_of_ordinal _ ((equiv_shrink _).injective.comp h)

/-- The type of ordinals in universe `u` is not `small.{u}`. This is the type-theoretic analog of
the Burali-Forti paradox. -/
theorem not_small_ordinal : ¬ small.{u} ordinal.{max u v} :=
λ h, @not_injective_of_ordinal_of_small _ h _ (λ a b, ordinal.lift_inj.1)

/-! ### Enumerating unbounded sets of ordinals with ordinals -/

namespace ordinal

section

/-- Enumerator function for an unbounded set of ordinals. -/
def enum_ord (S : set ordinal.{u}) : ordinal → ordinal :=
lt_wf.fix (λ o f, Inf (S ∩ set.Ici (blsub.{u u} o f)))

variables {S : set ordinal.{u}}

/-- The equation that characterizes `enum_ord` definitionally. This isn't the nicest expression to
    work with, so consider using `enum_ord_def` instead. -/
theorem enum_ord_def' (o) :
  enum_ord S o = Inf (S ∩ set.Ici (blsub.{u u} o (λ a _, enum_ord S a))) :=
lt_wf.fix_eq _ _

/-- The set in `enum_ord_def'` is nonempty. -/
theorem enum_ord_def'_nonempty (hS : unbounded (<) S) (a) : (S ∩ set.Ici a).nonempty :=
let ⟨b, hb, hb'⟩ := hS a in ⟨b, hb, le_of_not_gt hb'⟩

private theorem enum_ord_mem_aux (hS : unbounded (<) S) (o) :
  (enum_ord S o) ∈ S ∩ set.Ici (blsub.{u u} o (λ c _, enum_ord S c)) :=
by { rw enum_ord_def', exact Inf_mem (enum_ord_def'_nonempty hS _) }

theorem enum_ord_mem (hS : unbounded (<) S) (o) : enum_ord S o ∈ S :=
(enum_ord_mem_aux hS o).left

theorem blsub_le_enum_ord (hS : unbounded (<) S) (o) :
  blsub.{u u} o (λ c _, enum_ord S c) ≤ enum_ord S o :=
(enum_ord_mem_aux hS o).right

theorem enum_ord_strict_mono (hS : unbounded (<) S) : strict_mono (enum_ord S) :=
λ _ _ h, (lt_blsub.{u u} _ _ h).trans_le (blsub_le_enum_ord hS _)

/-- A more workable definition for `enum_ord`. -/
theorem enum_ord_def (o) :
  enum_ord S o = Inf (S ∩ {b | ∀ c, c < o → enum_ord S c < b}) :=
begin
  rw enum_ord_def',
  congr, ext,
  exact ⟨λ h a hao, (lt_blsub.{u u} _ _ hao).trans_le h, blsub_le⟩
end

/-- The set in `enum_ord_def` is nonempty. -/
lemma enum_ord_def_nonempty (hS : unbounded (<) S) {o} :
  {x | x ∈ S ∧ ∀ c, c < o → enum_ord S c < x}.nonempty :=
(⟨_, enum_ord_mem hS o, λ _ b, enum_ord_strict_mono hS b⟩)

@[simp] theorem enum_ord_range {f : ordinal → ordinal} (hf : strict_mono f) :
  enum_ord (range f) = f :=
funext (λ o, begin
  apply ordinal.induction o,
  intros a H,
  rw enum_ord_def a,
  have Hfa : f a ∈ range f ∩ {b | ∀ c, c < a → enum_ord (range f) c < b} :=
    ⟨mem_range_self a, λ b hb, (by {rw H b hb, exact hf hb})⟩,
  refine (cInf_le' Hfa).antisymm ((le_cInf_iff'' ⟨_, Hfa⟩).2 _),
  rintros _ ⟨⟨c, rfl⟩, hc : ∀ b < a, enum_ord (range f) b < f c⟩,
  rw hf.le_iff_le,
  contrapose! hc,
  exact ⟨c, hc, (H c hc).ge⟩,
end)

@[simp] theorem enum_ord_univ : enum_ord set.univ = id :=
by { rw ←range_id, exact enum_ord_range strict_mono_id }

@[simp] theorem enum_ord_zero : enum_ord S 0 = Inf S :=
by { rw enum_ord_def, simp [ordinal.not_lt_zero] }

theorem enum_ord_succ_le {a b} (hS : unbounded (<) S) (ha : a ∈ S) (hb : enum_ord S b < a) :
  enum_ord S (succ b) ≤ a :=
begin
  rw enum_ord_def,
  exact cInf_le' ⟨ha, λ c hc, ((enum_ord_strict_mono hS).monotone (le_of_lt_succ hc)).trans_lt hb⟩
end

theorem enum_ord_le_of_subset {S T : set ordinal} (hS : unbounded (<) S) (hST : S ⊆ T) (a) :
  enum_ord T a ≤ enum_ord S a :=
begin
  apply ordinal.induction a,
  intros b H,
  rw enum_ord_def,
  exact cInf_le' ⟨hST (enum_ord_mem hS b), λ c h, (H c h).trans_lt (enum_ord_strict_mono hS h)⟩
end

theorem enum_ord_surjective (hS : unbounded (<) S) : ∀ s ∈ S, ∃ a, enum_ord S a = s :=
λ s hs, ⟨Sup {a | enum_ord S a ≤ s}, begin
  apply le_antisymm,
  { rw enum_ord_def,
    refine cInf_le' ⟨hs, λ a ha, _⟩,
    have : enum_ord S 0 ≤ s := by { rw enum_ord_zero, exact cInf_le' hs },
    rcases exists_lt_of_lt_cSup (by exact ⟨0, this⟩) ha with ⟨b, hb, hab⟩,
    exact (enum_ord_strict_mono hS hab).trans_le hb },
  { by_contra' h,
    exact (le_cSup ⟨s, λ a,
      (lt_wf.self_le_of_strict_mono (enum_ord_strict_mono hS) a).trans⟩
      (enum_ord_succ_le hS hs h)).not_lt (lt_succ _) }
end⟩

/-- An order isomorphism between an unbounded set of ordinals and the ordinals. -/
def enum_ord_order_iso (hS : unbounded (<) S) : ordinal ≃o S :=
strict_mono.order_iso_of_surjective (λ o, ⟨_, enum_ord_mem hS o⟩) (enum_ord_strict_mono hS)
  (λ s, let ⟨a, ha⟩ := enum_ord_surjective hS s s.prop in ⟨a, subtype.eq ha⟩)

theorem range_enum_ord (hS : unbounded (<) S) : range (enum_ord S) = S :=
by { rw range_eq_iff, exact ⟨enum_ord_mem hS, enum_ord_surjective hS⟩ }

/-- A characterization of `enum_ord`: it is the unique strict monotonic function with range `S`. -/
theorem eq_enum_ord (f : ordinal → ordinal) (hS : unbounded (<) S) :
  strict_mono f ∧ range f = S ↔ f = enum_ord S :=
begin
  split,
  { rintro ⟨h₁, h₂⟩,
    rwa [←lt_wf.eq_strict_mono_iff_eq_range h₁ (enum_ord_strict_mono hS), range_enum_ord hS] },
  { rintro rfl,
    exact ⟨enum_ord_strict_mono hS, range_enum_ord hS⟩ }
end

end


/-! ### Casting naturals into ordinals, compatibility with operations -/

@[simp] theorem one_add_nat_cast (m : ℕ) : 1 + (m : ordinal) = succ m :=
by { rw [←nat.cast_one, ←nat.cast_add, add_comm], refl }

@[simp, norm_cast] theorem nat_cast_mul (m : ℕ) : ∀ n : ℕ, ((m * n : ℕ) : ordinal) = m * n
| 0     := by simp
| (n+1) := by rw [nat.mul_succ, nat.cast_add, nat_cast_mul, nat.cast_succ, mul_add_one]

@[simp, norm_cast] theorem nat_cast_le {m n : ℕ} : (m : ordinal) ≤ n ↔ m ≤ n :=
by rw [←cardinal.ord_nat, ←cardinal.ord_nat, cardinal.ord_le_ord, cardinal.nat_cast_le]

@[simp, norm_cast] theorem nat_cast_lt {m n : ℕ} : (m : ordinal) < n ↔ m < n :=
by simp only [lt_iff_le_not_le, nat_cast_le]

@[simp, norm_cast] theorem nat_cast_inj {m n : ℕ} : (m : ordinal) = n ↔ m = n :=
by simp only [le_antisymm_iff, nat_cast_le]

@[simp, norm_cast] theorem nat_cast_eq_zero {n : ℕ} : (n : ordinal) = 0 ↔ n = 0 :=
@nat_cast_inj n 0

theorem nat_cast_ne_zero {n : ℕ} : (n : ordinal) ≠ 0 ↔ n ≠ 0 :=
not_congr nat_cast_eq_zero

@[simp, norm_cast] theorem nat_cast_pos {n : ℕ} : (0 : ordinal) < n ↔ 0 < n :=
@nat_cast_lt 0 n

@[simp, norm_cast] theorem nat_cast_sub (m n : ℕ) : ((m - n : ℕ) : ordinal) = m - n :=
begin
  cases le_total m n with h h,
  { rw [tsub_eq_zero_iff_le.2 h, ordinal.sub_eq_zero_iff_le.2 (nat_cast_le.2 h)],
    refl },
  { apply (add_left_cancel n).1,
    rw [←nat.cast_add, add_tsub_cancel_of_le h, ordinal.add_sub_cancel_of_le (nat_cast_le.2 h)] }
end

@[simp, norm_cast] theorem nat_cast_div (m n : ℕ) : ((m / n : ℕ) : ordinal) = m / n :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  { have hn' := nat_cast_ne_zero.2 hn,
    apply le_antisymm,
    { rw [le_div hn', ←nat_cast_mul, nat_cast_le, mul_comm],
      apply nat.div_mul_le_self },
    { rw [div_le hn', ←add_one_eq_succ, ←nat.cast_succ, ←nat_cast_mul, nat_cast_lt, mul_comm,
        ←nat.div_lt_iff_lt_mul (nat.pos_of_ne_zero hn)],
      apply nat.lt_succ_self } }
end

@[simp, norm_cast] theorem nat_cast_mod (m n : ℕ) : ((m % n : ℕ) : ordinal) = m % n :=
by rw [←add_left_cancel, div_add_mod, ←nat_cast_div, ←nat_cast_mul, ←nat.cast_add, nat.div_add_mod]

@[simp] theorem lift_nat_cast : ∀ n : ℕ, lift.{u v} n = n
| 0     := by simp
| (n+1) := by simp [lift_nat_cast n]

end ordinal

/-! ### Properties of `omega` -/

namespace cardinal
open ordinal

@[simp] theorem ord_aleph_0 : ord.{u} ℵ₀ = ω :=
le_antisymm (ord_le.2 $ le_rfl) $
le_of_forall_lt $ λ o h, begin
  rcases ordinal.lt_lift_iff.1 h with ⟨o, rfl, h'⟩,
  rw [lt_ord, ←lift_card, lift_lt_aleph_0, ←typein_enum (<) h'],
  exact lt_aleph_0_iff_fintype.2 ⟨set.fintype_lt_nat _⟩
end

@[simp] theorem add_one_of_aleph_0_le {c} (h : ℵ₀ ≤ c) : c + 1 = c :=
begin
  rw [add_comm, ←card_ord c, ←card_one, ←card_add, one_add_of_omega_le],
  rwa [←ord_aleph_0, ord_le_ord]
end

end cardinal

namespace ordinal

theorem lt_add_of_limit {a b c : ordinal.{u}}
  (h : is_limit c) : a < b + c ↔ ∃ c' < c, a < b + c' :=
by rw [←is_normal.bsup_eq.{u u} (add_is_normal b) h, lt_bsup]

theorem lt_omega {o : ordinal} : o < ω ↔ ∃ n : ℕ, o = n :=
by simp_rw [←cardinal.ord_aleph_0, cardinal.lt_ord, lt_aleph_0, card_eq_nat]

theorem nat_lt_omega (n : ℕ) : ↑n < ω :=
lt_omega.2 ⟨_, rfl⟩

theorem omega_pos : 0 < ω := nat_lt_omega 0

theorem omega_ne_zero : ω ≠ 0 := omega_pos.ne'

theorem one_lt_omega : 1 < ω := by simpa only [nat.cast_one] using nat_lt_omega 1

theorem omega_is_limit : is_limit ω :=
⟨omega_ne_zero, λ o h,
  let ⟨n, e⟩ := lt_omega.1 h in
  by rw [e]; exact nat_lt_omega (n+1)⟩

theorem omega_le {o : ordinal} : ω ≤ o ↔ ∀ n : ℕ, ↑n ≤ o :=
⟨λ h n, (nat_lt_omega _).le.trans h,
 λ H, le_of_forall_lt $ λ a h,
   let ⟨n, e⟩ := lt_omega.1 h in
   by rw [e, ←succ_le_iff]; exact H (n+1)⟩

@[simp] theorem sup_nat_cast : sup nat.cast = ω :=
(sup_le $ λ n, (nat_lt_omega n).le).antisymm $ omega_le.2 $ le_sup _

theorem nat_lt_limit {o} (h : is_limit o) : ∀ n : ℕ, ↑n < o
| 0     := lt_of_le_of_ne (ordinal.zero_le o) h.1.symm
| (n+1) := h.2 _ (nat_lt_limit n)

theorem omega_le_of_is_limit {o} (h : is_limit o) : ω ≤ o :=
omega_le.2 $ λ n, le_of_lt $ nat_lt_limit h n

theorem is_limit_iff_omega_dvd {a : ordinal} : is_limit a ↔ a ≠ 0 ∧ ω ∣ a :=
begin
  refine ⟨λ l, ⟨l.1, ⟨a / ω, le_antisymm _ (mul_div_le _ _)⟩⟩, λ h, _⟩,
  { refine (limit_le l).2 (λ x hx, le_of_lt _),
    rw [←div_lt omega_ne_zero, ←succ_le_iff, le_div omega_ne_zero, mul_succ,
      add_le_of_limit omega_is_limit],
    intros b hb,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    exact (add_le_add_right (mul_div_le _ _) _).trans
      (lt_sub.1 $ nat_lt_limit (sub_is_limit l hx) _).le },
  { rcases h with ⟨a0, b, rfl⟩,
    refine mul_is_limit_left omega_is_limit (ordinal.pos_iff_ne_zero.2 $ mt _ a0),
    intro e, simp only [e, mul_zero] }
end

theorem add_mul_limit_aux {a b c : ordinal} (ba : b + a = a)
  (l : is_limit c)
  (IH : ∀ c' < c, (a + b) * succ c' = a * succ c' + b) :
  (a + b) * c = a * c :=
le_antisymm
  ((mul_le_of_limit l).2 $ λ c' h, begin
    apply (mul_le_mul_left' (le_succ c') _).trans,
    rw IH _ h,
    apply (add_le_add_left _ _).trans,
    { rw ← mul_succ, exact mul_le_mul_left' (succ_le_of_lt $ l.2 _ h) _ },
    { apply_instance },
    { rw ← ba, exact le_add_right _ _ }
  end)
  (mul_le_mul_right' (le_add_right _ _) _)

theorem add_mul_succ {a b : ordinal} (c) (ba : b + a = a) :
  (a + b) * succ c = a * succ c + b :=
begin
  apply limit_rec_on c,
  { simp only [succ_zero, mul_one] },
  { intros c IH,
    rw [mul_succ, IH, ← add_assoc, add_assoc _ b, ba, ← mul_succ] },
  { intros c l IH,
    have := add_mul_limit_aux ba l IH,
    rw [mul_succ, add_mul_limit_aux ba l IH, mul_succ, add_assoc] }
end

theorem add_mul_limit {a b c : ordinal} (ba : b + a = a)
  (l : is_limit c) : (a + b) * c = a * c :=
add_mul_limit_aux ba l (λ c' _, add_mul_succ c' ba)

theorem add_le_of_forall_add_lt {a b c : ordinal} (hb : 0 < b) (h : ∀ d < b, a + d < c) :
  a + b ≤ c :=
begin
  have H : a + (c - a) = c := ordinal.add_sub_cancel_of_le (by {rw ←add_zero a, exact (h _ hb).le}),
  rw ←H,
  apply add_le_add_left _ a,
  by_contra' hb,
  exact (h _ hb).ne H
end

theorem is_normal.apply_omega {f : ordinal.{u} → ordinal.{u}} (hf : is_normal f) :
  sup.{0 u} (f ∘ nat.cast) = f ω :=
by rw [←sup_nat_cast, is_normal.sup.{0 u u} hf]

@[simp] theorem sup_add_nat (o : ordinal) : sup (λ n : ℕ, o + n) = o + ω :=
(add_is_normal o).apply_omega

@[simp] theorem sup_mul_nat (o : ordinal) : sup (λ n : ℕ, o * n) = o * ω :=
begin
  rcases eq_zero_or_pos o with rfl | ho,
  { rw zero_mul, exact sup_eq_zero_iff.2 (λ n, zero_mul n) },
  { exact (mul_is_normal ho).apply_omega }
end

end ordinal


variables {α : Type u} {r : α → α → Prop} {a b : α}

namespace acc

/-- The rank of an element `a` accessible under a relation `r` is defined inductively as the
smallest ordinal greater than the ranks of all elements below it (i.e. elements `b` such that
`r b a`). -/
noncomputable def rank (h : acc r a) : ordinal.{u} :=
acc.rec_on h $ λ a h ih, ordinal.sup.{u u} $ λ b : {b // r b a}, order.succ $ ih b b.2

lemma rank_eq (h : acc r a) :
  h.rank = ordinal.sup.{u u} (λ b : {b // r b a}, order.succ (h.inv b.2).rank) :=
by { change (acc.intro a $ λ _, h.inv).rank = _, refl }

/-- if `r a b` then the rank of `a` is less than the rank of `b`. -/
lemma rank_lt_of_rel (hb : acc r b) (h : r a b) : (hb.inv h).rank < hb.rank :=
(order.lt_succ _).trans_le $ by { rw hb.rank_eq, refine le_trans _ (ordinal.le_sup _ ⟨a, h⟩), refl }

end acc

namespace well_founded
variables (hwf : well_founded r)
include hwf

/-- The rank of an element `a` under a well-founded relation `r` is defined inductively as the
smallest ordinal greater than the ranks of all elements below it (i.e. elements `b` such that
`r b a`). -/
noncomputable def rank (a : α) : ordinal.{u} := (hwf.apply a).rank

lemma rank_eq : hwf.rank a = ordinal.sup.{u u} (λ b : {b // r b a}, order.succ $ hwf.rank b) :=
by { rw [rank, acc.rank_eq], refl }

lemma rank_lt_of_rel (h : r a b) : hwf.rank a < hwf.rank b := acc.rank_lt_of_rel _ h

omit hwf

lemma rank_strict_mono [preorder α] [well_founded_lt α] :
  strict_mono (rank $ @is_well_founded.wf α (<) _) :=
λ _ _, rank_lt_of_rel _

lemma rank_strict_anti [preorder α] [well_founded_gt α] :
  strict_anti (rank $ @is_well_founded.wf α (>) _) :=
λ _ _, rank_lt_of_rel $ @is_well_founded.wf α (>) _

end well_founded
