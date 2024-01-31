/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import data.int.modeq
import data.nat.multiplicity
import group_theory.order_of_element
import ring_theory.nilpotent

/-!
# Characteristic of semirings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

universes u v

open finset
open_locale big_operators

variables {R : Type*}

namespace commute
variables [semiring R] {p : ℕ} {x y : R}

protected lemma add_pow_prime_pow_eq (hp : p.prime) (h : commute x y) (n : ℕ) :
  (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n +
    p * ∑ k in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) :=
begin
  transitivity
    x ^ p ^ n + y ^ p ^ n + ∑ k in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k,
  { simp_rw [h.add_pow, ←nat.Ico_zero_eq_range, nat.Ico_succ_right, Icc_eq_cons_Ico (zero_le _),
      finset.sum_cons, Ico_eq_cons_Ioo (pow_pos hp.pos _), finset.sum_cons, tsub_self, tsub_zero,
      pow_zero, nat.choose_zero_right, nat.choose_self, nat.cast_one, mul_one, one_mul,
      ←add_assoc] },
  { congr' 1,
    simp_rw [finset.mul_sum, nat.cast_comm, mul_assoc _ _ (p : R), ←nat.cast_mul],
    refine finset.sum_congr rfl (λ i hi, _),
    rw mem_Ioo at hi,
    rw nat.div_mul_cancel (hp.dvd_choose_pow hi.1.ne' hi.2.ne) },
end

protected lemma add_pow_prime_eq (hp : p.prime) (h : commute x y) :
  (x + y) ^ p = x ^ p + y ^ p +
    p * ∑ k in finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) :=
by simpa using h.add_pow_prime_pow_eq hp 1

protected lemma exists_add_pow_prime_pow_eq (hp : p.prime) (h : commute x y) (n : ℕ) :
  ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * r :=
⟨_, h.add_pow_prime_pow_eq hp n⟩

protected lemma exists_add_pow_prime_eq (hp : p.prime) (h : commute x y) :
  ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * r :=
⟨_, h.add_pow_prime_eq hp⟩

end commute

section comm_semiring
variables [comm_semiring R] {p : ℕ} {x y : R}

lemma add_pow_prime_pow_eq (hp : p.prime) (x y : R) (n : ℕ) :
  (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n +
    p * ∑ k in finset.Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) :=
(commute.all x y).add_pow_prime_pow_eq hp n

lemma add_pow_prime_eq (hp : p.prime) (x y : R) :
  (x + y) ^ p = x ^ p + y ^ p +
    p * ∑ k in finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) :=
(commute.all x y).add_pow_prime_eq hp

lemma exists_add_pow_prime_pow_eq (hp : p.prime) (x y : R) (n : ℕ) :
  ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * r :=
(commute.all x y).exists_add_pow_prime_pow_eq hp n

lemma exists_add_pow_prime_eq (hp : p.prime) (x y : R) :
  ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * r :=
(commute.all x y).exists_add_pow_prime_eq hp

end comm_semiring

variables (R)

/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R.

*Warning*: for a semiring `R`, `char_p R 0` and `char_zero R` need not coincide.
* `char_p R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `char_zero R` requires an injection `ℕ ↪ R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`char_zero {0, 1}` does not hold and yet `char_p {0, 1} 0` does.
This example is formalized in `counterexamples/char_p_zero_ne_char_zero`.
 -/
@[mk_iff]
class char_p [add_monoid_with_one R] (p : ℕ) : Prop :=
(cast_eq_zero_iff [] : ∀ x:ℕ, (x:R) = 0 ↔ p ∣ x)

@[simp]
theorem char_p.cast_eq_zero [add_monoid_with_one R] (p : ℕ) [char_p R p] :
  (p:R) = 0 :=
(char_p.cast_eq_zero_iff R p p).2 (dvd_refl p)

@[simp] lemma char_p.cast_card_eq_zero [add_group_with_one R] [fintype R] :
  (fintype.card R : R) = 0 :=
by rw [← nsmul_one, card_nsmul_eq_zero]

lemma char_p.add_order_of_one (R) [semiring R] : char_p R (add_order_of (1 : R)) :=
⟨λ n, by rw [← nat.smul_one_eq_coe, add_order_of_dvd_iff_nsmul_eq_zero]⟩

lemma char_p.int_cast_eq_zero_iff [add_group_with_one R] (p : ℕ) [char_p R p]
  (a : ℤ) :
  (a : R) = 0 ↔ (p:ℤ) ∣ a :=
begin
  rcases lt_trichotomy a 0 with h|rfl|h,
  { rw [← neg_eq_zero, ← int.cast_neg, ← dvd_neg],
    lift -a to ℕ using neg_nonneg.mpr (le_of_lt h) with b,
    rw [int.cast_coe_nat, char_p.cast_eq_zero_iff R p, int.coe_nat_dvd] },
  { simp only [int.cast_zero, eq_self_iff_true, dvd_zero] },
  { lift a to ℕ using (le_of_lt h) with b,
    rw [int.cast_coe_nat, char_p.cast_eq_zero_iff R p, int.coe_nat_dvd] }
end

lemma char_p.int_cast_eq_int_cast [add_group_with_one R] (p : ℕ) [char_p R p] {a b : ℤ} :
  (a : R) = b ↔ a ≡ b [ZMOD p] :=
by rw [eq_comm, ←sub_eq_zero, ←int.cast_sub, char_p.int_cast_eq_zero_iff R p, int.modeq_iff_dvd]

lemma char_p.nat_cast_eq_nat_cast [add_group_with_one R] (p : ℕ) [char_p R p] {a b : ℕ} :
  (a : R) = b ↔ a ≡ b [MOD p] :=
begin
  rw [←int.cast_coe_nat, ←int.cast_coe_nat b],
  exact (char_p.int_cast_eq_int_cast _ _).trans int.coe_nat_modeq_iff,
end

theorem char_p.eq [add_monoid_with_one R] {p q : ℕ} (c1 : char_p R p) (c2 : char_p R q) :
  p = q :=
nat.dvd_antisymm
  ((char_p.cast_eq_zero_iff R p q).1 (char_p.cast_eq_zero _ _))
  ((char_p.cast_eq_zero_iff R q p).1 (char_p.cast_eq_zero _ _))

instance char_p.of_char_zero [add_monoid_with_one R] [char_zero R] : char_p R 0 :=
⟨λ x, by rw [zero_dvd_iff, ← nat.cast_zero, nat.cast_inj]⟩

theorem char_p.exists [non_assoc_semiring R] : ∃ p, char_p R p :=
by letI := classical.dec_eq R; exact
classical.by_cases
  (assume H : ∀ p:ℕ, (p:R) = 0 → p = 0, ⟨0,
    ⟨λ x, by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; simp⟩⟩⟩)
  (λ H, ⟨nat.find (not_forall.1 H), ⟨λ x,
    ⟨λ H1, nat.dvd_of_mod_eq_zero (by_contradiction $ λ H2,
      nat.find_min (not_forall.1 H)
        (nat.mod_lt x $ nat.pos_of_ne_zero $ not_of_not_imp $
          nat.find_spec (not_forall.1 H))
        (not_imp_of_and_not ⟨by rwa [← nat.mod_add_div x (nat.find (not_forall.1 H)),
          nat.cast_add, nat.cast_mul, of_not_not (not_not_of_not_imp $ nat.find_spec
            (not_forall.1 H)),
          zero_mul, add_zero] at H1, H2⟩)),
    λ H1, by rw [← nat.mul_div_cancel' H1, nat.cast_mul,
      of_not_not (not_not_of_not_imp $ nat.find_spec (not_forall.1 H)), zero_mul]⟩⟩⟩)

theorem char_p.exists_unique [non_assoc_semiring R] : ∃! p, char_p R p :=
let ⟨c, H⟩ := char_p.exists R in ⟨c, H, λ y H2, char_p.eq R H2 H⟩

theorem char_p.congr {R : Type u} [add_monoid_with_one R] {p : ℕ} (q : ℕ) [hq : char_p R q]
  (h : q = p) :
  char_p R p :=
h ▸ hq

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable def ring_char [non_assoc_semiring R] : ℕ :=
classical.some (char_p.exists_unique R)

namespace ring_char
variables [non_assoc_semiring R]

theorem spec : ∀ x:ℕ, (x:R) = 0 ↔ ring_char R ∣ x :=
by letI := (classical.some_spec (char_p.exists_unique R)).1;
unfold ring_char; exact char_p.cast_eq_zero_iff R (ring_char R)

theorem eq (p : ℕ) [C : char_p R p] : ring_char R = p :=
((classical.some_spec (char_p.exists_unique R)).2 p C).symm

instance char_p : char_p R (ring_char R) :=
⟨spec R⟩

variables {R}

theorem of_eq {p : ℕ} (h : ring_char R = p) : char_p R p :=
char_p.congr (ring_char R) h

theorem eq_iff {p : ℕ} : ring_char R = p ↔ char_p R p :=
⟨of_eq, @eq R _ p⟩

theorem dvd {x : ℕ} (hx : (x : R) = 0) : ring_char R ∣ x :=
(spec R x).1 hx

@[simp]
lemma eq_zero [char_zero R] : ring_char R = 0 := eq R 0

@[simp]
lemma nat.cast_ring_char : (ring_char R : R) = 0 :=
by rw ring_char.spec

end ring_char

theorem add_pow_char_of_commute [semiring R] {p : ℕ} [hp : fact p.prime]
  [char_p R p] (x y : R) (h : commute x y) :
  (x + y)^p = x^p + y^p :=
let ⟨r, hr⟩ := h.exists_add_pow_prime_eq hp.out in by simp [hr]

theorem add_pow_char_pow_of_commute [semiring R] {p n : ℕ} [hp : fact p.prime] [char_p R p]
  (x y : R) (h : commute x y) :
  (x + y) ^ (p ^ n) = x ^ (p ^ n) + y ^ (p ^ n) :=
let ⟨r, hr⟩ := h.exists_add_pow_prime_pow_eq hp.out n in by simp [hr]

theorem sub_pow_char_of_commute [ring R] {p : ℕ} [fact p.prime]
  [char_p R p] (x y : R) (h : commute x y) :
  (x - y)^p = x^p - y^p :=
begin
  rw [eq_sub_iff_add_eq, ← add_pow_char_of_commute _ _ _ (commute.sub_left h rfl)],
  simp, repeat {apply_instance},
end

theorem sub_pow_char_pow_of_commute [ring R] {p : ℕ} [fact p.prime]
  [char_p R p] {n : ℕ} (x y : R) (h : commute x y) :
  (x - y) ^ (p ^ n) = x ^ (p ^ n) - y ^ (p ^ n) :=
begin
  induction n, { simp, },
  rw [pow_succ', pow_mul, pow_mul, pow_mul, n_ih],
  apply sub_pow_char_of_commute, apply commute.pow_pow h,
end

theorem add_pow_char [comm_semiring R] {p : ℕ} [fact p.prime]
  [char_p R p] (x y : R) : (x + y)^p = x^p + y^p :=
add_pow_char_of_commute _ _ _ (commute.all _ _)

theorem add_pow_char_pow [comm_semiring R] {p : ℕ} [fact p.prime]
  [char_p R p] {n : ℕ} (x y : R) :
  (x + y) ^ (p ^ n) = x ^ (p ^ n) + y ^ (p ^ n) :=
add_pow_char_pow_of_commute _ _ _ (commute.all _ _)

theorem sub_pow_char [comm_ring R] {p : ℕ} [fact p.prime]
  [char_p R p] (x y : R) : (x - y)^p = x^p - y^p :=
sub_pow_char_of_commute _ _ _ (commute.all _ _)

theorem sub_pow_char_pow [comm_ring R] {p : ℕ} [fact p.prime]
  [char_p R p] {n : ℕ} (x y : R) :
  (x - y) ^ (p ^ n) = x ^ (p ^ n) - y ^ (p ^ n) :=
sub_pow_char_pow_of_commute _ _ _ (commute.all _ _)

lemma char_p.neg_one_ne_one [ring R] (p : ℕ) [char_p R p] [fact (2 < p)] :
  (-1 : R) ≠ (1 : R) :=
begin
  suffices : (2 : R) ≠ 0,
  { symmetry, rw [ne.def, ← sub_eq_zero, sub_neg_eq_add], exact this },
  assume h,
  rw [show (2 : R) = (2 : ℕ), by norm_cast] at h,
  have := (char_p.cast_eq_zero_iff R p 2).mp h,
  have := nat.le_of_dvd dec_trivial this,
  rw fact_iff at *, linarith,
end

lemma char_p.neg_one_pow_char [comm_ring R] (p : ℕ) [char_p R p] [fact p.prime] :
  (-1 : R) ^ p = -1 :=
begin
  rw eq_neg_iff_add_eq_zero,
  nth_rewrite 1 ← one_pow p,
  rw [← add_pow_char, add_left_neg, zero_pow (fact.out (nat.prime p)).pos],
end

lemma char_p.neg_one_pow_char_pow [comm_ring R] (p n : ℕ) [char_p R p] [fact p.prime] :
  (-1 : R) ^ p ^ n = -1 :=
begin
  rw eq_neg_iff_add_eq_zero,
  nth_rewrite 1 ← one_pow (p ^ n),
  rw [← add_pow_char_pow, add_left_neg, zero_pow (pow_pos (fact.out (nat.prime p)).pos _)],
end

lemma ring_hom.char_p_iff_char_p {K L : Type*} [division_ring K] [semiring L] [nontrivial L]
  (f : K →+* L) (p : ℕ) :
  char_p K p ↔ char_p L p :=
by simp only [char_p_iff, ← f.injective.eq_iff, map_nat_cast f, f.map_zero]

section frobenius

section comm_semiring

variables [comm_semiring R] {S : Type v} [comm_semiring S] (f : R →* S) (g : R →+* S)
  (p : ℕ) [fact p.prime] [char_p R p] [char_p S p] (x y : R)

/-- The frobenius map that sends x to x^p -/
def frobenius : R →+* R :=
{ to_fun := λ x, x^p,
  map_one' := one_pow p,
  map_mul' := λ x y, mul_pow x y p,
  map_zero' := zero_pow (fact.out (nat.prime p)).pos,
  map_add' := add_pow_char R }

variable {R}

theorem frobenius_def : frobenius R p x = x ^ p := rfl

theorem iterate_frobenius (n : ℕ) : (frobenius R p)^[n] x = x ^ p ^ n :=
begin
  induction n, {simp},
  rw [function.iterate_succ', pow_succ', pow_mul, function.comp_apply, frobenius_def, n_ih]
end

theorem frobenius_mul : frobenius R p (x * y) = frobenius R p x * frobenius R p y :=
(frobenius R p).map_mul x y

theorem frobenius_one : frobenius R p 1 = 1 := one_pow _

theorem monoid_hom.map_frobenius : f (frobenius R p x) = frobenius S p (f x) :=
f.map_pow x p

theorem ring_hom.map_frobenius : g (frobenius R p x) = frobenius S p (g x) :=
g.map_pow x p

theorem monoid_hom.map_iterate_frobenius (n : ℕ) :
  f (frobenius R p^[n] x) = (frobenius S p^[n] (f x)) :=
function.semiconj.iterate_right (f.map_frobenius p) n x

theorem ring_hom.map_iterate_frobenius (n : ℕ) :
  g (frobenius R p^[n] x) = (frobenius S p^[n] (g x)) :=
g.to_monoid_hom.map_iterate_frobenius p x n

theorem monoid_hom.iterate_map_frobenius (f : R →* R) (p : ℕ) [fact p.prime] [char_p R p] (n : ℕ) :
  f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
f.iterate_map_pow _ _ _

theorem ring_hom.iterate_map_frobenius (f : R →+* R) (p : ℕ) [fact p.prime] [char_p R p] (n : ℕ) :
  f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
f.iterate_map_pow _ _ _

variable (R)

theorem frobenius_zero : frobenius R p 0 = 0 := (frobenius R p).map_zero

theorem frobenius_add : frobenius R p (x + y) = frobenius R p x + frobenius R p y :=
(frobenius R p).map_add x y

theorem frobenius_nat_cast (n : ℕ) : frobenius R p n = n := map_nat_cast (frobenius R p) n

open_locale big_operators
variables {R}

lemma list_sum_pow_char (l : list R) : l.sum ^ p = (l.map (^ p)).sum :=
(frobenius R p).map_list_sum _

lemma multiset_sum_pow_char (s : multiset R) : s.sum ^ p = (s.map (^ p)).sum :=
(frobenius R p).map_multiset_sum _

lemma sum_pow_char {ι : Type*} (s : finset ι) (f : ι → R) :
  (∑ i in s, f i) ^ p = ∑ i in s, f i ^ p :=
(frobenius R p).map_sum _ _

end comm_semiring

section comm_ring

variables [comm_ring R] {S : Type v} [comm_ring S] (f : R →* S) (g : R →+* S)
  (p : ℕ) [fact p.prime] [char_p R p]  [char_p S p] (x y : R)

theorem frobenius_neg : frobenius R p (-x) = -frobenius R p x := (frobenius R p).map_neg x

theorem frobenius_sub : frobenius R p (x - y) = frobenius R p x - frobenius R p y :=
(frobenius R p).map_sub x y

end comm_ring

end frobenius

theorem frobenius_inj [comm_ring R] [is_reduced R]
  (p : ℕ) [fact p.prime] [char_p R p] :
  function.injective (frobenius R p) :=
λ x h H, by { rw ← sub_eq_zero at H ⊢, rw ← frobenius_sub at H, exact is_reduced.eq_zero _ ⟨_,H⟩ }

/-- If `ring_char R = 2`, where `R` is a finite reduced commutative ring,
then every `a : R` is a square. -/
lemma is_square_of_char_two' {R : Type*} [finite R] [comm_ring R] [is_reduced R] [char_p R 2]
 (a : R) : is_square a :=
by { casesI nonempty_fintype R, exact exists_imp_exists (λ b h, pow_two b ▸ eq.symm h)
  (((fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).surjective a) }

namespace char_p

section
variables [non_assoc_ring R]

lemma char_p_to_char_zero (R : Type*) [add_group_with_one R] [char_p R 0] :
  char_zero R :=
char_zero_of_inj_zero $
  λ n h0, eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)

lemma cast_eq_mod (p : ℕ) [char_p R p] (k : ℕ) : (k : R) = (k % p : ℕ) :=
calc (k : R) = ↑(k % p + p * (k / p)) : by rw [nat.mod_add_div]
         ... = ↑(k % p)               : by simp [cast_eq_zero]

/-- The characteristic of a finite ring cannot be zero. -/
theorem char_ne_zero_of_finite (p : ℕ) [char_p R p] [finite R] : p ≠ 0 :=
begin
  unfreezingI { rintro rfl },
  haveI : char_zero R := char_p_to_char_zero R,
  casesI nonempty_fintype R,
  exact absurd nat.cast_injective (not_injective_infinite_finite (coe : ℕ → R))
end

lemma ring_char_ne_zero_of_finite [finite R] : ring_char R ≠ 0 :=
char_ne_zero_of_finite R (ring_char R)

end

section comm_ring

variables [comm_ring R] [is_reduced R] {R}

@[simp]
lemma pow_prime_pow_mul_eq_one_iff (p k m : ℕ) [fact p.prime]
  [char_p R p] (x : R) :
  x ^ (p ^ k * m) = 1 ↔ x ^ m = 1 :=
begin
  induction k with k hk,
  { rw [pow_zero, one_mul] },
  { refine ⟨λ h, _, λ h, _⟩,
    { rw [pow_succ, mul_assoc, pow_mul', ← frobenius_def, ← frobenius_one p] at h,
      exact hk.1 (frobenius_inj R p h) },
    { rw [pow_mul', h, one_pow] } }
end

end comm_ring

section semiring
open nat

variables [non_assoc_semiring R]

theorem char_ne_one [nontrivial R] (p : ℕ) [hc : char_p R p] : p ≠ 1 :=
assume hp : p = 1,
have ( 1 : R) = 0, by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p),
absurd this one_ne_zero

section no_zero_divisors

variable [no_zero_divisors R]

theorem char_is_prime_of_two_le (p : ℕ) [hc : char_p R p] (hp : 2 ≤ p) : nat.prime p :=
suffices ∀d ∣ p, d = 1 ∨ d = p, from nat.prime_def_lt''.mpr ⟨hp, this⟩,
assume (d : ℕ) (hdvd : ∃ e, p = d * e),
let ⟨e, hmul⟩ := hdvd in
have (p : R) = 0, from (cast_eq_zero_iff R p p).mpr (dvd_refl p),
have (d : R) * e = 0, from (@cast_mul R _ d e) ▸ (hmul ▸ this),
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
  (assume hd : (d : R) = 0,
  have p ∣ d, from (cast_eq_zero_iff R p d).mp hd,
  show d = 1 ∨ d = p, from or.inr (dvd_antisymm ⟨e, hmul⟩ this))
  (assume he : (e : R) = 0,
  have p ∣ e, from (cast_eq_zero_iff R p e).mp he,
  have e ∣ p, from dvd_of_mul_left_eq d (eq.symm hmul),
  have e = p, from dvd_antisymm ‹e ∣ p› ‹p ∣ e›,
  have h₀ : 0 < p, from two_pos.trans_le hp,
  have d * p = 1 * p, by rw ‹e = p› at hmul; rw [one_mul]; exact eq.symm hmul,
  show d = 1 ∨ d = p, from or.inl (mul_right_cancel₀ h₀.ne' this))

section nontrivial

variables [nontrivial R]

theorem char_is_prime_or_zero (p : ℕ) [hc : char_p R p] : nat.prime p ∨ p = 0 :=
match p, hc with
| 0,     _  := or.inr rfl
| 1,     hc := absurd (eq.refl (1 : ℕ)) (@char_ne_one R _ _ (1 : ℕ) hc)
| (m+2), hc := or.inl (@char_is_prime_of_two_le R _ _ (m+2) hc (nat.le_add_left 2 m))
end

lemma char_is_prime_of_pos (p : ℕ) [ne_zero p] [char_p R p] : fact p.prime :=
⟨(char_p.char_is_prime_or_zero R _).resolve_right $ ne_zero.ne p⟩

end nontrivial

end no_zero_divisors

end semiring

section ring

variables (R) [ring R] [no_zero_divisors R] [nontrivial R] [finite R]

theorem char_is_prime (p : ℕ) [char_p R p] :
  p.prime :=
or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_finite R p)

end ring

section char_one

variables {R} [non_assoc_semiring R]

@[priority 100]  -- see Note [lower instance priority]
instance [char_p R 1] : subsingleton R :=
subsingleton.intro $
suffices ∀ (r : R), r = 0,
  from assume a b, show a = b, by rw [this a, this b],
assume r,
calc r = 1 * r       : by rw one_mul
   ... = (1 : ℕ) * r : by rw nat.cast_one
   ... = 0 * r       : by rw char_p.cast_eq_zero
   ... = 0           : by rw zero_mul

lemma false_of_nontrivial_of_char_one [nontrivial R] [char_p R 1] : false :=
false_of_nontrivial_of_subsingleton R

lemma ring_char_ne_one [nontrivial R] : ring_char R ≠ 1 :=
by { intros h, apply zero_ne_one' R, symmetry, rw [←nat.cast_one, ring_char.spec, h], }

lemma nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : char_p R v] :
  nontrivial R :=
⟨⟨(1 : ℕ), 0, λ h, hv $ by rwa [char_p.cast_eq_zero_iff _ v, nat.dvd_one] at h; assumption ⟩⟩

lemma ring_char_of_prime_eq_zero [nontrivial R] {p : ℕ}
  (hprime : nat.prime p) (hp0 : (p : R) = 0) : ring_char R = p :=
or.resolve_left ((nat.dvd_prime hprime).1 (ring_char.dvd hp0)) ring_char_ne_one

end char_one

end char_p

section

/-- We have `2 ≠ 0` in a nontrivial ring whose characteristic is not `2`. -/
@[protected]
lemma ring.two_ne_zero {R : Type*} [non_assoc_semiring R] [nontrivial R] (hR : ring_char R ≠ 2) :
  (2 : R) ≠ 0 :=
begin
  rw [ne.def, (by norm_cast : (2 : R) = (2 : ℕ)), ring_char.spec, nat.dvd_prime nat.prime_two],
  exact mt (or_iff_left hR).mp char_p.ring_char_ne_one,
end

/-- Characteristic `≠ 2` and nontrivial implies that `-1 ≠ 1`. -/
-- We have `char_p.neg_one_ne_one`, which assumes `[ring R] (p : ℕ) [char_p R p] [fact (2 < p)]`.
-- This is a version using `ring_char` instead.
lemma ring.neg_one_ne_one_of_char_ne_two {R : Type*} [non_assoc_ring R] [nontrivial R]
 (hR : ring_char R ≠ 2) :
  (-1 : R) ≠ 1 :=
λ h, ring.two_ne_zero hR (neg_eq_iff_add_eq_zero.mp h)

/-- Characteristic `≠ 2` in a domain implies that `-a = a` iff `a = 0`. -/
lemma ring.eq_self_iff_eq_zero_of_char_ne_two {R : Type*} [non_assoc_ring R] [nontrivial R]
 [no_zero_divisors R] (hR : ring_char R ≠ 2) {a : R} :
  -a = a ↔ a = 0 :=
⟨λ h, (mul_eq_zero.mp $ (two_mul a).trans $ neg_eq_iff_add_eq_zero.mp h).resolve_left
         (ring.two_ne_zero hR),
 λ h, ((congr_arg (λ x, - x) h).trans neg_zero).trans h.symm⟩

end

section

variables (R) [non_assoc_ring R] [fintype R] (n : ℕ)

lemma char_p_of_ne_zero (hn : fintype.card R = n) (hR : ∀ i < n, (i : R) = 0 → i = 0) :
  char_p R n :=
{ cast_eq_zero_iff :=
  begin
    have H : (n : R) = 0, by { rw [← hn, char_p.cast_card_eq_zero] },
    intro k,
    split,
    { intro h,
      rw [← nat.mod_add_div k n, nat.cast_add, nat.cast_mul, H, zero_mul, add_zero] at h,
      rw nat.dvd_iff_mod_eq_zero,
      apply hR _ (nat.mod_lt _ _) h,
      rw [← hn, fintype.card_pos_iff],
      exact ⟨0⟩, },
    { rintro ⟨k, rfl⟩, rw [nat.cast_mul, H, zero_mul] }
  end }

lemma char_p_of_prime_pow_injective (R) [ring R] [fintype R] (p : ℕ) [hp : fact p.prime] (n : ℕ)
  (hn : fintype.card R = p ^ n) (hR : ∀ i ≤ n, (p ^ i : R) = 0 → i = n) :
  char_p R (p ^ n) :=
begin
  obtain ⟨c, hc⟩ := char_p.exists R, resetI,
  have hcpn : c ∣ p ^ n,
  { rw [← char_p.cast_eq_zero_iff R c, ← hn, char_p.cast_card_eq_zero], },
  obtain ⟨i, hi, hc⟩ : ∃ i ≤ n, c = p ^ i, by rwa nat.dvd_prime_pow hp.1 at hcpn,
  obtain rfl : i = n,
  { apply hR i hi, rw [← nat.cast_pow, ← hc, char_p.cast_eq_zero] },
  rwa ← hc
end

end

section prod

variables (S : Type v) [add_monoid_with_one R] [add_monoid_with_one S] (p q : ℕ) [char_p R p]

/-- The characteristic of the product of rings is the least common multiple of the
characteristics of the two rings. -/
instance [char_p S q] : char_p (R × S) (nat.lcm p q) :=
{ cast_eq_zero_iff :=
    by simp [prod.ext_iff, char_p.cast_eq_zero_iff R p,
      char_p.cast_eq_zero_iff S q, nat.lcm_dvd_iff] }

/-- The characteristic of the product of two rings of the same characteristic
  is the same as the characteristic of the rings -/
instance prod.char_p [char_p S p] : char_p (R × S) p :=
by convert nat.lcm.char_p R S p p; simp

end prod

instance ulift.char_p [add_monoid_with_one R] (p : ℕ) [char_p R p] : char_p (ulift.{v} R) p :=
{ cast_eq_zero_iff := λ n, iff.trans (ulift.ext_iff _ _) $ char_p.cast_eq_zero_iff R p n }

instance mul_opposite.char_p [add_monoid_with_one R] (p : ℕ) [char_p R p] : char_p (Rᵐᵒᵖ) p :=
{ cast_eq_zero_iff := λ n, mul_opposite.unop_inj.symm.trans  $ char_p.cast_eq_zero_iff R p n }

section

/-- If two integers from `{0, 1, -1}` result in equal elements in a ring `R`
that is nontrivial and of characteristic not `2`, then they are equal. -/
lemma int.cast_inj_on_of_ring_char_ne_two {R : Type*} [non_assoc_ring R] [nontrivial R]
  (hR : ring_char R ≠ 2) :
  ({0, 1, -1} : set ℤ).inj_on (coe : ℤ → R) :=
begin
  intros a ha b hb h,
  apply eq_of_sub_eq_zero,
  by_contra hf,
  change a = 0 ∨ a = 1 ∨ a = -1 at ha,
  change b = 0 ∨ b = 1 ∨ b = -1 at hb,
  have hh : a - b = 1 ∨ b - a = 1 ∨ a - b = 2 ∨ b - a = 2 := by
  { rcases ha with ha | ha | ha; rcases hb with hb | hb | hb,
    swap 5, swap 9, -- move goals with `a = b` to the front
    iterate 3 { rw [ha, hb, sub_self] at hf, tauto, }, -- 6 goals remain
    all_goals { rw [ha, hb], norm_num, }, },
  have h' : ((a - b : ℤ) : R) = 0 := by exact_mod_cast sub_eq_zero_of_eq h,
  have h'' : ((b - a : ℤ) : R) = 0 := by exact_mod_cast sub_eq_zero_of_eq h.symm,
  rcases hh with hh | hh | hh | hh,
  { rw [hh, (by norm_cast : ((1 : ℤ) : R) = 1)] at h', exact one_ne_zero h', },
  { rw [hh, (by norm_cast : ((1 : ℤ) : R) = 1)] at h'', exact one_ne_zero h'', },
  { rw [hh, (by norm_cast : ((2 : ℤ) : R) = 2)] at h', exact ring.two_ne_zero hR h', },
  { rw [hh, (by norm_cast : ((2 : ℤ) : R) = 2)] at h'', exact ring.two_ne_zero hR h'', },
end

end

namespace ne_zero

variables (R) [add_monoid_with_one R] {r : R} {n p : ℕ} {a : ℕ+}

lemma of_not_dvd [char_p R p] (h : ¬ p ∣ n) : ne_zero (n : R) :=
⟨(char_p.cast_eq_zero_iff R p n).not.mpr h⟩

lemma not_char_dvd  (p : ℕ) [char_p R p] (k : ℕ) [h : ne_zero (k : R)] : ¬ p ∣ k :=
by rwa [←char_p.cast_eq_zero_iff R p k, ←ne.def, ←ne_zero_iff]

end ne_zero
