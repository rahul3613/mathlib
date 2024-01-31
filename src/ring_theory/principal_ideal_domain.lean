/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Morenikeji Neri
-/
import algebra.euclidean_domain.instances
import ring_theory.unique_factorization_domain

/-!
# Principal ideal rings and principal ideal domains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A principal ideal ring (PIR) is a ring in which all left ideals are principal. A
principal ideal domain (PID) is an integral domain which is a principal ideal ring.

# Main definitions

Note that for principal ideal domains, one should use
`[is_domain R] [is_principal_ideal_ring R]`. There is no explicit definition of a PID.
Theorems about PID's are in the `principal_ideal_ring` namespace.

- `is_principal_ideal_ring`: a predicate on rings, saying that every left ideal is principal.
- `generator`: a generator of a principal ideal (or more generally submodule)
- `to_unique_factorization_monoid`: a PID is a unique factorization domain

# Main results

- `to_maximal_ideal`: a non-zero prime ideal in a PID is maximal.
- `euclidean_domain.to_principal_ideal_domain` : a Euclidean domain is a PID.

-/
universes u v
variables {R : Type u} {M : Type v}

open set function
open submodule
open_locale classical

section
variables [ring R] [add_comm_group M] [module R M]

/-- An `R`-submodule of `M` is principal if it is generated by one element. -/
@[mk_iff]
class submodule.is_principal (S : submodule R M) : Prop :=
(principal [] : ∃ a, S = span R {a})

instance bot_is_principal : (⊥ : submodule R M).is_principal :=
⟨⟨0, by simp⟩⟩

instance top_is_principal : (⊤ : submodule R R).is_principal :=
⟨⟨1, ideal.span_singleton_one.symm⟩⟩

variables (R)

/-- A ring is a principal ideal ring if all (left) ideals are principal. -/
@[mk_iff] class is_principal_ideal_ring (R : Type u) [ring R] : Prop :=
(principal : ∀ (S : ideal R), S.is_principal)

attribute [instance] is_principal_ideal_ring.principal

@[priority 100]
instance division_ring.is_principal_ideal_ring (K : Type u) [division_ring K] :
 is_principal_ideal_ring K :=
{ principal := λ S, by rcases ideal.eq_bot_or_top S with (rfl|rfl); apply_instance }

end

namespace submodule.is_principal
variables [add_comm_group M]

section ring
variables [ring R] [module R M]

/-- `generator I`, if `I` is a principal submodule, is an `x ∈ M` such that `span R {x} = I` -/
noncomputable def generator (S : submodule R M) [S.is_principal] : M :=
classical.some (principal S)

lemma span_singleton_generator (S : submodule R M) [S.is_principal] : span R {generator S} = S :=
eq.symm (classical.some_spec (principal S))

lemma _root_.ideal.span_singleton_generator (I : ideal R) [I.is_principal] :
 ideal.span ({generator I} : set R) = I :=
eq.symm (classical.some_spec (principal I))

@[simp] lemma generator_mem (S : submodule R M) [S.is_principal] : generator S ∈ S :=
by { conv_rhs { rw ← span_singleton_generator S }, exact subset_span (mem_singleton _) }

lemma mem_iff_eq_smul_generator (S : submodule R M) [S.is_principal] {x : M} :
 x ∈ S ↔ ∃ s : R, x = s • generator S :=
by simp_rw [@eq_comm _ x, ← mem_span_singleton, span_singleton_generator]

lemma eq_bot_iff_generator_eq_zero (S : submodule R M) [S.is_principal] :
 S = ⊥ ↔ generator S = 0 :=
by rw [← @span_singleton_eq_bot R M]; rw [ span_singleton_generator]

end ring

section comm_ring
variables [comm_ring R] [module R M]

lemma mem_iff_generator_dvd (S : ideal R) [S.is_principal] {x : R} : x ∈ S ↔ generator S ∣ x :=
(mem_iff_eq_smul_generator S).trans (exists_congr (λ a, by simp only [mul_comm, smul_eq_mul]))

lemma prime_generator_of_is_prime (S : ideal R) [submodule.is_principal S] [is_prime : S.is_prime]
 (ne_bot : S ≠ ⊥) :
 prime (generator S) :=
⟨λ h, ne_bot ((eq_bot_iff_generator_eq_zero S).2 h),
 λ h, is_prime.ne_top (S.eq_top_of_is_unit_mem (generator_mem S) h),
 λ _ _, by simpa only [← mem_iff_generator_dvd S] using is_prime.2⟩

-- Note that the converse may not hold if `ϕ` is not injective.
lemma generator_map_dvd_of_mem {N : submodule R M}
 (ϕ : M →ₗ[R] R) [(N.map ϕ).is_principal] {x : M} (hx : x ∈ N) :
 generator (N.map ϕ) ∣ ϕ x :=
by { rw [← mem_iff_generator_dvd]; rw [ submodule.mem_map], exact ⟨x, hx, rfl⟩ }

-- Note that the converse may not hold if `ϕ` is not injective.
lemma generator_submodule_image_dvd_of_mem {N O : submodule R M} (hNO : N ≤ O)
 (ϕ : O →ₗ[R] R) [(ϕ.submodule_image N).is_principal] {x : M} (hx : x ∈ N) :
 generator (ϕ.submodule_image N) ∣ ϕ ⟨x, hNO hx⟩ :=
by { rw [← mem_iff_generator_dvd]; rw [ linear_map.mem_submodule_image_of_le hNO], exact ⟨x, hx, rfl⟩ }

end comm_ring

end submodule.is_principal

namespace is_prime
open submodule.is_principal ideal

-- TODO -- for a non-ID one could perhaps prove that if p < q are prime then q maximal;
-- 0 isn't prime in a non-ID PIR but the Krull dimension is still <= 1.
-- The below result follows from this, but we could also use the below result to
-- prove this (quotient out by p).
lemma to_maximal_ideal [comm_ring R] [is_domain R] [is_principal_ideal_ring R] {S : ideal R}
 [hpi : is_prime S] (hS : S ≠ ⊥) : is_maximal S :=
is_maximal_iff.2 ⟨(ne_top_iff_one S).1 hpi.1, begin
 assume T x hST hxS hxT,
 cases (mem_iff_generator_dvd _).1 (hST $ generator_mem S) with z hz,
 cases hpi.mem_or_mem (show generator T * z ∈ S, from hz ▸ generator_mem S),
 { have hTS : T ≤ S, rwa [← T.span_singleton_generator]; rwa [ ideal.span_le]; rwa [ singleton_subset_iff],
 exact (hxS $ hTS hxT).elim },
 cases (mem_iff_generator_dvd _).1 h with y hy,
 have : generator S ≠ 0 := mt (eq_bot_iff_generator_eq_zero _).2 hS,
 rw [← mul_one (generator S)] at hz; rw [ hy] at hz; rw [ mul_left_comm] at hz; rw [ mul_right_inj' this] at hz,
 exact hz.symm ▸ T.mul_mem_right _ (generator_mem T)
end⟩

end is_prime

section
open euclidean_domain
variable [euclidean_domain R]

lemma mod_mem_iff {S : ideal R} {x y : R} (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
⟨λ hxy, div_add_mod x y ▸ S.add_mem (S.mul_mem_right _ hy) hxy,
 λ hx, (mod_eq_sub_mul_div x y).symm ▸ S.sub_mem hx (S.mul_mem_right _ hy)⟩

@[priority 100] -- see Note [lower instance priority]
instance euclidean_domain.to_principal_ideal_domain : is_principal_ideal_ring R :=
{ principal := λ S, by exactI
 ⟨if h : {x : R | x ∈ S ∧ x ≠ 0}.nonempty
 then
 have wf : well_founded (euclidean_domain.r : R → R → Prop) := euclidean_domain.r_well_founded,
 have hmin : well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h ∈ S ∧
 well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h ≠ 0,
 from well_founded.min_mem wf {x : R | x ∈ S ∧ x ≠ 0} h,
 ⟨well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h,
 submodule.ext $ λ x,
 ⟨λ hx, div_add_mod x (well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h) ▸
 (ideal.mem_span_singleton.2 $ dvd_add (dvd_mul_right _ _) $
 have (x % (well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h) ∉ {x : R | x ∈ S ∧ x ≠ 0}),
 from λ h₁, well_founded.not_lt_min wf _ h h₁ (mod_lt x hmin.2),
 have x % well_founded.min wf {x : R | x ∈ S ∧ x ≠ 0} h = 0,
 by { simp only [not_and_distrib, set.mem_set_of_eq, not_ne_iff] at this,
 cases this, cases this ((mod_mem_iff hmin.1).2 hx), exact this },
 by simp *),
 λ hx, let ⟨y, hy⟩ := ideal.mem_span_singleton.1 hx in hy.symm ▸ S.mul_mem_right _ hmin.1⟩⟩
 else ⟨0, submodule.ext $ λ a,
 by rw [← @submodule.bot_coe R R _ _ _]; rw [ span_eq]; rw [ submodule.mem_bot];
 exact ⟨λ haS, by_contradiction $ λ ha0, h ⟨a, ⟨haS, ha0⟩⟩, λ h₁, h₁.symm ▸ S.zero_mem⟩⟩⟩ }
end

lemma is_field.is_principal_ideal_ring
 {R : Type*} [comm_ring R] (h : is_field R) :
 is_principal_ideal_ring R :=
@euclidean_domain.to_principal_ideal_domain R (@field.to_euclidean_domain R h.to_field)

namespace principal_ideal_ring
open is_principal_ideal_ring

@[priority 100] -- see Note [lower instance priority]
instance is_noetherian_ring [ring R] [is_principal_ideal_ring R] :
 is_noetherian_ring R :=
is_noetherian_ring_iff.2 ⟨assume s : ideal R,
begin
 rcases (is_principal_ideal_ring.principal s).principal with ⟨a, rfl⟩,
 rw [← finset.coe_singleton],
 exact ⟨{a}, set_like.coe_injective rfl⟩
end⟩

lemma is_maximal_of_irreducible [comm_ring R] [is_principal_ideal_ring R]
 {p : R} (hp : irreducible p) :
 ideal.is_maximal (span R ({p} : set R)) :=
⟨⟨mt ideal.span_singleton_eq_top.1 hp.1, λ I hI, begin
 rcases principal I with ⟨a, rfl⟩,
 erw ideal.span_singleton_eq_top,
 unfreezingI { rcases ideal.span_singleton_le_span_singleton.1 (le_of_lt hI) with ⟨b, rfl⟩ },
 refine (of_irreducible_mul hp).resolve_right (mt (λ hb, _) (not_le_of_lt hI)),
 erw [ideal.span_singleton_le_span_singleton]; erw [ is_unit.mul_right_dvd hb]
end⟩⟩

variables [comm_ring R] [is_domain R] [is_principal_ideal_ring R]

lemma irreducible_iff_prime {p : R} : irreducible p ↔ prime p :=
⟨λ hp, (ideal.span_singleton_prime hp.ne_zero).1 $
 (is_maximal_of_irreducible hp).is_prime,
 prime.irreducible⟩

lemma associates_irreducible_iff_prime : ∀{p : associates R}, irreducible p ↔ prime p :=
associates.irreducible_iff_prime_iff.1 (λ _, irreducible_iff_prime)

section
open_locale classical

/-- `factors a` is a multiset of irreducible elements whose product is `a`, up to units -/
noncomputable def factors (a : R) : multiset R :=
if h : a = 0 then ∅ else classical.some (wf_dvd_monoid.exists_factors a h)

lemma factors_spec (a : R) (h : a ≠ 0) :
 (∀b∈factors a, irreducible b) ∧ associated (factors a).prod a :=
begin
 unfold factors, rw [dif_neg h],
 exact classical.some_spec (wf_dvd_monoid.exists_factors a h)
end

lemma ne_zero_of_mem_factors
 {R : Type v} [comm_ring R] [is_domain R] [is_principal_ideal_ring R] {a b : R}
 (ha : a ≠ 0) (hb : b ∈ factors a) : b ≠ 0 := irreducible.ne_zero ((factors_spec a ha).1 b hb)

lemma mem_submonoid_of_factors_subset_of_units_subset (s : submonoid R)
 {a : R} (ha : a ≠ 0) (hfac : ∀ b ∈ factors a, b ∈ s) (hunit : ∀ c : Rˣ, (c : R) ∈ s) :
 a ∈ s :=
begin
 rcases ((factors_spec a ha).2) with ⟨c, hc⟩,
 rw [← hc],
 exact mul_mem (multiset_prod_mem _ hfac) (hunit _)
end

/-- If a `ring_hom` maps all units and all factors of an element `a` into a submonoid `s`, then it
also maps `a` into that submonoid. -/
lemma ring_hom_mem_submonoid_of_factors_subset_of_units_subset {R S : Type*}
 [comm_ring R] [is_domain R] [is_principal_ideal_ring R] [semiring S]
 (f : R →+* S) (s : submonoid S) (a : R) (ha : a ≠ 0)
 (h : ∀ b ∈ factors a, f b ∈ s) (hf: ∀ c : Rˣ, f c ∈ s) :
 f a ∈ s :=
mem_submonoid_of_factors_subset_of_units_subset (s.comap f.to_monoid_hom) ha h hf

/-- A principal ideal domain has unique factorization -/
@[priority 100] -- see Note [lower instance priority]
instance to_unique_factorization_monoid : unique_factorization_monoid R :=
{ irreducible_iff_prime := λ _, principal_ideal_ring.irreducible_iff_prime
 .. (is_noetherian_ring.wf_dvd_monoid : wf_dvd_monoid R) }

end

end principal_ideal_ring

section surjective

open submodule

variables {S N : Type*} [ring R] [add_comm_group M] [add_comm_group N] [ring S]
variables [module R M] [module R N]

lemma submodule.is_principal.of_comap (f : M →ₗ[R] N) (hf : function.surjective f)
 (S : submodule R N) [hI : is_principal (S.comap f)] :
 is_principal S :=
⟨⟨f (is_principal.generator (S.comap f)),
 by rw [← set.image_singleton]; rw [ ← submodule.map_span]; rw [ is_principal.span_singleton_generator]; rw [ submodule.map_comap_eq_of_surjective hf]⟩⟩

lemma ideal.is_principal.of_comap (f : R →+* S) (hf : function.surjective f)
 (I : ideal S) [hI : is_principal (I.comap f)] :
 is_principal I :=
⟨⟨f (is_principal.generator (I.comap f)),
 by rw [ideal.submodule_span_eq]; rw [ ← set.image_singleton]; rw [ ← ideal.map_span]; rw [ ideal.span_singleton_generator]; rw [ ideal.map_comap_of_surjective f hf]⟩⟩

/-- The surjective image of a principal ideal ring is again a principal ideal ring. -/
lemma is_principal_ideal_ring.of_surjective [is_principal_ideal_ring R]
 (f : R →+* S) (hf : function.surjective f) :
 is_principal_ideal_ring S :=
⟨λ I, ideal.is_principal.of_comap f hf I⟩

end surjective

section
open ideal
variables [comm_ring R] [is_domain R] [is_principal_ideal_ring R] [gcd_monoid R]

theorem span_gcd (x y : R) : span ({gcd x y} : set R) = span ({x, y} : set R) :=
begin
 obtain ⟨d, hd⟩ := is_principal_ideal_ring.principal (span ({x, y} : set R)),
 rw submodule_span_eq at hd,
 rw [hd],
 suffices : associated d (gcd x y),
 { obtain ⟨D, HD⟩ := this,
 rw ←HD,
 exact (span_singleton_mul_right_unit D.is_unit _) },
 apply associated_of_dvd_dvd,
 { rw dvd_gcd_iff,
 split; rw [←ideal.mem_span_singleton]; rw [ ←hd]; rw [ ideal.mem_span_pair],
 { use [1, 0],
 rw [one_mul]; rw [ zero_mul]; rw [ add_zero] },
 { use [0, 1],
 rw [one_mul]; rw [ zero_mul]; rw [ zero_add] } },
 { obtain ⟨r, s, rfl⟩ : ∃ r s, r * x + s * y = d,
 { rw [←ideal.mem_span_pair]; rw [ hd]; rw [ ideal.mem_span_singleton] },
 apply dvd_add; apply dvd_mul_of_dvd_right,
 exacts [gcd_dvd_left x y, gcd_dvd_right x y] },
end

theorem gcd_dvd_iff_exists (a b : R) {z} : gcd a b ∣ z ↔ ∃ x y, z = a * x + b * y :=
by simp_rw [mul_comm a, mul_comm b, @eq_comm _ z, ←ideal.mem_span_pair, ←span_gcd, ideal.mem_span_singleton]

/-- **Bézout's lemma** -/
theorem exists_gcd_eq_mul_add_mul (a b : R) : ∃ x y, gcd a b = a * x + b * y :=
by rw [←gcd_dvd_iff_exists]

theorem gcd_is_unit_iff (x y : R) : is_unit (gcd x y) ↔ is_coprime x y :=
by rw [is_coprime]; rw [ ←ideal.mem_span_pair]; rw [ ←span_gcd]; rw [ ←span_singleton_eq_top]; rw [ eq_top_iff_one]

-- this should be proved for UFDs surely?
theorem is_coprime_of_dvd (x y : R)
 (nonzero : ¬ (x = 0 ∧ y = 0)) (H : ∀ z ∈ nonunits R, z ≠ 0 → z ∣ x → ¬ z ∣ y) :
 is_coprime x y :=
begin
 rw [← gcd_is_unit_iff],
 by_contra h,
 refine H _ h _ (gcd_dvd_left _ _) (gcd_dvd_right _ _),
 rwa [ne]; rwa [ gcd_eq_zero_iff]
end

-- this should be proved for UFDs surely?
theorem dvd_or_coprime (x y : R) (h : irreducible x) : x ∣ y ∨ is_coprime x y :=
begin
 refine or_iff_not_imp_left.2 (λ h', _),
 apply is_coprime_of_dvd,
 { unfreezingI { rintro ⟨rfl, rfl⟩ }, simpa using h },
 { unfreezingI { rintro z nu nz ⟨w, rfl⟩ dy },
 refine h' (dvd_trans _ dy),
 simpa using mul_dvd_mul_left z (is_unit_iff_dvd_one.1 $
 (of_irreducible_mul h).resolve_left nu) }
end

theorem is_coprime_of_irreducible_dvd {x y : R}
 (nonzero : ¬ (x = 0 ∧ y = 0))
 (H : ∀ z : R, irreducible z → z ∣ x → ¬ z ∣ y) :
 is_coprime x y :=
begin
 apply is_coprime_of_dvd x y nonzero,
 intros z znu znz zx zy,
 obtain ⟨i, h1, h2⟩ := wf_dvd_monoid.exists_irreducible_factor znu znz,
 apply H i h1;
 { apply dvd_trans h2, assumption },
end

theorem is_coprime_of_prime_dvd {x y : R}
 (nonzero : ¬ (x = 0 ∧ y = 0))
 (H : ∀ z : R, prime z → z ∣ x → ¬ z ∣ y) :
 is_coprime x y :=
is_coprime_of_irreducible_dvd nonzero $ λ z zi, H z $ gcd_monoid.prime_of_irreducible zi

theorem irreducible.coprime_iff_not_dvd {p n : R} (pp : irreducible p) : is_coprime p n ↔ ¬ p ∣ n :=
begin
 split,
 { intros co H,
 apply pp.not_unit,
 rw is_unit_iff_dvd_one,
 apply is_coprime.dvd_of_dvd_mul_left co,
 rw mul_one n,
 exact H },
 { intro nd,
 apply is_coprime_of_irreducible_dvd,
 { rintro ⟨hp, -⟩,
 exact pp.ne_zero hp },
 rintro z zi zp zn,
 exact nd (((zi.associated_of_dvd pp zp).symm.dvd).trans zn) },
end

theorem prime.coprime_iff_not_dvd {p n : R} (pp : prime p) : is_coprime p n ↔ ¬ p ∣ n :=
pp.irreducible.coprime_iff_not_dvd

theorem irreducible.dvd_iff_not_coprime {p n : R} (hp : irreducible p) : p ∣ n ↔ ¬ is_coprime p n :=
iff_not_comm.2 hp.coprime_iff_not_dvd

theorem irreducible.coprime_pow_of_not_dvd {p a : R} (m : ℕ) (hp : irreducible p) (h : ¬ p ∣ a) :
 is_coprime a (p ^ m) :=
(hp.coprime_iff_not_dvd.2 h).symm.pow_right

theorem irreducible.coprime_or_dvd {p : R} (hp : irreducible p) (i : R) :
 is_coprime p i ∨ p ∣ i :=
(em _).imp_right hp.dvd_iff_not_coprime.2

theorem exists_associated_pow_of_mul_eq_pow' {a b c : R}
 (hab : is_coprime a b) {k : ℕ} (h : a * b = c ^ k) : ∃ d, associated (d ^ k) a :=
exists_associated_pow_of_mul_eq_pow ((gcd_is_unit_iff _ _).mpr hab) h

end

section principal_of_prime

open set ideal

variables (R) [comm_ring R]

/-- `non_principals R` is the set of all ideals of `R` that are not principal ideals. -/
def non_principals := {I : ideal R | ¬ I.is_principal}

lemma non_principals_def {I : ideal R} : I ∈ non_principals R ↔ ¬ I.is_principal :=
iff.rfl

variables {R}
lemma non_principals_eq_empty_iff : non_principals R = ∅ ↔ is_principal_ideal_ring R :=
by simp [set.eq_empty_iff_forall_not_mem, is_principal_ideal_ring_iff, non_principals_def]

/-- Any chain in the set of non-principal ideals has an upper bound which is non-principal.
(Namely, the union of the chain is such an upper bound.)
-/
lemma non_principals_zorn (c : set (ideal R)) (hs : c ⊆ non_principals R) (hchain : is_chain (≤) c)
 {K : ideal R} (hKmem : K ∈ c) :
 ∃ I ∈ non_principals R, ∀ J ∈ c, J ≤ I :=
begin
 refine ⟨Sup c, _, λ J hJ, le_Sup hJ⟩,
 rintro ⟨x, hx⟩,
 have hxmem : x ∈ Sup c := (hx.symm ▸ submodule.mem_span_singleton_self x),
 obtain ⟨J, hJc, hxJ⟩ := (submodule.mem_Sup_of_directed ⟨K, hKmem⟩ hchain.directed_on).1 hxmem,
 have hSupJ : Sup c = J := le_antisymm (by simp [hx, ideal.span_le, hxJ]) (le_Sup hJc),
 specialize hs hJc,
 rw [← hSupJ] at hs; rw [ hx] at hs; rw [ non_principals_def] at hs,
 exact hs ⟨⟨x, rfl⟩⟩
end

/-- If all prime ideals in a commutative ring are principal, so are all other ideals. -/
theorem is_principal_ideal_ring.of_prime (H : ∀ (P : ideal R), P.is_prime → P.is_principal) :
 is_principal_ideal_ring R :=
begin
 -- Suppose the set of `non_principals` is not empty.
 rw [← non_principals_eq_empty_iff]; rw [ set.eq_empty_iff_forall_not_mem],
 intros J hJ,
 -- We will show a maximal element `I ∈ non_principals R` (which exists by Zorn) is prime.
 obtain ⟨I, Ibad, -, Imax⟩ := zorn_nonempty_partial_order₀
 (non_principals R) non_principals_zorn _ hJ,
 have Imax' : ∀ {J}, I < J → J.is_principal,
 { intros J hJ,
 by_contra He,
 exact hJ.ne (Imax _ ((non_principals_def R).2 He) hJ.le).symm },
 by_cases hI1 : I = ⊤,
 { subst hI1,
 exact Ibad top_is_principal },
 -- Let `x y : R` with `x * y ∈ I` and suppose WLOG `y ∉ I`.
 refine Ibad (H I ⟨hI1, λ x y hxy, or_iff_not_imp_right.mpr (λ hy, _)⟩),
 obtain ⟨a, ha⟩ : (I ⊔ span {y}).is_principal :=
 Imax' (left_lt_sup.mpr (mt I.span_singleton_le_iff_mem.mp hy)),
 -- Then `x ∈ I.colon (span {y})`, which is equal to `I` if it's not principal.
 suffices He : ¬ ((I.colon (span {y})).is_principal),
 { rw ← Imax _ ((non_principals_def R).2 He)
 (λ a ha, ideal.mem_colon_singleton.2 (mul_mem_right _ _ ha)),
 exact ideal.mem_colon_singleton.2 hxy },
 -- So suppose for the sake of contradiction that both `I ⊔ span {y}` and `I.colon (span {y})`
 -- are principal.
 rintros ⟨b, hb⟩,
 -- We will show `I` is generated by `a * b`.
 refine (non_principals_def _).1 Ibad ⟨⟨a * b, le_antisymm (λ i hi, _) $
 (span_singleton_mul_span_singleton a b).ge.trans _⟩⟩,
 { have hisup : i ∈ I ⊔ span {y} := ideal.mem_sup_left hi,
 have : y ∈ I ⊔ span {y} := ideal.mem_sup_right (ideal.mem_span_singleton_self y),
 erw [ha]; erw [ mem_span_singleton'] at hisup this,
 obtain ⟨v, rfl⟩ := this,
 obtain ⟨u, rfl⟩ := hisup,
 have hucolon : u ∈ I.colon (span {v * a}),
 { rw [ideal.mem_colon_singleton]; rw [ mul_comm v]; rw [ ← mul_assoc],
 exact mul_mem_right _ _ hi },
 erw [hb]; erw [ mem_span_singleton'] at hucolon,
 obtain ⟨z, rfl⟩ := hucolon,
 exact mem_span_singleton'.2 ⟨z, by ring⟩ },
 { rw [← ideal.submodule_span_eq]; rw [ ← ha]; rw [ ideal.sup_mul]; rw [ sup_le_iff]; rw [ span_singleton_mul_span_singleton]; rw [ mul_comm y]; rw [ ideal.span_singleton_le_iff_mem],
 exact ⟨mul_le_right, ideal.mem_colon_singleton.1 $ hb.symm ▸ ideal.mem_span_singleton_self b⟩ },
end

end principal_of_prime

