/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.polynomial.algebra_map
import field_theory.minpoly.is_integrally_closed
import ring_theory.power_basis

/-!
# A predicate on adjoining roots of polynomial

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a predicate `is_adjoin_root S f`, which states that the ring `S` can be
constructed by adjoining a specified root of the polynomial `f : R[X]` to `R`.
This predicate is useful when the same ring can be generated by adjoining the root of different
polynomials, and you want to vary which polynomial you're considering.

The results in this file are intended to mirror those in `ring_theory.adjoin_root`,
in order to provide an easier way to translate results from one to the other.

## Motivation

`adjoin_root` presents one construction of a ring `R[α]`. However, it is possible to obtain
rings of this form in many ways, such as `number_field.ring_of_integers ℚ(√-5)`,
or `algebra.adjoin R {α, α^2}`, or `intermediate_field.adjoin R {α, 2 - α}`,
or even if we want to view `ℂ` as adjoining a root of `X^2 + 1` to `ℝ`.

## Main definitions

The two main predicates in this file are:

 * `is_adjoin_root S f`: `S` is generated by adjoining a specified root of `f : R[X]` to `R`
 * `is_adjoin_root_monic S f`: `S` is generated by adjoining a root of the monic polynomial
 `f : R[X]` to `R`

Using `is_adjoin_root` to map into `S`:

 * `is_adjoin_root.map`: inclusion from `R[X]` to `S`
 * `is_adjoin_root.root`: the specific root adjoined to `R` to give `S`

Using `is_adjoin_root` to map out of `S`:

 * `is_adjoin_root.repr`: choose a non-unique representative in `R[X]`
 * `is_adjoin_root.lift`, `is_adjoin_root.lift_hom`: lift a morphism `R →+* T` to `S →+* T`
 * `is_adjoin_root_monic.mod_by_monic_hom`: a unique representative in `R[X]` if `f` is monic

## Main results

 * `adjoin_root.is_adjoin_root` and `adjoin_root.is_adjoin_root_monic`:
 `adjoin_root` satisfies the conditions on `is_adjoin_root`(`_monic`)
 * `is_adjoin_root_monic.power_basis`: the `root` generates a power basis on `S` over `R`
 * `is_adjoin_root.aequiv`: algebra isomorphism showing adjoining a root gives a unique ring
 up to isomorphism
 * `is_adjoin_root.of_equiv`: transfer `is_adjoin_root` across an algebra isomorphism
 * `is_adjoin_root_eq.minpoly_eq`: the minimal polynomial of the adjoined root of `f` is equal to
 `f`, if `f` is irreducible and monic, and `R` is a GCD domain
-/

open_locale polynomial
open polynomial
noncomputable theory

universes u v

section move_me

end move_me

/-- `is_adjoin_root S f` states that the ring `S` can be constructed by adjoining a specified root
of the polynomial `f : R[X]` to `R`.

Compare `power_basis R S`, which does not explicitly specify which polynomial we adjoin a root of
(in particular `f` does not need to be the minimal polynomial of the root we adjoin),
and `adjoin_root` which constructs a new type.

This is not a typeclass because the choice of root given `S` and `f` is not unique.
-/
@[nolint has_nonempty_instance] -- This class doesn't really make sense on a predicate
structure is_adjoin_root {R : Type u} (S : Type v) [comm_semiring R] [semiring S] [algebra R S]
 (f : R[X]) : Type (max u v) :=
(map : R[X] →+* S)
(map_surjective : function.surjective map)
(ker_map : ring_hom.ker map = ideal.span {f})
(algebra_map_eq : algebra_map R S = map.comp polynomial.C)

/-- `is_adjoin_root_monic S f` states that the ring `S` can be constructed by adjoining a specified
root of the monic polynomial `f : R[X]` to `R`.

As long as `f` is monic, there is a well-defined representation of elements of `S` as polynomials
in `R[X]` of degree lower than `deg f` (see `mod_by_monic_hom` and `coeff`). In particular,
we have `is_adjoin_root_monic.power_basis`.

Bundling `monic` into this structure is very useful when working with explicit `f`s such as
`X^2 - C a * X - C b` since it saves you carrying around the proofs of monicity.
-/
@[nolint has_nonempty_instance] -- This class doesn't really make sense on a predicate
structure is_adjoin_root_monic {R : Type u} (S : Type v) [comm_semiring R] [semiring S]
 [algebra R S] (f : R[X]) extends is_adjoin_root S f :=
(monic : monic f)

section ring

variables {R : Type u} {S : Type v} [comm_ring R] [ring S] {f : R[X]} [algebra R S]

namespace is_adjoin_root

/-- `(h : is_adjoin_root S f).root` is the root of `f` that can be adjoined to generate `S`. -/
def root (h : is_adjoin_root S f) : S := h.map X

lemma subsingleton (h : is_adjoin_root S f) [subsingleton R] : subsingleton S :=
h.map_surjective.subsingleton

lemma algebra_map_apply (h : is_adjoin_root S f) (x : R) :
 algebra_map R S x = h.map (polynomial.C x) :=
by rw [h.algebra_map_eq]; rw [ ring_hom.comp_apply]

@[simp] lemma mem_ker_map (h : is_adjoin_root S f) {p} : p ∈ ring_hom.ker h.map ↔ f ∣ p :=
by rw [h.ker_map]; rw [ ideal.mem_span_singleton]

lemma map_eq_zero_iff (h : is_adjoin_root S f) {p} : h.map p = 0 ↔ f ∣ p :=
by rw [← h.mem_ker_map]; rw [ ring_hom.mem_ker]

@[simp] lemma map_X (h : is_adjoin_root S f) : h.map X = h.root := rfl

@[simp] lemma map_self (h : is_adjoin_root S f) : h.map f = 0 :=
h.map_eq_zero_iff.mpr dvd_rfl

@[simp] lemma aeval_eq (h : is_adjoin_root S f) (p : R[X]) : aeval h.root p = h.map p :=
polynomial.induction_on p (λ x, by { rw [aeval_C]; rw [ h.algebra_map_apply] })
 (λ p q ihp ihq, by rw [alg_hom.map_add]; rw [ ring_hom.map_add]; rw [ ihp]; rw [ ihq])
 (λ n x ih, by { rw [alg_hom.map_mul]; rw [ aeval_C]; rw [ alg_hom.map_pow]; rw [ aeval_X]; rw [ ring_hom.map_mul]; rw [ ← h.algebra_map_apply]; rw [ ring_hom.map_pow]; rw [ map_X] })

@[simp] lemma aeval_root (h : is_adjoin_root S f) : aeval h.root f = 0 :=
by rw [aeval_eq]; rw [ map_self]

/-- Choose an arbitrary representative so that `h.map (h.repr x) = x`.

If `f` is monic, use `is_adjoin_root_monic.mod_by_monic_hom` for a unique choice of representative.
-/
def repr (h : is_adjoin_root S f) (x : S) : R[X] :=
(h.map_surjective x).some

lemma map_repr (h : is_adjoin_root S f) (x : S) : h.map (h.repr x) = x :=
(h.map_surjective x).some_spec

/-- `repr` preserves zero, up to multiples of `f` -/
lemma repr_zero_mem_span (h : is_adjoin_root S f) : h.repr 0 ∈ ideal.span ({f} : set R[X]) :=
by rw [← h.ker_map]; rw [ ring_hom.mem_ker]; rw [ h.map_repr]

/-- `repr` preserves addition, up to multiples of `f` -/
lemma repr_add_sub_repr_add_repr_mem_span (h : is_adjoin_root S f) (x y : S) :
 h.repr (x + y) - (h.repr x + h.repr y) ∈ ideal.span ({f} : set R[X]) :=
by rw [← h.ker_map]; rw [ ring_hom.mem_ker]; rw [ map_sub]; rw [ h.map_repr]; rw [ map_add]; rw [ h.map_repr]; rw [ h.map_repr]; rw [ sub_self]

/-- Extensionality of the `is_adjoin_root` structure itself. See `is_adjoin_root_monic.ext_elem`
for extensionality of the ring elements. -/
lemma ext_map (h h' : is_adjoin_root S f) (eq : ∀ x, h.map x = h'.map x) : h = h' :=
begin
 cases h, cases h', congr,
 exact ring_hom.ext eq
end

/-- Extensionality of the `is_adjoin_root` structure itself. See `is_adjoin_root_monic.ext_elem`
for extensionality of the ring elements. -/
@[ext]
lemma ext (h h' : is_adjoin_root S f) (eq : h.root = h'.root) : h = h' :=
h.ext_map h' (λ x, by rw [← h.aeval_eq]; rw [ ← h'.aeval_eq]; rw [ eq])

section lift

variables {T : Type*} [comm_ring T] {i : R →+* T} {x : T} (hx : f.eval₂ i x = 0)

include hx

/-- Auxiliary lemma for `is_adjoin_root.lift` -/
lemma eval₂_repr_eq_eval₂_of_map_eq (h : is_adjoin_root S f) (z : S) (w : R[X])
 (hzw : h.map w = z) :
 (h.repr z).eval₂ i x = w.eval₂ i x :=
begin
 rw [eq_comm] at hzw; rw [ ← sub_eq_zero] at hzw; rw [ ← h.map_repr z] at hzw; rw [ ← map_sub] at hzw; rw [ h.map_eq_zero_iff] at hzw,
 obtain ⟨y, hy⟩ := hzw,
 rw [← sub_eq_zero]; rw [ ← eval₂_sub]; rw [ hy]; rw [ eval₂_mul]; rw [ hx]; rw [ zero_mul]
end

variables (i x) -- To match `adjoin_root.lift`

/-- Lift a ring homomorphism `R →+* T` to `S →+* T` by specifying a root `x` of `f` in `T`,
where `S` is given by adjoining a root of `f` to `R`. -/
def lift (h : is_adjoin_root S f) : S →+* T :=
{ to_fun := λ z, (h.repr z).eval₂ i x,
 map_zero' := by rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ _ (map_zero _)]; rw [ eval₂_zero],
 map_add' := λ z w, begin
 rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ (h.repr z + h.repr w)]; rw [ eval₂_add],
 { rw [map_add]; rw [ map_repr]; rw [ map_repr] }
 end,
 map_one' := by rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ _ (map_one _)]; rw [ eval₂_one],
 map_mul' := λ z w, begin
 rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ (h.repr z * h.repr w)]; rw [ eval₂_mul],
 { rw [map_mul]; rw [ map_repr]; rw [ map_repr] }
 end }

variables {i x}

@[simp] lemma lift_map (h : is_adjoin_root S f) (z : R[X]) :
 h.lift i x hx (h.map z) = z.eval₂ i x :=
by rw [lift]; rw [ ring_hom.coe_mk]; rw [ h.eval₂_repr_eq_eval₂_of_map_eq hx _ _ rfl]

@[simp] lemma lift_root (h : is_adjoin_root S f) :
 h.lift i x hx h.root = x :=
by rw [← h.map_X]; rw [ lift_map]; rw [ eval₂_X]

@[simp] lemma lift_algebra_map (h : is_adjoin_root S f) (a : R) :
 h.lift i x hx (algebra_map R S a) = i a :=
by rw [h.algebra_map_apply]; rw [ lift_map]; rw [ eval₂_C]

/-- Auxiliary lemma for `apply_eq_lift` -/
lemma apply_eq_lift (h : is_adjoin_root S f) (g : S →+* T)
 (hmap : ∀ a, g (algebra_map R S a) = i a) (hroot : g h.root = x) (a : S):
 g a = h.lift i x hx a :=
begin
 rw [← h.map_repr a]; rw [ polynomial.as_sum_range_C_mul_X_pow (h.repr a)],
 simp only [map_sum, map_mul, map_pow, h.map_X, hroot, ← h.algebra_map_apply, hmap, lift_root,
 lift_algebra_map]
end

/-- Unicity of `lift`: a map that agrees on `R` and `h.root` agrees with `lift` everywhere. -/
lemma eq_lift (h : is_adjoin_root S f) (g : S →+* T)
 (hmap : ∀ a, g (algebra_map R S a) = i a) (hroot : g h.root = x) :
 g = h.lift i x hx :=
ring_hom.ext (h.apply_eq_lift hx g hmap hroot)

variables [algebra R T] (hx' : aeval x f = 0)

omit hx

variables (x) -- To match `adjoin_root.lift_hom`

/-- Lift the algebra map `R → T` to `S →ₐ[R] T` by specifying a root `x` of `f` in `T`,
where `S` is given by adjoining a root of `f` to `R`. -/
def lift_hom (h : is_adjoin_root S f) : S →ₐ[R] T :=
{ commutes' := λ a, h.lift_algebra_map hx' a,
 .. h.lift (algebra_map R T) x hx' }

variables {x}

@[simp] lemma coe_lift_hom (h : is_adjoin_root S f) :
 (h.lift_hom x hx' : S →+* T) = h.lift (algebra_map R T) x hx' := rfl

lemma lift_algebra_map_apply (h : is_adjoin_root S f) (z : S) :
 h.lift (algebra_map R T) x hx' z = h.lift_hom x hx' z := rfl

@[simp] lemma lift_hom_map (h : is_adjoin_root S f) (z : R[X]) :
 h.lift_hom x hx' (h.map z) = aeval x z :=
by rw [← lift_algebra_map_apply]; rw [ lift_map]; rw [ aeval_def]

@[simp] lemma lift_hom_root (h : is_adjoin_root S f) :
 h.lift_hom x hx' h.root = x :=
by rw [← lift_algebra_map_apply]; rw [ lift_root]

/-- Unicity of `lift_hom`: a map that agrees on `h.root` agrees with `lift_hom` everywhere. -/
lemma eq_lift_hom (h : is_adjoin_root S f) (g : S →ₐ[R] T) (hroot : g h.root = x) :
 g = h.lift_hom x hx' :=
alg_hom.ext (h.apply_eq_lift hx' g g.commutes hroot)

end lift

end is_adjoin_root

namespace adjoin_root

variables (f)

/-- `adjoin_root f` is indeed given by adjoining a root of `f`. -/
protected def is_adjoin_root : is_adjoin_root (adjoin_root f) f :=
{ map := adjoin_root.mk f,
 map_surjective := ideal.quotient.mk_surjective,
 ker_map := begin
 ext,
 rw [ring_hom.mem_ker]; rw [ ← @adjoin_root.mk_self _ _ f]; rw [ adjoin_root.mk_eq_mk]; rw [ ideal.mem_span_singleton]; rw [ ← dvd_add_left (dvd_refl f)]; rw [ sub_add_cancel]
 end,
 algebra_map_eq := adjoin_root.algebra_map_eq f }

/-- `adjoin_root f` is indeed given by adjoining a root of `f`. If `f` is monic this is more
powerful than `adjoin_root.is_adjoin_root`. -/
protected def is_adjoin_root_monic (hf : monic f) :
 is_adjoin_root_monic (adjoin_root f) f :=
{ monic := hf,
 .. adjoin_root.is_adjoin_root f }

@[simp]
lemma is_adjoin_root_map_eq_mk :
 (adjoin_root.is_adjoin_root f).map = adjoin_root.mk f := rfl

@[simp]
lemma is_adjoin_root_monic_map_eq_mk (hf : f.monic) :
 (adjoin_root.is_adjoin_root_monic f hf).map = adjoin_root.mk f := rfl

@[simp]
lemma is_adjoin_root_root_eq_root :
 (adjoin_root.is_adjoin_root f).root = adjoin_root.root f :=
by simp only [is_adjoin_root.root, adjoin_root.root, adjoin_root.is_adjoin_root_map_eq_mk]

@[simp]
lemma is_adjoin_root_monic_root_eq_root (hf : monic f) :
 (adjoin_root.is_adjoin_root_monic f hf).root = adjoin_root.root f :=
by simp only [is_adjoin_root.root, adjoin_root.root, adjoin_root.is_adjoin_root_monic_map_eq_mk]

end adjoin_root

namespace is_adjoin_root_monic

open is_adjoin_root

lemma map_mod_by_monic (h : is_adjoin_root_monic S f) (g : R[X]) :
 h.map (g %ₘ f) = h.map g :=
begin
 rw [← ring_hom.sub_mem_ker_iff]; rw [ mem_ker_map]; rw [ mod_by_monic_eq_sub_mul_div _ h.monic]; rw [ sub_right_comm]; rw [ sub_self]; rw [ zero_sub]; rw [ dvd_neg],
 exact ⟨_, rfl⟩
end

lemma mod_by_monic_repr_map (h : is_adjoin_root_monic S f) (g : R[X]) :
 h.repr (h.map g) %ₘ f = g %ₘ f :=
mod_by_monic_eq_of_dvd_sub h.monic $ by rw [← h.mem_ker_map]; rw [ ring_hom.sub_mem_ker_iff]; rw [ map_repr]

/-- `is_adjoin_root.mod_by_monic_hom` sends the equivalence class of `f` mod `g` to `f %ₘ g`. -/
def mod_by_monic_hom (h : is_adjoin_root_monic S f) : S →ₗ[R] R[X] :=
{ to_fun := λ x, h.repr x %ₘ f,
 map_add' := λ x y,
 by conv_lhs { rw [← h.map_repr x]; rw [ ← h.map_repr y]; rw [ ← map_add]; rw [ h.mod_by_monic_repr_map]; rw [ add_mod_by_monic] },
 map_smul' := λ c x,
 by rw [ring_hom.id_apply]; rw [ ← h.map_repr x]; rw [ algebra.smul_def]; rw [ h.algebra_map_apply]; rw [ ← map_mul]; rw [ h.mod_by_monic_repr_map]; rw [ ← smul_eq_C_mul]; rw [ smul_mod_by_monic]; rw [ h.map_repr] }

@[simp] lemma mod_by_monic_hom_map (h : is_adjoin_root_monic S f) (g : R[X]) :
 h.mod_by_monic_hom (h.map g) = g %ₘ f :=
h.mod_by_monic_repr_map g

@[simp] lemma map_mod_by_monic_hom (h : is_adjoin_root_monic S f) (x : S) :
 h.map (h.mod_by_monic_hom x) = x :=
by rw [mod_by_monic_hom]; rw [ linear_map.coe_mk]; rw [ map_mod_by_monic]; rw [ map_repr]

@[simp] lemma mod_by_monic_hom_root_pow (h : is_adjoin_root_monic S f) {n : ℕ}
 (hdeg : n < nat_degree f) :
 h.mod_by_monic_hom (h.root ^ n) = X ^ n :=
begin
 nontriviality R,
 rwa [← h.map_X]; rwa [ ← map_pow]; rwa [ mod_by_monic_hom_map]; rwa [ mod_by_monic_eq_self_iff h.monic]; rwa [ degree_X_pow],
 contrapose! hdeg,
 simpa [nat_degree_le_iff_degree_le] using hdeg
end

@[simp] lemma mod_by_monic_hom_root (h : is_adjoin_root_monic S f) (hdeg : 1 < nat_degree f) :
 h.mod_by_monic_hom h.root = X :=
by simpa using mod_by_monic_hom_root_pow h hdeg

/-- The basis on `S` generated by powers of `h.root`.

Auxiliary definition for `is_adjoin_root_monic.power_basis`. -/
def basis (h : is_adjoin_root_monic S f) : basis (fin (nat_degree f)) R S :=
basis.of_repr
{ to_fun := λ x, (h.mod_by_monic_hom x).to_finsupp.comap_domain coe (fin.coe_injective.inj_on _),
 inv_fun := λ g, h.map (of_finsupp (g.map_domain coe)),
 left_inv := λ x, begin
 casesI subsingleton_or_nontrivial R,
 { haveI := h.subsingleton,
 exact subsingleton.elim _ _ },
 simp only,
 rw [finsupp.map_domain_comap_domain]; rw [ polynomial.eta]; rw [ h.map_mod_by_monic_hom x],
 intros i hi,
 refine set.mem_range.mpr ⟨⟨i, _⟩, rfl⟩,
 contrapose! hi,
 simp only [polynomial.to_finsupp_apply, not_not, finsupp.mem_support_iff, ne.def,
 mod_by_monic_hom, linear_map.coe_mk, finset.mem_coe],
 by_cases hx : h.to_is_adjoin_root.repr x %ₘ f = 0,
 { simp [hx] },
 refine coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le _ hi),
 rw nat_degree_lt_nat_degree_iff hx,
 { exact degree_mod_by_monic_lt _ h.monic },
 end,
 right_inv := λ g, begin
 nontriviality R,
 ext i,
 simp only [h.mod_by_monic_hom_map, finsupp.comap_domain_apply, polynomial.to_finsupp_apply],
 rw [(polynomial.mod_by_monic_eq_self_iff h.monic).mpr]; rw [ polynomial.coeff]; rw [ finsupp.map_domain_apply fin.coe_injective],
 rw [degree_eq_nat_degree h.monic.ne_zero]; rw [ degree_lt_iff_coeff_zero],
 intros m hm,
 rw [polynomial.coeff]; rw [ finsupp.map_domain_notin_range],
 rw [set.mem_range]; rw [ not_exists],
 rintro i rfl,
 exact i.prop.not_le hm
 end,
 map_add' := λ x y,
 by simp only [map_add, finsupp.comap_domain_add_of_injective fin.coe_injective, to_finsupp_add],
 map_smul' := λ c x,
 by simp only [map_smul, finsupp.comap_domain_smul_of_injective fin.coe_injective,
 ring_hom.id_apply, to_finsupp_smul] }

@[simp] lemma basis_apply (h : is_adjoin_root_monic S f) (i) : h.basis i = h.root ^ (i : ℕ) :=
basis.apply_eq_iff.mpr $
show (h.mod_by_monic_hom (h.to_is_adjoin_root.root ^ (i : ℕ))).to_finsupp
 .comap_domain coe (fin.coe_injective.inj_on _) = finsupp.single _ _,
begin
 ext j,
 rw [finsupp.comap_domain_apply]; rw [ mod_by_monic_hom_root_pow],
 { rw [X_pow_eq_monomial]; rw [ to_finsupp_monomial]; rw [ finsupp.single_apply_left fin.coe_injective] },
 { exact i.is_lt },
end

lemma deg_pos [nontrivial S] (h : is_adjoin_root_monic S f) : 0 < nat_degree f :=
begin
 rcases h.basis.index_nonempty with ⟨⟨i, hi⟩⟩,
 exact (nat.zero_le _).trans_lt hi
end

lemma deg_ne_zero [nontrivial S] (h : is_adjoin_root_monic S f) : nat_degree f ≠ 0 :=
h.deg_pos.ne'

/-- If `f` is monic, the powers of `h.root` form a basis. -/
@[simps gen dim basis]
def power_basis (h : is_adjoin_root_monic S f) : power_basis R S :=
{ gen := h.root,
 dim := nat_degree f,
 basis := h.basis,
 basis_eq_pow := h.basis_apply }

@[simp] lemma basis_repr (h : is_adjoin_root_monic S f) (x : S) (i : fin (nat_degree f)) :
 h.basis.repr x i = (h.mod_by_monic_hom x).coeff (i : ℕ) :=
begin
 change (h.mod_by_monic_hom x).to_finsupp.comap_domain coe (fin.coe_injective.inj_on _) i = _,
 rw [finsupp.comap_domain_apply]; rw [ polynomial.to_finsupp_apply]
end

lemma basis_one (h : is_adjoin_root_monic S f) (hdeg : 1 < nat_degree f) :
 h.basis ⟨1, hdeg⟩ = h.root :=
by rw [h.basis_apply]; rw [ fin.coe_mk]; rw [ pow_one]

/-- `is_adjoin_root_monic.lift_polyₗ` lifts a linear map on polynomials to a linear map on `S`. -/
@[simps]
def lift_polyₗ {T : Type*} [add_comm_group T] [module R T] (h : is_adjoin_root_monic S f)
 (g : R[X] →ₗ[R] T) : S →ₗ[R] T :=
g.comp h.mod_by_monic_hom

/-- `is_adjoin_root_monic.coeff h x i` is the `i`th coefficient of the representative of `x : S`.
-/
def coeff (h : is_adjoin_root_monic S f) : S →ₗ[R] (ℕ → R) :=
h.lift_polyₗ
{ to_fun := polynomial.coeff,
 map_add' := λ p q, funext (polynomial.coeff_add p q),
 map_smul' := λ c p, funext (polynomial.coeff_smul c p) }

lemma coeff_apply_lt (h : is_adjoin_root_monic S f) (z : S) (i : ℕ) (hi : i < nat_degree f) :
 h.coeff z i = h.basis.repr z ⟨i, hi⟩ :=
begin
 simp only [coeff, linear_map.comp_apply, finsupp.lcoe_fun_apply, finsupp.lmap_domain_apply,
 linear_equiv.coe_coe, lift_polyₗ_apply, linear_map.coe_mk, h.basis_repr],
 refl
end

lemma coeff_apply_coe (h : is_adjoin_root_monic S f) (z : S) (i : fin (nat_degree f)) :
 h.coeff z i = h.basis.repr z i :=
h.coeff_apply_lt z i i.prop

lemma coeff_apply_le (h : is_adjoin_root_monic S f) (z : S) (i : ℕ) (hi : nat_degree f ≤ i) :
 h.coeff z i = 0 :=
begin
 simp only [coeff, linear_map.comp_apply, finsupp.lcoe_fun_apply, finsupp.lmap_domain_apply,
 linear_equiv.coe_coe, lift_polyₗ_apply, linear_map.coe_mk, h.basis_repr],
 nontriviality R,
 exact polynomial.coeff_eq_zero_of_degree_lt ((degree_mod_by_monic_lt _ h.monic).trans_le
 (polynomial.degree_le_of_nat_degree_le hi)),
end

lemma coeff_apply (h : is_adjoin_root_monic S f) (z : S) (i : ℕ) :
 h.coeff z i = if hi : i < nat_degree f then h.basis.repr z ⟨i, hi⟩ else 0 :=
begin
 split_ifs with hi,
 { exact h.coeff_apply_lt z i hi },
 { exact h.coeff_apply_le z i (le_of_not_lt hi) },
end

lemma coeff_root_pow (h : is_adjoin_root_monic S f) {n} (hn : n < nat_degree f) :
 h.coeff (h.root ^ n) = pi.single n 1 :=
begin
 ext i,
 rw coeff_apply,
 split_ifs with hi,
 { calc h.basis.repr (h.root ^ n) ⟨i, _⟩
 = h.basis.repr (h.basis ⟨n, hn⟩) ⟨i, hi⟩
 : by rw [h.basis_apply]; rw [ fin.coe_mk]
 ... = pi.single ((⟨n, hn⟩ : fin _) : ℕ) (1 : (λ _, R) _) ↑(⟨i, _⟩ : fin _) :
 by rw [h.basis.repr_self]; rw [ ← finsupp.single_eq_pi_single]; rw [ finsupp.single_apply_left fin.coe_injective]
 ... = pi.single n 1 i : by rw [fin.coe_mk]; rw [ fin.coe_mk] },
 { refine (pi.single_eq_of_ne _ (1 : (λ _, R) _)).symm,
 rintro rfl,
 simpa [hi] using hn },
end

lemma coeff_one [nontrivial S] (h : is_adjoin_root_monic S f) :
 h.coeff 1 = pi.single 0 1 :=
by rw [← h.coeff_root_pow h.deg_pos]; rw [ pow_zero]

lemma coeff_root (h : is_adjoin_root_monic S f) (hdeg : 1 < (nat_degree f)) :
 h.coeff h.root = pi.single 1 1 :=
by rw [← h.coeff_root_pow hdeg]; rw [ pow_one]

lemma coeff_algebra_map [nontrivial S] (h : is_adjoin_root_monic S f) (x : R) :
 h.coeff (algebra_map R S x) = pi.single 0 x :=
begin
 ext i,
 rw [algebra.algebra_map_eq_smul_one]; rw [ map_smul]; rw [ coeff_one]; rw [ pi.smul_apply]; rw [ smul_eq_mul],
 refine (pi.apply_single (λ _ y, x * y) _ 0 1 i).trans (by simp),
 intros,
 simp
end

lemma ext_elem (h : is_adjoin_root_monic S f) ⦃x y : S⦄
 (hxy : ∀ i < (nat_degree f), h.coeff x i = h.coeff y i) : x = y :=
equiv_like.injective h.basis.equiv_fun $ funext $ λ i,
show h.basis.equiv_fun x i = h.basis.equiv_fun y i,
by rw [basis.equiv_fun_apply]; rw [ ← h.coeff_apply_coe]; rw [ basis.equiv_fun_apply]; rw [ ← h.coeff_apply_coe]; rw [ hxy i i.prop]

lemma ext_elem_iff (h : is_adjoin_root_monic S f) {x y : S} :
 x = y ↔ ∀ i < (nat_degree f), h.coeff x i = h.coeff y i :=
⟨λ hxy i hi, hxy ▸ rfl, λ hxy, h.ext_elem hxy⟩

lemma coeff_injective (h : is_adjoin_root_monic S f) : function.injective h.coeff :=
λ x y hxy, h.ext_elem (λ i hi, hxy ▸ rfl)

lemma is_integral_root (h : is_adjoin_root_monic S f) : is_integral R h.root :=
⟨f, h.monic, h.aeval_root⟩

end is_adjoin_root_monic

end ring

section comm_ring

variables {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] [algebra R S] {f : R[X]}

namespace is_adjoin_root

section lift

@[simp] lemma lift_self_apply (h : is_adjoin_root S f) (x : S) :
 h.lift (algebra_map R S) h.root h.aeval_root x = x :=
by rw [← h.map_repr x]; rw [ lift_map]; rw [ ← aeval_def]; rw [ h.aeval_eq]

lemma lift_self (h : is_adjoin_root S f) :
 h.lift (algebra_map R S) h.root h.aeval_root = ring_hom.id S :=
ring_hom.ext (h.lift_self_apply)

end lift

section equiv

variables {T : Type*} [comm_ring T] [algebra R T]

/-- Adjoining a root gives a unique ring up to algebra isomorphism.

This is the converse of `is_adjoin_root.of_equiv`: this turns an `is_adjoin_root` into an
`alg_equiv`, and `is_adjoin_root.of_equiv` turns an `alg_equiv` into an `is_adjoin_root`.
-/
def aequiv (h : is_adjoin_root S f) (h' : is_adjoin_root T f) : S ≃ₐ[R] T :=
{ to_fun := h.lift_hom h'.root h'.aeval_root,
 inv_fun := h'.lift_hom h.root h.aeval_root,
 left_inv := λ x, by rw [← h.map_repr x]; rw [ lift_hom_map]; rw [ aeval_eq]; rw [ lift_hom_map]; rw [ aeval_eq],
 right_inv := λ x, by rw [← h'.map_repr x]; rw [ lift_hom_map]; rw [ aeval_eq]; rw [ lift_hom_map]; rw [ aeval_eq],
 .. h.lift_hom h'.root h'.aeval_root }

@[simp] lemma aequiv_map (h : is_adjoin_root S f) (h' : is_adjoin_root T f) (z : R[X]) :
 h.aequiv h' (h.map z) = h'.map z :=
by rw [aequiv]; rw [ alg_equiv.coe_mk]; rw [ lift_hom_map]; rw [ aeval_eq]

@[simp] lemma aequiv_root (h : is_adjoin_root S f) (h' : is_adjoin_root T f) :
 h.aequiv h' h.root = h'.root :=
by rw [aequiv]; rw [ alg_equiv.coe_mk]; rw [ lift_hom_root]

@[simp] lemma aequiv_self (h : is_adjoin_root S f) : h.aequiv h = alg_equiv.refl :=
by { ext a, exact h.lift_self_apply a }

@[simp] lemma aequiv_symm (h : is_adjoin_root S f) (h' : is_adjoin_root T f) :
 (h.aequiv h').symm = h'.aequiv h :=
by { ext, refl }

@[simp] lemma lift_aequiv {U : Type*} [comm_ring U]
 (h : is_adjoin_root S f) (h' : is_adjoin_root T f) (i : R →+* U) (x hx z) :
 (h'.lift i x hx (h.aequiv h' z)) = h.lift i x hx z :=
by rw [← h.map_repr z]; rw [ aequiv_map]; rw [ lift_map]; rw [ lift_map]

@[simp] lemma lift_hom_aequiv {U : Type*} [comm_ring U] [algebra R U]
 (h : is_adjoin_root S f) (h' : is_adjoin_root T f) (x : U) (hx z) :
 (h'.lift_hom x hx (h.aequiv h' z)) = h.lift_hom x hx z :=
h.lift_aequiv h' _ _ hx _

@[simp] lemma aequiv_aequiv {U : Type*} [comm_ring U] [algebra R U]
 (h : is_adjoin_root S f) (h' : is_adjoin_root T f) (h'' : is_adjoin_root U f) (x) :
 (h'.aequiv h'') (h.aequiv h' x) = h.aequiv h'' x :=
h.lift_hom_aequiv _ _ h''.aeval_root _

@[simp] lemma aequiv_trans {U : Type*} [comm_ring U] [algebra R U]
 (h : is_adjoin_root S f) (h' : is_adjoin_root T f) (h'' : is_adjoin_root U f) :
 (h.aequiv h').trans (h'.aequiv h'') = h.aequiv h'' :=
by { ext z, exact h.aequiv_aequiv h' h'' z }

/-- Transfer `is_adjoin_root` across an algebra isomorphism.

This is the converse of `is_adjoin_root.aequiv`: this turns an `alg_equiv` into an `is_adjoin_root`,
and `is_adjoin_root.aequiv` turns an `is_adjoin_root` into an `alg_equiv`.
-/
@[simps map_apply]
def of_equiv (h : is_adjoin_root S f) (e : S ≃ₐ[R] T) : is_adjoin_root T f :=
{ map := ((e : S ≃+* T) : S →+* T).comp h.map,
 map_surjective := e.surjective.comp h.map_surjective,
 ker_map := by rw [← ring_hom.comap_ker]; rw [ ring_hom.ker_coe_equiv]; rw [ ← ring_hom.ker_eq_comap_bot]; rw [ h.ker_map],
 algebra_map_eq := by ext;
 simp only [alg_equiv.commutes, ring_hom.comp_apply, alg_equiv.coe_ring_equiv,
 ring_equiv.coe_to_ring_hom, ← h.algebra_map_apply] }

@[simp] lemma of_equiv_root (h : is_adjoin_root S f) (e : S ≃ₐ[R] T) :
 (h.of_equiv e).root = e h.root := rfl

@[simp] lemma aequiv_of_equiv {U : Type*} [comm_ring U] [algebra R U]
 (h : is_adjoin_root S f) (h' : is_adjoin_root T f) (e : T ≃ₐ[R] U) :
 h.aequiv (h'.of_equiv e) = (h.aequiv h').trans e :=
by ext a; rw [← h.map_repr a]; rw [ aequiv_map]; rw [ alg_equiv.trans_apply]; rw [ aequiv_map]; rw [ of_equiv_map_apply]

@[simp] lemma of_equiv_aequiv {U : Type*} [comm_ring U] [algebra R U]
 (h : is_adjoin_root S f) (h' : is_adjoin_root U f) (e : S ≃ₐ[R] T) :
 (h.of_equiv e).aequiv h' = e.symm.trans (h.aequiv h') :=
by ext a; rw [← (h.of_equiv e).map_repr a]; rw [ aequiv_map]; rw [ alg_equiv.trans_apply]; rw [ of_equiv_map_apply]; rw [ e.symm_apply_apply]; rw [ aequiv_map]

end equiv

end is_adjoin_root

namespace is_adjoin_root_monic

lemma minpoly_eq [is_domain R] [is_domain S] [no_zero_smul_divisors R S] [is_integrally_closed R]
 (h : is_adjoin_root_monic S f) (hirr : irreducible f) :
 minpoly R h.root = f :=
let ⟨q, hq⟩ := minpoly.is_integrally_closed_dvd h.is_integral_root h.aeval_root in
symm $ eq_of_monic_of_associated h.monic (minpoly.monic h.is_integral_root) $
by convert (associated.mul_left (minpoly R h.root) $
 associated_one_iff_is_unit.2 $ (hirr.is_unit_or_is_unit hq).resolve_left $
 minpoly.not_is_unit R h.root);
 rw mul_one

end is_adjoin_root_monic

section algebra

open adjoin_root is_adjoin_root minpoly power_basis is_adjoin_root_monic algebra

lemma algebra.adjoin.power_basis'_minpoly_gen [is_domain R] [is_domain S]
 [no_zero_smul_divisors R S] [is_integrally_closed R] {x : S} (hx' : is_integral R x) :
 minpoly R x = minpoly R (algebra.adjoin.power_basis' hx').gen :=
begin
 haveI := is_domain_of_prime (prime_of_is_integrally_closed hx'),
 haveI := no_zero_smul_divisors_of_prime_of_degree_ne_zero
 (prime_of_is_integrally_closed hx') (ne_of_lt (degree_pos hx')).symm,
 rw [← minpoly_gen_eq]; rw [ adjoin.power_basis']; rw [ minpoly_gen_map]; rw [ minpoly_gen_eq]; rw [ power_basis'_gen]; rw [ ← is_adjoin_root_monic_root_eq_root _ (monic hx')]; rw [ minpoly_eq],
 exact irreducible hx',
end

end algebra

end comm_ring

