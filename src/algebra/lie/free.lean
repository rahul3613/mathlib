/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.of_associative
import algebra.lie.non_unital_non_assoc_algebra
import algebra.lie.universal_enveloping
import algebra.free_non_unital_non_assoc_algebra

/-!
# Free Lie algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a commutative ring `R` and a type `X` we construct the free Lie algebra on `X` with
coefficients in `R` together with its universal property.

## Main definitions

 * `free_lie_algebra`
 * `free_lie_algebra.lift`
 * `free_lie_algebra.of`
 * `free_lie_algebra.universal_enveloping_equiv_free_algebra`

## Implementation details

### Quotient of free non-unital, non-associative algebra

We follow [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975) and construct
the free Lie algebra as a quotient of the free non-unital, non-associative algebra. Since we do not
currently have definitions of ideals, lattices of ideals, and quotients for
`non_unital_non_assoc_semiring`, we construct our quotient using the low-level `quot` function on
an inductively-defined relation.

### Alternative construction (needs PBW)

An alternative construction of the free Lie algebra on `X` is to start with the free unital
associative algebra on `X`, regard it as a Lie algebra via the ring commutator, and take its
smallest Lie subalgebra containing `X`. I.e.:
`lie_subalgebra.lie_span R (free_algebra R X) (set.range (free_algebra.ι R))`.

However with this definition there does not seem to be an easy proof that the required universal
property holds, and I don't know of a proof that avoids invoking the Poincaré–Birkhoff–Witt theorem.
A related MathOverflow question is [this one](https://mathoverflow.net/questions/396680/).

## Tags

lie algebra, free algebra, non-unital, non-associative, universal property, forgetful functor,
adjoint functor
-/

universes u v w

noncomputable theory

variables (R : Type u) (X : Type v) [comm_ring R]

/- We save characters by using Bourbaki's name `lib` (as in «libre») for
`free_non_unital_non_assoc_algebra` in this file. -/
local notation `lib` := free_non_unital_non_assoc_algebra
local notation `lib.lift` := free_non_unital_non_assoc_algebra.lift
local notation `lib.of` := free_non_unital_non_assoc_algebra.of
local notation `lib.lift_of_apply` := free_non_unital_non_assoc_algebra.lift_of_apply
local notation `lib.lift_comp_of` := free_non_unital_non_assoc_algebra.lift_comp_of

namespace free_lie_algebra

/-- The quotient of `lib R X` by the equivalence relation generated by this relation will give us
the free Lie algebra. -/
inductive rel : lib R X → lib R X → Prop
| lie_self (a : lib R X) : rel (a * a) 0
| leibniz_lie (a b c : lib R X) : rel (a * (b * c)) (((a * b) * c) + (b * (a * c)))
| smul (t : R) {a b : lib R X} : rel a b → rel (t • a) (t • b)
| add_right {a b : lib R X} (c : lib R X) : rel a b → rel (a + c) (b + c)
| mul_left (a : lib R X) {b c : lib R X} : rel b c → rel (a * b) (a * c)
| mul_right {a b : lib R X} (c : lib R X) : rel a b → rel (a * c) (b * c)

variables {R X}

lemma rel.add_left (a : lib R X) {b c : lib R X} (h : rel R X b c) : rel R X (a + b) (a + c) :=
by { rw [add_comm _ b]; rw [ add_comm _ c], exact h.add_right _, }

lemma rel.neg {a b : lib R X} (h : rel R X a b) : rel R X (-a) (-b) :=
by simpa only [neg_one_smul] using h.smul (-1)

lemma rel.sub_left (a : lib R X) {b c : lib R X} (h : rel R X b c) : rel R X (a - b) (a - c) :=
by simpa only [sub_eq_add_neg] using h.neg.add_left a

lemma rel.sub_right {a b : lib R X} (c : lib R X) (h : rel R X a b) : rel R X (a - c) (b - c) :=
by simpa only [sub_eq_add_neg] using h.add_right (-c)

lemma rel.smul_of_tower {S : Type*} [monoid S] [distrib_mul_action S R] [is_scalar_tower S R R]
 (t : S) (a b : lib R X)
 (h : rel R X a b) : rel R X (t • a) (t • b) :=
begin
 rw [←smul_one_smul R t a]; rw [ ←smul_one_smul R t b],
 exact h.smul _,
end

end free_lie_algebra

/-- The free Lie algebra on the type `X` with coefficients in the commutative ring `R`. -/
@[derive inhabited]
def free_lie_algebra := quot (free_lie_algebra.rel R X)

namespace free_lie_algebra

instance {S : Type*} [monoid S] [distrib_mul_action S R] [is_scalar_tower S R R] :
 has_smul S (free_lie_algebra R X) :=
{ smul := λ t, quot.map ((•) t) (rel.smul_of_tower t) }

instance {S : Type*} [monoid S] [distrib_mul_action S R] [distrib_mul_action Sᵐᵒᵖ R]
 [is_scalar_tower S R R] [is_central_scalar S R] :
 is_central_scalar S (free_lie_algebra R X) :=
{ op_smul_eq_smul := λ t, quot.ind $ by exact λ a, congr_arg (quot.mk _) (op_smul_eq_smul t a) }

instance : has_zero (free_lie_algebra R X) :=
{ zero := quot.mk _ 0 }

instance : has_add (free_lie_algebra R X) :=
{ add := quot.map₂ (+) (λ _ _ _, rel.add_left _) (λ _ _ _, rel.add_right _) }

instance : has_neg (free_lie_algebra R X) :=
{ neg := quot.map has_neg.neg (λ _ _, rel.neg) }

instance : has_sub (free_lie_algebra R X) :=
{ sub := quot.map₂ has_sub.sub (λ _ _ _, rel.sub_left _) (λ _ _ _, rel.sub_right _) }

instance : add_group (free_lie_algebra R X) :=
function.surjective.add_group (quot.mk _) (surjective_quot_mk _)
 rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance : add_comm_semigroup (free_lie_algebra R X) :=
function.surjective.add_comm_semigroup (quot.mk _) (surjective_quot_mk _) (λ _ _, rfl)

instance : add_comm_group (free_lie_algebra R X) :=
{ ..free_lie_algebra.add_group R X,
 ..free_lie_algebra.add_comm_semigroup R X }

instance {S : Type*} [semiring S] [module S R] [is_scalar_tower S R R] :
 module S (free_lie_algebra R X) :=
function.surjective.module S ⟨quot.mk _, rfl, λ _ _, rfl⟩ (surjective_quot_mk _) (λ _ _, rfl)

/-- Note that here we turn the `has_mul` coming from the `non_unital_non_assoc_semiring` structure
on `lib R X` into a `has_bracket` on `free_lie_algebra`. -/
instance : lie_ring (free_lie_algebra R X) :=
{ bracket := quot.map₂ (*) (λ _ _ _, rel.mul_left _) (λ _ _ _, rel.mul_right _),
 add_lie := by { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩, change quot.mk _ _ = quot.mk _ _, rw add_mul, },
 lie_add := by { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩, change quot.mk _ _ = quot.mk _ _, rw mul_add, },
 lie_self := by { rintros ⟨a⟩, exact quot.sound (rel.lie_self a), },
 leibniz_lie := by { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩, exact quot.sound (rel.leibniz_lie a b c), }, }

instance : lie_algebra R (free_lie_algebra R X) :=
{ lie_smul :=
 begin
 rintros t ⟨a⟩ ⟨c⟩,
 change quot.mk _ (a • (t • c)) = quot.mk _ (t • (a • c)),
 rw ← smul_comm,
 end, }

variables {X}

/-- The embedding of `X` into the free Lie algebra of `X` with coefficients in the commutative ring
`R`. -/
def of : X → free_lie_algebra R X := λ x, quot.mk _ (lib.of R x)

variables {L : Type w} [lie_ring L] [lie_algebra R L]

/-- An auxiliary definition used to construct the equivalence `lift` below. -/
def lift_aux (f : X → commutator_ring L) := lib.lift R f

lemma lift_aux_map_smul (f : X → L) (t : R) (a : lib R X) :
 lift_aux R f (t • a) = t • lift_aux R f a :=
non_unital_alg_hom.map_smul _ t a

lemma lift_aux_map_add (f : X → L) (a b : lib R X) :
 lift_aux R f (a + b) = (lift_aux R f a) + (lift_aux R f b) :=
non_unital_alg_hom.map_add _ a b

lemma lift_aux_map_mul (f : X → L) (a b : lib R X) :
 lift_aux R f (a * b) = ⁅lift_aux R f a, lift_aux R f b⁆ :=
non_unital_alg_hom.map_mul _ a b

lemma lift_aux_spec (f : X → L) (a b : lib R X) (h : free_lie_algebra.rel R X a b) :
 lift_aux R f a = lift_aux R f b :=
begin
 induction h,
 case rel.lie_self : a'
 { simp only [lift_aux_map_mul, non_unital_alg_hom.map_zero, lie_self], },
 case rel.leibniz_lie : a' b' c'
 { simp only [lift_aux_map_mul, lift_aux_map_add, sub_add_cancel, lie_lie], },
 case rel.smul : t a' b' h₁ h₂
 { simp only [lift_aux_map_smul, h₂], },
 case rel.add_right : a' b' c' h₁ h₂
 { simp only [lift_aux_map_add, h₂], },
 case rel.mul_left : a' b' c' h₁ h₂
 { simp only [lift_aux_map_mul, h₂], },
 case rel.mul_right : a' b' c' h₁ h₂
 { simp only [lift_aux_map_mul, h₂], },
end

/-- The quotient map as a `non_unital_alg_hom`. -/
def mk : lib R X →ₙₐ[R] commutator_ring (free_lie_algebra R X) :=
{ to_fun := quot.mk (rel R X),
 map_smul' := λ t a, rfl,
 map_zero' := rfl,
 map_add' := λ a b, rfl,
 map_mul' := λ a b, rfl, }

/-- The functor `X ↦ free_lie_algebra R X` from the category of types to the category of Lie
algebras over `R` is adjoint to the forgetful functor in the other direction. -/
def lift : (X → L) ≃ (free_lie_algebra R X →ₗ⁅R⁆ L) :=
{ to_fun := λ f,
 { to_fun := λ c, quot.lift_on c (lift_aux R f) (lift_aux_spec R f),
 map_add' := by { rintros ⟨a⟩ ⟨b⟩, rw ← lift_aux_map_add, refl, },
 map_smul' := by { rintros t ⟨a⟩, rw ← lift_aux_map_smul, refl, },
 map_lie' := by { rintros ⟨a⟩ ⟨b⟩, rw ← lift_aux_map_mul, refl, }, },
 inv_fun := λ F, F ∘ (of R),
 left_inv := λ f, by { ext x, simp only [lift_aux, of, quot.lift_on_mk, lie_hom.coe_mk,
 function.comp_app, lib.lift_of_apply], },
 right_inv := λ F,
 begin
 ext ⟨a⟩,
 let F' := F.to_non_unital_alg_hom.comp (mk R),
 exact non_unital_alg_hom.congr_fun (lib.lift_comp_of R F') a,
 end, }

@[simp] lemma lift_symm_apply (F : free_lie_algebra R X →ₗ⁅R⁆ L) : (lift R).symm F = F ∘ (of R) :=
rfl

variables {R}

@[simp] lemma of_comp_lift (f : X → L) : (lift R f) ∘ (of R) = f :=
(lift R).left_inv f

@[simp] lemma lift_unique (f : X → L) (g : free_lie_algebra R X →ₗ⁅R⁆ L) :
 g ∘ (of R) = f ↔ g = lift R f :=
(lift R).symm_apply_eq

attribute [irreducible] of lift

@[simp] lemma lift_of_apply (f : X → L) (x) : lift R f (of R x) = f x :=
by rw [← function.comp_app (lift R f) (of R) x]; rw [ of_comp_lift]

@[simp] lemma lift_comp_of (F : free_lie_algebra R X →ₗ⁅R⁆ L) : lift R (F ∘ (of R)) = F :=
by { rw ← lift_symm_apply, exact (lift R).apply_symm_apply F, }

@[ext] lemma hom_ext {F₁ F₂ : free_lie_algebra R X →ₗ⁅R⁆ L} (h : ∀ x, F₁ (of R x) = F₂ (of R x)) :
 F₁ = F₂ :=
have h' : (lift R).symm F₁ = (lift R).symm F₂, { ext, simp [h], },
(lift R).symm.injective h'

variables (R X)

/-- The universal enveloping algebra of the free Lie algebra is just the free unital associative
algebra. -/
@[simps] def universal_enveloping_equiv_free_algebra :
 universal_enveloping_algebra R (free_lie_algebra R X) ≃ₐ[R] free_algebra R X :=
alg_equiv.of_alg_hom
 (universal_enveloping_algebra.lift R $ free_lie_algebra.lift R $ free_algebra.ι R)
 (free_algebra.lift R $ (universal_enveloping_algebra.ι R) ∘ (free_lie_algebra.of R))
 (by { ext, simp, })
 (by { ext, simp, })

end free_lie_algebra

