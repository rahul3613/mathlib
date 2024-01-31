/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.fin.vec_notation
import algebra.big_operators.fin

/-!
# Lemmas for tuples `fin m → α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains alternative definitions of common operators on vectors which expand
definitionally to the expected expression when evaluated on `![]` notation.

This allows "proof by reflection", where we prove `f = ![f 0, f 1]` by defining
`fin_vec.eta_expand f` to be equal to the RHS definitionally, and then prove that
`f = eta_expand f`.

The definitions in this file should normally not be used directly; the intent is for the
corresponding `*_eq` lemmas to be used in a place where they are definitionally unfolded.

## Main definitions

* `fin_vec.seq`
* `fin_vec.map`
* `fin_vec.sum`
* `fin_vec.eta_expand`
-/

namespace fin_vec
variables {m n : ℕ} {α β γ : Type*}

/-- Evaluate `fin_vec.seq f v = ![(f 0) (v 0), (f 1) (v 1), ...]` -/
def seq : Π {m}, (fin m → (α → β)) → (fin m → α) → fin m → β
| 0 f v := ![]
| (n + 1) f v := matrix.vec_cons (f 0 (v 0)) (seq (matrix.vec_tail f) (matrix.vec_tail v))

@[simp]
lemma seq_eq : Π {m} (f : fin m → (α → β)) (v : fin m → α),
  seq f v = (λ i, f i (v i))
| 0 f v := subsingleton.elim _ _
| (n + 1) f v := funext $ λ i, begin
  simp_rw [seq, seq_eq],
  refine i.cases _ (λ i, _),
  { refl },
  { simp only [matrix.cons_val_succ], refl },
end

example {f₁ f₂ : α → β} (a₁ a₂ : α) : seq ![f₁, f₂] ![a₁, a₂] = ![f₁ a₁, f₂ a₂] := rfl

/-- `fin_vec.map f v = ![f (v 0), f (v 1), ...]` -/
def map (f : α → β) {m} : (fin m → α) → fin m → β := seq (λ i, f)

/--
This can be use to prove
```lean
example {f : α → β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
(map_eq _ _).symm
```
-/
@[simp]
lemma map_eq (f : α → β) {m} (v : fin m → α) : map f v = (f ∘ v) :=
seq_eq _ _

example {f : α → β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
(map_eq _ _).symm

/-- Expand `v` to `![v 0, v 1, ...]` -/
def eta_expand {m} (v : fin m → α) : fin m → α := map id v

/--
This can be use to prove
```lean
example {f : α → β} (a : fin 2 → α) : a = ![a 0, a 1] := (eta_expand_eq _).symm
```
-/
@[simp]
lemma eta_expand_eq {m} (v : fin m → α) : eta_expand v = v := map_eq id v

example {f : α → β} (a : fin 2 → α) : a = ![a 0, a 1] := (eta_expand_eq _).symm

/-- `∀` with better defeq for `∀ x : fin m → α, P x`. -/
def «forall» : Π {m} (P : (fin m → α) → Prop), Prop
| 0 P := P ![]
| (n + 1) P := ∀ x : α, «forall» (λ v, P (matrix.vec_cons x v))

/--
This can be use to prove
```lean
example (P : (fin 2 → α) → Prop) : (∀ f, P f) ↔ (∀ a₀ a₁, P ![a₀, a₁]) := (forall_iff _).symm
```
-/
@[simp]
lemma forall_iff : Π {m} (P : (fin m → α) → Prop), «forall» P ↔ ∀ x, P x
| 0 P := by { simp only [«forall», fin.forall_fin_zero_pi], refl }
| (n + 1) P := by simp only [«forall», forall_iff, fin.forall_fin_succ_pi, matrix.vec_cons]

example (P : (fin 2 → α) → Prop) : (∀ f, P f) ↔ (∀ a₀ a₁, P ![a₀, a₁]) := (forall_iff _).symm

/-- `∃` with better defeq for `∃ x : fin m → α, P x`. -/
def «exists» : Π {m} (P : (fin m → α) → Prop), Prop
| 0 P := P ![]
| (n + 1) P := ∃ x : α, «exists» (λ v, P (matrix.vec_cons x v))

/--
This can be use to prove
```lean
example (P : (fin 2 → α) → Prop) : (∃ f, P f) ↔ (∃ a₀ a₁, P ![a₀, a₁]) := (exists_iff _).symm
```
-/
lemma exists_iff : Π {m} (P : (fin m → α) → Prop), «exists» P ↔ ∃ x, P x
| 0 P := by { simp only [«exists», fin.exists_fin_zero_pi, matrix.vec_empty], refl }
| (n + 1) P := by simp only [«exists», exists_iff, fin.exists_fin_succ_pi, matrix.vec_cons]

example (P : (fin 2 → α) → Prop) : (∃ f, P f) ↔ (∃ a₀ a₁, P ![a₀, a₁]) := (exists_iff _).symm

/-- `finset.univ.sum` with better defeq for `fin` -/
def sum [has_add α] [has_zero α] : Π{m} (v : fin m → α), α
| 0 v := 0
| 1 v := v 0
| (n + 2) v := sum (v ∘ fin.cast_succ) + v (fin.last _)

open_locale big_operators

/-- This can be used to prove
```lean
example [add_comm_monoid α] (a : fin 3 → α) : ∑ i, a i = a 0 + a 1 + a 2 :=
(sum_eq _).symm
```
-/
@[simp]
lemma sum_eq [add_comm_monoid α] : Π {m} (a : fin m → α),
  sum a = ∑ i, a i
| 0 a := rfl
| 1 a := (fintype.sum_unique a).symm
| (n + 2) a := by rw [fin.sum_univ_cast_succ, sum, sum_eq]

example [add_comm_monoid α] (a : fin 3 → α) : ∑ i, a i = a 0 + a 1 + a 2 :=
(sum_eq _).symm

end fin_vec
