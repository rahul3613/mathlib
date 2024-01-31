/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/

import algebraic_topology.fundamental_groupoid.fundamental_group
import group_theory.eckmann_hilton
import logic.equiv.transfer_instance
import algebra.group.ext

/-!
# `n`th homotopy group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the `n`th homotopy group at `x : X`, `π_n X x`, as the equivalence classes
of functions from the `n`-dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `gen_loop (fin n) x`; in particular
`gen_loop (fin 1) x ≃ path x x`.

We show that `π_0 X x` is equivalent to the path-connected components, and
that `π_1 X x` is equivalent to the fundamental group at `x`.
We provide a group instance using path composition and show commutativity when `n > 1`.

## definitions

* `gen_loop N x` is the type of continuous fuctions `I^N → X` that send the boundary to `x`,
* `homotopy_group.pi n X x` denoted `π_ n X x` is the quotient of `gen_loop (fin n) x` by
  homotopy relative to the boundary,
* group instance `group (π_(n+1) X x)`,
* commutative group instance `comm_group (π_(n+2) X x)`.

TODO:
* `Ω^M (Ω^N X) ≃ₜ Ω^(M⊕N) X`, and `Ω^M X ≃ₜ Ω^N X` when `M ≃ N`. Similarly for `π_`.
* Path-induced homomorphisms. Show that `homotopy_group.pi_1_equiv_fundamental_group`
  is a group isomorphism.
* Examples with `𝕊^n`: `π_n (𝕊^n) = ℤ`, `π_m (𝕊^n)` trivial for `m < n`.
* Actions of π_1 on π_n.
* Lie algebra: `⁅π_(n+1), π_(m+1)⁆` contained in `π_(n+m+1)`.

-/

open_locale unit_interval topology
open homeomorph

noncomputable theory

localized "notation `I^` N := N → I" in topology

namespace cube

/-- The points in a cube with at least one projection equal to 0 or 1. -/
def boundary (N : Type*) : set (I^N) := {y | ∃ i, y i = 0 ∨ y i = 1}

variables {N : Type*} [decidable_eq N]

/-- The forward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
@[reducible] def split_at (i : N) : (I^N) ≃ₜ I × I^{j // j ≠ i} := fun_split_at I i

/-- The backward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
@[reducible] def insert_at (i : N) : I × (I^{j // j ≠ i}) ≃ₜ I^N := (fun_split_at I i).symm

lemma insert_at_boundary (i : N) {t₀ : I} {t} (H : (t₀ = 0 ∨ t₀ = 1) ∨ t ∈ boundary {j // j ≠ i}) :
  insert_at i ⟨t₀, t⟩ ∈ boundary N :=
begin
  obtain H | ⟨j, H⟩ := H,
  { use i, rwa [fun_split_at_symm_apply, dif_pos rfl] },
  { use j, rwa [fun_split_at_symm_apply, dif_neg j.prop, subtype.coe_eta] },
end

end cube

variables (N X : Type*) [topological_space X] (x : X)

/-- The space of paths with both endpoints equal to a specified point `x : X`. -/
@[reducible] def loop_space := path x x
localized "notation `Ω` := loop_space" in topology

instance loop_space.inhabited : inhabited (path x x) := ⟨path.refl x⟩

/-- The `n`-dimensional generalized loops based at `x` in a space `X` are
  continuous functions `I^n → X` that sends the boundary to `x`.
  We allow an arbitrary indexing type `N` in place of `fin n` here. -/
def gen_loop : set C(I^N, X) := {p | ∀ y ∈ cube.boundary N, p y = x}
localized "notation `Ω^` := gen_loop" in topology

variables {N X x}

namespace gen_loop

/-- Copy of a `gen_loop` with a new map from the unit cube equal to the old one.
  Useful to fix definitional equalities. -/
def copy (f : Ω^N X x) (g : (I^N) → X) (h : g = f) : Ω^N X x :=
⟨⟨g, h.symm ▸ f.1.2⟩, by { convert f.2, ext1, simp_rw h, refl }⟩

lemma coe_copy (f : Ω^N X x) {g : (I^N) → X} (h : g = f) : ⇑(copy f g h) = g := rfl

lemma copy_eq (f : Ω^N X x) {g : (I^N) → X} (h : g = f) : copy f g h = f :=
by { ext x, exact congr_fun h x }

lemma boundary (f : Ω^N X x) : ∀ y ∈ cube.boundary N, f y = x := f.2

instance fun_like : fun_like (Ω^N X x) (I^N) (λ _, X) :=
{ coe := λ f, f.1,
  coe_injective' := λ ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h, by { congr, exact h } }

@[ext] lemma ext (f g : Ω^N X x) (H : ∀ y, f y = g y) : f = g :=
fun_like.coe_injective' (funext H)

@[simp] lemma mk_apply (f : C(I^N, X)) (H y) : (⟨f, H⟩ : Ω^N X x) y = f y := rfl

/-- The constant `gen_loop` at `x`. -/
def const : Ω^N X x := ⟨continuous_map.const _ x, λ _ _, rfl⟩

@[simp] lemma const_apply {t} : (@const N X _ x) t = x := rfl

instance inhabited : inhabited (Ω^N X x) := ⟨const⟩

/-- The "homotopic relative to boundary" relation between `gen_loop`s. -/
def homotopic (f g : Ω^N X x) : Prop := f.1.homotopic_rel g.1 (cube.boundary N)

namespace homotopic

variables {f g h : Ω^N X x}

@[refl] lemma refl (f : Ω^N X x) : homotopic f f := continuous_map.homotopic_rel.refl _

@[symm] lemma symm (H : homotopic f g) : homotopic g f := H.symm

@[trans] lemma trans (H0 : homotopic f g) (H1 : homotopic g h) : homotopic f h := H0.trans H1

lemma equiv : equivalence (@homotopic N X _ x) :=
⟨homotopic.refl, λ _ _, homotopic.symm, λ _ _ _, homotopic.trans⟩

instance setoid (N) (x : X) : setoid (Ω^N X x) := ⟨homotopic, equiv⟩

end homotopic

section loop_homeo

variable [decidable_eq N]

/-- Loop from a generalized loop by currying $I^N → X$ into $I → (I^{N\setminus\{j\}} → X)$. -/
@[simps] def to_loop (i : N) (p : Ω^N X x) : Ω (Ω^{j // j ≠ i} X x) const :=
{ to_fun := λ t, ⟨(p.val.comp (cube.insert_at i).to_continuous_map).curry t,
    λ y yH, p.property (cube.insert_at i (t, y)) (cube.insert_at_boundary i $ or.inr yH)⟩,
  source' := by { ext t, refine p.property (cube.insert_at i (0, t)) ⟨i, or.inl _⟩, simp },
  target' := by { ext t, refine p.property (cube.insert_at i (1, t)) ⟨i, or.inr _⟩, simp } }

lemma continuous_to_loop (i : N) : continuous (@to_loop N X _ x _ i) :=
path.continuous_uncurry_iff.1 $ continuous.subtype_mk (continuous_map.continuous_eval'.comp $
  continuous.prod_map (continuous_map.continuous_curry.comp $
    (continuous_map.continuous_comp_left _).comp continuous_subtype_coe) continuous_id) _

/-- Generalized loop from a loop by uncurrying $I → (I^{N\setminus\{j\}} → X)$ into $I^N → X$. -/
@[simps] def from_loop (i : N) (p : Ω (Ω^{j // j ≠ i} X x) const) : Ω^N X x :=
⟨(continuous_map.comp ⟨coe⟩ p.to_continuous_map).uncurry.comp (cube.split_at i).to_continuous_map,
begin
  rintros y ⟨j, Hj⟩,
  simp only [subtype.val_eq_coe, continuous_map.comp_apply, to_continuous_map_apply,
    fun_split_at_apply, continuous_map.uncurry_apply, continuous_map.coe_mk,
    function.uncurry_apply_pair],
  obtain rfl | Hne := eq_or_ne j i,
  { cases Hj; simpa only [Hj, p.coe_to_continuous_map, p.source, p.target] },
  { exact gen_loop.boundary _ _ ⟨⟨j, Hne⟩, Hj⟩ },
end⟩

lemma continuous_from_loop (i : N) : continuous (@from_loop N X _ x _ i) :=
((continuous_map.continuous_comp_left _).comp $ continuous_map.continuous_uncurry.comp $
  (continuous_map.continuous_comp _).comp continuous_induced_dom).subtype_mk _

lemma to_from (i : N) (p : Ω (Ω^{j // j ≠ i} X x) const) : to_loop i (from_loop i p) = p :=
begin
  simp_rw [to_loop, from_loop, continuous_map.comp_assoc, to_continuous_map_as_coe,
    to_continuous_map_comp_symm, continuous_map.comp_id], ext, refl,
end

/-- The `n+1`-dimensional loops are in bijection with the loops in the space of
  `n`-dimensional loops with base point `const`.
  We allow an arbitrary indexing type `N` in place of `fin n` here. -/
@[simps] def loop_homeo (i : N) : Ω^N X x ≃ₜ Ω (Ω^{j // j ≠ i} X x) const :=
{ to_fun := to_loop i,
  inv_fun := from_loop i,
  left_inv := λ p, by { ext, exact congr_arg p (equiv.apply_symm_apply _ _) },
  right_inv := to_from i,
  continuous_to_fun := continuous_to_loop i,
  continuous_inv_fun := continuous_from_loop i }

lemma to_loop_apply (i : N) {p : Ω^N X x} {t} {tn} :
  to_loop i p t tn = p (cube.insert_at i ⟨t, tn⟩) := rfl

lemma from_loop_apply (i : N) {p : Ω (Ω^{j // j ≠ i} X x) const} {t : I^N} :
  from_loop i p t = p (t i) (cube.split_at i t).snd := rfl

/-- Composition with `cube.insert_at` as a continuous map. -/
@[reducible] def c_comp_insert (i : N) : C(C(I^N, X), C(I × I^{j // j ≠ i}, X)) :=
⟨λ f, f.comp (cube.insert_at i).to_continuous_map,
  (cube.insert_at i).to_continuous_map.continuous_comp_left⟩

/-- A homotopy between `n+1`-dimensional loops `p` and `q` constant on the boundary
  seen as a homotopy between two paths in the space of `n`-dimensional paths. -/
def homotopy_to (i : N) {p q : Ω^N X x} (H : p.1.homotopy_rel q.1 (cube.boundary N)) :
  C(I × I, C(I^{j // j ≠ i}, X)) :=
((⟨_, continuous_map.continuous_curry⟩: C(_,_)).comp $
  (c_comp_insert i).comp H.to_continuous_map.curry).uncurry

-- Should be generated with `@[simps]` but it times out.
lemma homotopy_to_apply (i : N) {p q : Ω^N X x} (H : p.1.homotopy_rel q.1 $ cube.boundary N)
  (t : I × I) (tₙ : I^{j // j ≠ i}) :
  homotopy_to i H t tₙ = H (t.fst, cube.insert_at i (t.snd, tₙ)) := rfl

lemma homotopic_to (i : N) {p q : Ω^N X x} :
  homotopic p q → (to_loop i p).homotopic (to_loop i q) :=
begin
  refine nonempty.map (λ H, ⟨⟨⟨λ t, ⟨homotopy_to i H t, _⟩, _⟩, _, _⟩, _⟩),
  { rintros y ⟨i, iH⟩,
    rw [homotopy_to_apply, H.eq_fst, p.2],
    all_goals { apply cube.insert_at_boundary, right, exact ⟨i, iH⟩} },
  { continuity },
  show ∀ _ _ _, _,
  { intros t y yH,
    split; ext; erw homotopy_to_apply,
    apply H.eq_fst, work_on_goal 2 { apply H.eq_snd },
    all_goals { use i, rw [fun_split_at_symm_apply, dif_pos rfl], exact yH } },
  all_goals { intro, ext, erw [homotopy_to_apply, to_loop_apply] },
  exacts [H.apply_zero _, H.apply_one _],
end

/-- The converse to `gen_loop.homotopy_to`: a homotopy between two loops in the space of
  `n`-dimensional loops can be seen as a homotopy between two `n+1`-dimensional paths. -/
def homotopy_from (i : N) {p q : Ω^N X x}
  (H : (to_loop i p).homotopy (to_loop i q)) : C(I × I^N, X) :=
(continuous_map.comp ⟨_, continuous_map.continuous_uncurry⟩
  (continuous_map.comp ⟨coe⟩ H.to_continuous_map).curry).uncurry.comp $
    (continuous_map.id I).prod_map (cube.split_at i).to_continuous_map

-- Should be generated with `@[simps]` but it times out.
lemma homotopy_from_apply (i : N) {p q : Ω^N X x} (H : (to_loop i p).homotopy (to_loop i q))
  (t : I × I^N) : homotopy_from i H t = H (t.fst, t.snd i) (λ j, t.snd ↑j) := rfl

lemma homotopic_from (i : N) {p q : Ω^N X x} :
  (to_loop i p).homotopic (to_loop i q) → homotopic p q :=
begin
  refine nonempty.map (λ H, ⟨⟨homotopy_from i H, _, _⟩, _⟩),
  show ∀ _ _ _, _,
  { rintros t y ⟨j, jH⟩,
    erw homotopy_from_apply,
    obtain rfl | h := eq_or_ne j i,
    { split,
      { rw H.eq_fst, exacts [congr_arg p (equiv.right_inv _ _), jH] },
      { rw H.eq_snd, exacts [congr_arg q (equiv.right_inv _ _), jH] } },
    { rw [p.2 _ ⟨j, jH⟩, q.2 _ ⟨j, jH⟩], split; { apply boundary, exact ⟨⟨j, h⟩, jH⟩ } } },
  all_goals { intro,
    convert homotopy_from_apply _ _ _,
    rw H.apply_zero <|> rw H.apply_one,
    apply congr_arg p <|> apply congr_arg q,
    exact (equiv.right_inv _ _).symm },
end

/-- Concatenation of two `gen_loop`s along the `i`th coordinate. -/
def trans_at (i : N) (f g : Ω^N X x) : Ω^N X x :=
copy (from_loop i $ (to_loop i f).trans $ to_loop i g)
  (λ t, if (t i : ℝ) ≤ 1/2
    then f (t.update i $ set.proj_Icc 0 1 zero_le_one (2 * t i))
    else g (t.update i $ set.proj_Icc 0 1 zero_le_one (2 * t i - 1)))
begin
  ext1, symmetry,
  dsimp only [path.trans, from_loop, path.coe_mk, function.comp_app,
    mk_apply, continuous_map.comp_apply, to_continuous_map_apply, fun_split_at_apply,
    continuous_map.uncurry_apply, continuous_map.coe_mk, function.uncurry_apply_pair],
  split_ifs, change f _ = _, swap, change g _ = _,
  all_goals { congr' 1 }
end

/-- Reversal of a `gen_loop` along the `i`th coordinate. -/
def symm_at (i : N) (f : Ω^N X x) : Ω^N X x :=
copy (from_loop i (to_loop i f).symm)
  (λ t, f $ λ j, if j = i then σ (t i) else t j) $
  by { ext1, change _ = f _, congr, ext1, simp }

lemma trans_at_distrib {i j : N} (h : i ≠ j) (a b c d : Ω^N X x) :
  trans_at i (trans_at j a b) (trans_at j c d) = trans_at j (trans_at i a c) (trans_at i b d) :=
begin
  ext, simp_rw [trans_at, coe_copy, function.update_apply, if_neg h, if_neg h.symm],
  split_ifs; { congr' 1, ext1, simp only [function.update, eq_rec_constant, dite_eq_ite],
    apply ite_ite_comm, rintro rfl, exact h.symm },
end

lemma from_loop_trans_to_loop {i : N} {p q : Ω^N X x} :
  from_loop i ((to_loop i p).trans $ to_loop i q) = trans_at i p q :=
(copy_eq _ _).symm

lemma from_loop_symm_to_loop {i : N} {p : Ω^N X x} :
  from_loop i (to_loop i p).symm = symm_at i p := (copy_eq _ _).symm

end loop_homeo

end gen_loop

/-- The `n`th homotopy group at `x` defined as the quotient of `Ω^n x` by the
  `gen_loop.homotopic` relation. -/
@[derive inhabited]
def homotopy_group (N) (X : Type*) [topological_space X] (x : X) : Type* :=
quotient (gen_loop.homotopic.setoid N x)

variable [decidable_eq N]
open gen_loop
/-- Equivalence between the homotopy group of X and the fundamental group of
  `Ω^{j // j ≠ i} x`. -/
def homotopy_group_equiv_fundamental_group (i : N) :
  homotopy_group N X x ≃ fundamental_group (Ω^{j // j ≠ i} X x) const :=
begin
  refine equiv.trans _ (category_theory.groupoid.iso_equiv_hom _ _).symm,
  apply quotient.congr (loop_homeo i).to_equiv,
  exact λ p q, ⟨homotopic_to i, homotopic_from i⟩,
end

/-- Homotopy group of finite index. -/
@[reducible] def homotopy_group.pi (n) (X : Type*) [topological_space X] (x : X) :=
homotopy_group (fin n) _ x
localized "notation `π_` := homotopy_group.pi" in topology

/-- The 0-dimensional generalized loops based at `x` are in bijection with `X`. -/
def gen_loop_homeo_of_is_empty (N x) [is_empty N] : Ω^N X x ≃ₜ X :=
{ to_fun := λ f, f 0,
  inv_fun := λ y, ⟨continuous_map.const _ y, λ _ ⟨i, _⟩, is_empty_elim i⟩,
  left_inv := λ f, by { ext, exact congr_arg f (subsingleton.elim _ _) },
  right_inv := λ _, rfl,
  continuous_to_fun :=
    (continuous_map.continuous_eval_const' (0 : N → I)).comp continuous_induced_dom,
  continuous_inv_fun := (continuous_map.const'.2).subtype_mk _ }

/-- The homotopy "group" indexed by an empty type is in bijection with
  the path components of `X`, aka the `zeroth_homotopy`. -/
def homotopy_group_equiv_zeroth_homotopy_of_is_empty (N x) [is_empty N] :
  homotopy_group N X x ≃ zeroth_homotopy X :=
quotient.congr (gen_loop_homeo_of_is_empty N x).to_equiv
begin
  -- joined iff homotopic
  intros, split; rintro ⟨H⟩,
  exacts
  [⟨{ to_fun := λ t, H ⟨t, is_empty_elim⟩,
      source' := (H.apply_zero _).trans (congr_arg a₁ $ subsingleton.elim _ _),
      target' := (H.apply_one _).trans (congr_arg a₂ $ subsingleton.elim _ _) }⟩,
   ⟨{ to_fun := λ t0, H t0.fst,
      map_zero_left' := λ _, by convert H.source,
      map_one_left' := λ _, by convert H.target,
      prop' := λ _ _ ⟨i, _⟩, is_empty_elim i }⟩],
end

/-- The 0th homotopy "group" is in bijection with `zeroth_homotopy`. -/
def homotopy_group.pi_0_equiv_zeroth_homotopy : π_ 0 X x ≃ zeroth_homotopy X :=
homotopy_group_equiv_zeroth_homotopy_of_is_empty (fin 0) x

/-- The 1-dimensional generalized loops based at `x` are in bijection with loops at `x`. -/
@[simps] def gen_loop_equiv_of_unique (N) [unique N] : Ω^N X x ≃ Ω X x :=
{ to_fun := λ p, path.mk ⟨λ t, p (λ _, t), by continuity⟩
    (gen_loop.boundary _ (λ _, 0) ⟨default, or.inl rfl⟩)
    (gen_loop.boundary _ (λ _, 1) ⟨default, or.inr rfl⟩),
  inv_fun := λ p, ⟨⟨λ c, p (c default), by continuity⟩,
  begin
    rintro y ⟨i, iH|iH⟩; cases unique.eq_default i; apply (congr_arg p iH).trans,
    exacts [p.source, p.target],
  end⟩,
  left_inv := λ p, by { ext, exact congr_arg p (eq_const_of_unique y).symm },
  right_inv := λ p, by { ext, refl } }

/-- The homotopy group at `x` indexed by a singleton is in bijection with the fundamental group,
  i.e. the loops based at `x` up to homotopy. -/
/- TODO (?): deducing this from `homotopy_group_equiv_fundamental_group` would require
  combination of `category_theory.functor.map_Aut` and
  `fundamental_groupoid.fundamental_groupoid_functor` applied to `gen_loop_homeo_of_is_empty`,
  with possibly worse defeq. -/
def homotopy_group_equiv_fundamental_group_of_unique (N) [unique N] :
  homotopy_group N X x ≃ fundamental_group X x :=
begin
  refine equiv.trans _ (category_theory.groupoid.iso_equiv_hom _ _).symm,
  refine quotient.congr (gen_loop_equiv_of_unique N) _,
  intros, split; rintros ⟨H⟩,
  { exact
    ⟨ { to_fun := λ tx, H (tx.fst, λ _, tx.snd),
        map_zero_left' := λ _, H.apply_zero _,
        map_one_left' := λ _, H.apply_one _,
        prop' := λ t y iH, H.prop' _ _ ⟨default, iH⟩ } ⟩ },
  refine ⟨⟨⟨⟨λ tx, H (tx.fst, tx.snd default), H.continuous.comp _⟩, λ y, _, λ y, _⟩, _⟩⟩,
  { exact continuous_fst.prod_mk ((continuous_apply _).comp continuous_snd) },
  { convert H.apply_zero _, exact eq_const_of_unique y },
  { convert H.apply_one _, exact eq_const_of_unique y },
  { rintro t y ⟨i, iH⟩,
    cases unique.eq_default i, split,
    { convert H.eq_fst _ _, exacts [eq_const_of_unique y, iH] },
    { convert H.eq_snd _ _, exacts [eq_const_of_unique y, iH] } },
end

/-- The first homotopy group at `x` is in bijection with the fundamental group. -/
def homotopy_group.pi_1_equiv_fundamental_group : π_ 1 X x ≃ fundamental_group X x :=
homotopy_group_equiv_fundamental_group_of_unique (fin 1)

namespace homotopy_group

/-- Group structure on `homotopy_group N X x` for nonempty `N` (in particular `π_(n+1) X x`). -/
instance group (N) [decidable_eq N] [nonempty N] : group (homotopy_group N X x) :=
(homotopy_group_equiv_fundamental_group $ classical.arbitrary N).group

/-- Group structure on `homotopy_group` obtained by pulling back path composition along the
  `i`th direction. The group structures for two different `i j : N` distribute over each
  other, and therefore are equal by the Eckmann-Hilton argument. -/
@[reducible] def aux_group (i : N) : group (homotopy_group N X x) :=
(homotopy_group_equiv_fundamental_group i).group

lemma is_unital_aux_group (i : N) :
  eckmann_hilton.is_unital (aux_group i).mul (⟦const⟧ : homotopy_group N X x) :=
⟨⟨(aux_group i).one_mul⟩, ⟨(aux_group i).mul_one⟩⟩

lemma aux_group_indep (i j : N) : (aux_group i : group (homotopy_group N X x)) = aux_group j :=
begin
  by_cases h : i = j, { rw h },
  refine group.ext (eckmann_hilton.mul (is_unital_aux_group i) (is_unital_aux_group j) _),
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩,
  change quotient.mk _ = _,
  apply congr_arg quotient.mk,
  simp only [from_loop_trans_to_loop, trans_at_distrib h,
    coe_to_equiv, loop_homeo_apply, coe_symm_to_equiv, loop_homeo_symm_apply],
end

lemma trans_at_indep {i} (j) (f g : Ω^N X x) : ⟦trans_at i f g⟧ = ⟦trans_at j f g⟧ :=
begin
  simp_rw ← from_loop_trans_to_loop,
  have := congr_arg (@group.mul _) (aux_group_indep i j),
  exact congr_fun₂ this ⟦g⟧ ⟦f⟧,
end

lemma symm_at_indep {i} (j) (f : Ω^N X x) : ⟦symm_at i f⟧ = ⟦symm_at j f⟧ :=
begin
  simp_rw ← from_loop_symm_to_loop,
  have := congr_arg (@group.inv _) (aux_group_indep i j),
  exact congr_fun this ⟦f⟧,
end

/-- Characterization of multiplicative identity -/
lemma one_def [nonempty N] : (1 : homotopy_group N X x) = ⟦const⟧ := rfl

/-- Characterization of multiplication -/
lemma mul_spec [nonempty N] {i} {p q : Ω^N X x} :
  (⟦p⟧ * ⟦q⟧ : homotopy_group N X x) = ⟦trans_at i q p⟧ :=
by { rw [trans_at_indep _ q, ← from_loop_trans_to_loop], apply quotient.sound, refl }

/-- Characterization of multiplicative inverse -/
lemma inv_spec [nonempty N] {i} {p : Ω^N X x} : (⟦p⟧⁻¹ : homotopy_group N X x) = ⟦symm_at i p⟧ :=
by { rw [symm_at_indep _ p, ← from_loop_symm_to_loop], apply quotient.sound, refl }

/-- Multiplication on `homotopy_group N X x` is commutative for nontrivial `N`.
  In particular, multiplication on `π_(n+2)` is commutative. -/
instance comm_group [nontrivial N] : comm_group (homotopy_group N X x) :=
let h := exists_ne (classical.arbitrary N) in
@eckmann_hilton.comm_group (homotopy_group N X x) _ 1 (is_unital_aux_group h.some) _
begin
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩,
  apply congr_arg quotient.mk,
  simp only [from_loop_trans_to_loop, trans_at_distrib h.some_spec,
    coe_to_equiv, loop_homeo_apply, coe_symm_to_equiv, loop_homeo_symm_apply],
end

end homotopy_group
