/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import topology.local_homeomorph

/-!
# Local homeomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines local homeomorphisms.

## Main definitions

* `is_locally_homeomorph`: A function `f : X → Y` satisfies `is_locally_homeomorph` if for each
  point `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.

  Note that `is_locally_homeomorph` is a global condition. This is in contrast to
  `local_homeomorph`, which is a homeomorphism between specific open subsets.
-/

open_locale topology

variables {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  (g : Y → Z) (f : X →  Y) (s : set X) (t : set Y)

/-- A function `f : X → Y` satisfies `is_locally_homeomorph_on f s` if each `x ∈ s` is contained in
the source of some `e : local_homeomorph X Y` with `f = e`. -/
def is_locally_homeomorph_on :=
∀ x ∈ s, ∃ e : local_homeomorph X Y, x ∈ e.source ∧ f = e

namespace is_locally_homeomorph_on

/-- Proves that `f` satisfies `is_locally_homeomorph_on f s`. The condition `h` is weaker than the
definition of `is_locally_homeomorph_on f s`, since it only requires `e : local_homeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
lemma mk (h : ∀ x ∈ s, ∃ e : local_homeomorph X Y, x ∈ e.source ∧ ∀ y ∈ e.source, f y = e y) :
  is_locally_homeomorph_on f s :=
begin
  intros x hx,
  obtain ⟨e, hx, he⟩ := h x hx,
  exact ⟨{ to_fun := f,
    map_source' := λ x hx, by rw he x hx; exact e.map_source' hx,
    left_inv' := λ x hx, by rw he x hx; exact e.left_inv' hx,
    right_inv' := λ y hy, by rw he _ (e.map_target' hy); exact e.right_inv' hy,
    continuous_to_fun := (continuous_on_congr he).mpr e.continuous_to_fun,
    .. e }, hx, rfl⟩,
end

variables {g f s t}

lemma map_nhds_eq (hf : is_locally_homeomorph_on f s) {x : X} (hx : x ∈ s) :
  (𝓝 x).map f = 𝓝 (f x) :=
let ⟨e, hx, he⟩ := hf x hx in he.symm ▸ e.map_nhds_eq hx

protected lemma continuous_at (hf : is_locally_homeomorph_on f s) {x : X} (hx : x ∈ s) :
  continuous_at f x :=
(hf.map_nhds_eq hx).le

protected lemma continuous_on (hf : is_locally_homeomorph_on f s) : continuous_on f s :=
continuous_at.continuous_on (λ x, hf.continuous_at)

protected lemma comp (hg : is_locally_homeomorph_on g t) (hf : is_locally_homeomorph_on f s)
  (h : set.maps_to f s t) : is_locally_homeomorph_on (g ∘ f) s :=
begin
  intros x hx,
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx),
  obtain ⟨ef, hxf, rfl⟩ := hf x hx,
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩,
end

end is_locally_homeomorph_on

/-- A function `f : X → Y` satisfies `is_locally_homeomorph f` if each `x : x` is contained in
  the source of some `e : local_homeomorph X Y` with `f = e`. -/
def is_locally_homeomorph :=
∀ x : X, ∃ e : local_homeomorph X Y, x ∈ e.source ∧ f = e

variables {f}

lemma is_locally_homeomorph_iff_is_locally_homeomorph_on_univ :
  is_locally_homeomorph f ↔ is_locally_homeomorph_on f set.univ :=
by simp only [is_locally_homeomorph, is_locally_homeomorph_on, set.mem_univ, forall_true_left]

protected lemma is_locally_homeomorph.is_locally_homeomorph_on (hf : is_locally_homeomorph f) :
  is_locally_homeomorph_on f set.univ :=
is_locally_homeomorph_iff_is_locally_homeomorph_on_univ.mp hf

variables (f)

namespace is_locally_homeomorph

/-- Proves that `f` satisfies `is_locally_homeomorph f`. The condition `h` is weaker than the
definition of `is_locally_homeomorph f`, since it only requires `e : local_homeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
lemma mk (h : ∀ x : X, ∃ e : local_homeomorph X Y, x ∈ e.source ∧ ∀ y ∈ e.source, f y = e y) :
  is_locally_homeomorph f :=
is_locally_homeomorph_iff_is_locally_homeomorph_on_univ.mpr
  (is_locally_homeomorph_on.mk f set.univ (λ x hx, h x))

variables {g f}

lemma map_nhds_eq (hf : is_locally_homeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
hf.is_locally_homeomorph_on.map_nhds_eq (set.mem_univ x)

protected lemma continuous (hf : is_locally_homeomorph f) : continuous f :=
continuous_iff_continuous_on_univ.mpr hf.is_locally_homeomorph_on.continuous_on

protected lemma is_open_map (hf : is_locally_homeomorph f) : is_open_map f :=
is_open_map.of_nhds_le (λ x, ge_of_eq (hf.map_nhds_eq x))

protected lemma comp (hg : is_locally_homeomorph g) (hf : is_locally_homeomorph f) :
  is_locally_homeomorph (g ∘ f) :=
is_locally_homeomorph_iff_is_locally_homeomorph_on_univ.mpr
  (hg.is_locally_homeomorph_on.comp hf.is_locally_homeomorph_on (set.univ.maps_to_univ f))

end is_locally_homeomorph
