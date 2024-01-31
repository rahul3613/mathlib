/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.lipschitz
import topology.uniform_space.complete_separated

/-!
# Antilipschitz functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a map `f : α → β` between two (extended) metric spaces is
`antilipschitz_with K`, `K ≥ 0`, if for all `x, y` we have `edist x y ≤ K * edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `dist x y ≤ K * dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjuction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/

variables {α : Type*} {β : Type*} {γ : Type*}

open_locale nnreal ennreal uniformity
open set filter bornology

/-- We say that `f : α → β` is `antilipschitz_with K` if for any two points `x`, `y` we have
`edist x y ≤ K * edist (f x) (f y)`. -/
def antilipschitz_with [pseudo_emetric_space α] [pseudo_emetric_space β] (K : ℝ≥0) (f : α → β) :=
∀ x y, edist x y ≤ K * edist (f x) (f y)

lemma antilipschitz_with.edist_lt_top [pseudo_emetric_space α] [pseudo_metric_space β] {K : ℝ≥0}
  {f : α → β} (h : antilipschitz_with K f) (x y : α) : edist x y < ⊤ :=
(h x y).trans_lt $ ennreal.mul_lt_top ennreal.coe_ne_top (edist_ne_top _ _)

lemma antilipschitz_with.edist_ne_top [pseudo_emetric_space α] [pseudo_metric_space β] {K : ℝ≥0}
  {f : α → β} (h : antilipschitz_with K f) (x y : α) : edist x y ≠ ⊤ :=
(h.edist_lt_top x y).ne

section metric

variables [pseudo_metric_space α] [pseudo_metric_space β] {K : ℝ≥0} {f : α → β}

lemma antilipschitz_with_iff_le_mul_nndist :
  antilipschitz_with K f ↔ ∀ x y, nndist x y ≤ K * nndist (f x) (f y) :=
by { simp only [antilipschitz_with, edist_nndist], norm_cast }

alias antilipschitz_with_iff_le_mul_nndist ↔ antilipschitz_with.le_mul_nndist
  antilipschitz_with.of_le_mul_nndist

lemma antilipschitz_with_iff_le_mul_dist :
  antilipschitz_with K f ↔ ∀ x y, dist x y ≤ K * dist (f x) (f y) :=
by { simp only [antilipschitz_with_iff_le_mul_nndist, dist_nndist], norm_cast }

alias antilipschitz_with_iff_le_mul_dist ↔ antilipschitz_with.le_mul_dist
  antilipschitz_with.of_le_mul_dist

namespace antilipschitz_with

lemma mul_le_nndist (hf : antilipschitz_with K f) (x y : α) :
  K⁻¹ * nndist x y ≤ nndist (f x) (f y) :=
by simpa only [div_eq_inv_mul] using nnreal.div_le_of_le_mul' (hf.le_mul_nndist x y)

lemma mul_le_dist (hf : antilipschitz_with K f) (x y : α) :
  (K⁻¹ * dist x y : ℝ) ≤ dist (f x) (f y) :=
by exact_mod_cast hf.mul_le_nndist x y

end antilipschitz_with

end metric

namespace antilipschitz_with

variables [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]
variables {K : ℝ≥0} {f : α → β}

open emetric

/-- Extract the constant from `hf : antilipschitz_with K f`. This is useful, e.g.,
if `K` is given by a long formula, and we want to reuse this value. -/
@[nolint unused_arguments] -- uses neither `f` nor `hf`
protected def K (hf : antilipschitz_with K f) : ℝ≥0 := K

protected lemma injective {α : Type*} {β : Type*} [emetric_space α] [pseudo_emetric_space β]
  {K : ℝ≥0} {f : α → β} (hf : antilipschitz_with K f) : function.injective f :=
λ x y h, by simpa only [h, edist_self, mul_zero, edist_le_zero] using hf x y

lemma mul_le_edist (hf : antilipschitz_with K f) (x y : α) :
  (K⁻¹ * edist x y : ℝ≥0∞) ≤ edist (f x) (f y) :=
begin
  rw [mul_comm, ← div_eq_mul_inv],
  exact ennreal.div_le_of_le_mul' (hf x y)
end

lemma ediam_preimage_le (hf : antilipschitz_with K f) (s : set β) : diam (f ⁻¹' s) ≤ K * diam s :=
diam_le $ λ x hx y hy, (hf x y).trans $ mul_le_mul_left' (edist_le_diam_of_mem hx hy) K

lemma le_mul_ediam_image (hf : antilipschitz_with K f) (s : set α) : diam s ≤ K * diam (f '' s) :=
(diam_mono (subset_preimage_image _ _)).trans (hf.ediam_preimage_le (f '' s))

protected lemma id : antilipschitz_with 1 (id : α → α) :=
λ x y, by simp only [ennreal.coe_one, one_mul, id, le_refl]

lemma comp {Kg : ℝ≥0} {g : β → γ} (hg : antilipschitz_with Kg g)
  {Kf : ℝ≥0} {f : α → β} (hf : antilipschitz_with Kf f) :
  antilipschitz_with (Kf * Kg) (g ∘ f) :=
λ x y,
calc edist x y ≤ Kf * edist (f x) (f y) : hf x y
... ≤ Kf * (Kg * edist (g (f x)) (g (f y))) : ennreal.mul_left_mono (hg _ _)
... = _ : by rw [ennreal.coe_mul, mul_assoc]

lemma restrict (hf : antilipschitz_with K f) (s : set α) :
  antilipschitz_with K (s.restrict f) :=
λ x y, hf x y

lemma cod_restrict (hf : antilipschitz_with K f) {s : set β} (hs : ∀ x, f x ∈ s) :
  antilipschitz_with K (s.cod_restrict f hs) :=
λ x y, hf x y

lemma to_right_inv_on' {s : set α} (hf : antilipschitz_with K (s.restrict f))
  {g : β → α} {t : set β} (g_maps : maps_to g t s) (g_inv : right_inv_on g f t) :
  lipschitz_with K (t.restrict g) :=
λ x y, by simpa only [restrict_apply, g_inv x.mem, g_inv y.mem, subtype.edist_eq, subtype.coe_mk]
  using hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩

lemma to_right_inv_on (hf : antilipschitz_with K f) {g : β → α} {t : set β}
  (h : right_inv_on g f t) :
  lipschitz_with K (t.restrict g) :=
(hf.restrict univ).to_right_inv_on' (maps_to_univ g t) h

lemma to_right_inverse (hf : antilipschitz_with K f) {g : β → α} (hg : function.right_inverse g f) :
  lipschitz_with K g :=
begin
  intros x y,
  have := hf (g x) (g y),
  rwa [hg x, hg y] at this
end

lemma comap_uniformity_le (hf : antilipschitz_with K f) :
  (𝓤 β).comap (prod.map f f) ≤ 𝓤 α :=
begin
  refine ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).2 (λ ε h₀, _),
  refine ⟨K⁻¹ * ε, ennreal.mul_pos (ennreal.inv_ne_zero.2 ennreal.coe_ne_top) h₀.ne', _⟩,
  refine λ x hx, (hf x.1 x.2).trans_lt _,
  rw [mul_comm, ← div_eq_mul_inv] at hx,
  rw mul_comm,
  exact ennreal.mul_lt_of_lt_div hx
end

protected lemma uniform_inducing (hf : antilipschitz_with K f) (hfc : uniform_continuous f) :
  uniform_inducing f :=
⟨le_antisymm hf.comap_uniformity_le hfc.le_comap⟩

protected lemma uniform_embedding {α : Type*} {β : Type*} [emetric_space α] [pseudo_emetric_space β]
  {K : ℝ≥0} {f : α → β} (hf : antilipschitz_with K f) (hfc : uniform_continuous f) :
  uniform_embedding f :=
⟨hf.uniform_inducing hfc, hf.injective⟩

lemma is_complete_range [complete_space α] (hf : antilipschitz_with K f)
  (hfc : uniform_continuous f) : is_complete (range f) :=
(hf.uniform_inducing hfc).is_complete_range

lemma is_closed_range {α β : Type*} [pseudo_emetric_space α] [emetric_space β] [complete_space α]
  {f : α → β} {K : ℝ≥0} (hf : antilipschitz_with K f) (hfc : uniform_continuous f) :
  is_closed (range f) :=
(hf.is_complete_range hfc).is_closed

lemma closed_embedding {α : Type*} {β : Type*} [emetric_space α] [emetric_space β] {K : ℝ≥0}
  {f : α → β} [complete_space α] (hf : antilipschitz_with K f) (hfc : uniform_continuous f) :
  closed_embedding f :=
{ closed_range := hf.is_closed_range hfc,
  .. (hf.uniform_embedding hfc).embedding }

lemma subtype_coe (s : set α) : antilipschitz_with 1 (coe : s → α) :=
antilipschitz_with.id.restrict s

lemma of_subsingleton [subsingleton α] {K : ℝ≥0} : antilipschitz_with K f :=
λ x y, by simp only [subsingleton.elim x y, edist_self, zero_le]

/-- If `f : α → β` is `0`-antilipschitz, then `α` is a `subsingleton`. -/
protected lemma subsingleton {α β} [emetric_space α] [pseudo_emetric_space β] {f : α → β}
  (h : antilipschitz_with 0 f) : subsingleton α :=
⟨λ x y, edist_le_zero.1 $ (h x y).trans_eq $ zero_mul _⟩

end antilipschitz_with

namespace antilipschitz_with

open metric

variables [pseudo_metric_space α] [pseudo_metric_space β] [pseudo_metric_space γ]
variables {K : ℝ≥0} {f : α → β}

lemma bounded_preimage (hf : antilipschitz_with K f)
  {s : set β} (hs : bounded s) :
  bounded (f ⁻¹' s) :=
exists.intro (K * diam s) $ λ x hx y hy,
calc dist x y ≤ K * dist (f x) (f y) : hf.le_mul_dist x y
... ≤ K * diam s : mul_le_mul_of_nonneg_left (dist_le_diam_of_mem hs hx hy) K.2

lemma tendsto_cobounded (hf : antilipschitz_with K f) : tendsto f (cobounded α) (cobounded β) :=
compl_surjective.forall.2 $ λ s (hs : is_bounded s), metric.is_bounded_iff.2 $
  hf.bounded_preimage $ metric.is_bounded_iff.1 hs

/-- The image of a proper space under an expanding onto map is proper. -/
protected lemma proper_space {α : Type*} [metric_space α] {K : ℝ≥0} {f : α → β} [proper_space α]
  (hK : antilipschitz_with K f) (f_cont : continuous f) (hf : function.surjective f) :
  proper_space β :=
begin
  apply proper_space_of_compact_closed_ball_of_le 0 (λx₀ r hr, _),
  let K := f ⁻¹' (closed_ball x₀ r),
  have A : is_closed K := is_closed_ball.preimage f_cont,
  have B : bounded K := hK.bounded_preimage bounded_closed_ball,
  have : is_compact K := is_compact_iff_is_closed_bounded.2 ⟨A, B⟩,
  convert this.image f_cont,
  exact (hf.image_preimage _).symm
end

lemma bounded_of_image2_left (f : α → β → γ) {K₁ : ℝ≥0}
  (hf : ∀ b, antilipschitz_with K₁ (λ a, f a b))
  {s : set α} {t : set β} (hst : bounded (set.image2 f s t)) :
  bounded s ∨ bounded t :=
begin
  contrapose! hst,
  obtain ⟨b, hb⟩ : t.nonempty := nonempty_of_unbounded hst.2,
  have : ¬bounded (set.image2 f s {b}),
  { intro h,
    apply hst.1,
    rw set.image2_singleton_right at h,
    replace h := (hf b).bounded_preimage h,
    refine h.mono (subset_preimage_image _ _) },
  exact mt (bounded.mono (image2_subset subset.rfl (singleton_subset_iff.mpr hb))) this,
end

lemma bounded_of_image2_right {f : α → β → γ} {K₂ : ℝ≥0}
  (hf : ∀ a, antilipschitz_with K₂ (f a))
  {s : set α} {t : set β} (hst : bounded (set.image2 f s t)) :
  bounded s ∨ bounded t :=
or.symm $ bounded_of_image2_left (flip f) hf $ image2_swap f s t ▸ hst

end antilipschitz_with

lemma lipschitz_with.to_right_inverse [pseudo_emetric_space α] [pseudo_emetric_space β] {K : ℝ≥0}
  {f : α → β} (hf : lipschitz_with K f) {g : β → α} (hg : function.right_inverse g f) :
  antilipschitz_with K g :=
λ x y, by simpa only [hg _] using hf (g x) (g y)

/-- The preimage of a proper space under a Lipschitz homeomorphism is proper. -/
@[protected]
theorem lipschitz_with.proper_space [pseudo_metric_space α] [metric_space β] [proper_space β]
  {K : ℝ≥0} {f : α ≃ₜ β} (hK : lipschitz_with K f) :
  proper_space α :=
(hK.to_right_inverse f.right_inv).proper_space f.symm.continuous f.symm.surjective
