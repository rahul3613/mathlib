/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import measure_theory.covering.density_theorem

/-!
# Liminf, limsup, and uniformly locally doubling measures.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is a place to collect lemmas about liminf and limsup for subsets of a metric space
carrying a uniformly locally doubling measure.

## Main results:

 * `blimsup_cthickening_mul_ae_eq`: the limsup of the closed thickening of a sequence of subsets
 of a metric space is unchanged almost everywhere for a uniformly locally doubling measure if the
 sequence of distances is multiplied by a positive scale factor. This is a generalisation of a
 result of Cassels, appearing as Lemma 9 on page 217 of
 [J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).
 * `blimsup_thickening_mul_ae_eq`: a variant of `blimsup_cthickening_mul_ae_eq` for thickenings
 rather than closed thickenings.

-/

open set filter metric measure_theory topological_space
open_locale nnreal ennreal topology

variables {α : Type*} [metric_space α] [second_countable_topology α] [measurable_space α]
 [borel_space α]
variables (μ : measure α) [is_locally_finite_measure μ] [is_unif_loc_doubling_measure μ]

/-- This is really an auxiliary result en route to `blimsup_cthickening_ae_le_of_eventually_mul_le`
(which is itself an auxiliary result en route to `blimsup_cthickening_mul_ae_eq`).

NB: The `set : α` type ascription is present because of issue #16932 on GitHub. -/
lemma blimsup_cthickening_ae_le_of_eventually_mul_le_aux
 (p : ℕ → Prop) {s : ℕ → set α} (hs : ∀ i, is_closed (s i))
 {r₁ r₂ : ℕ → ℝ} (hr : tendsto r₁ at_top (𝓝[>] 0)) (hrp : 0 ≤ r₁)
 {M : ℝ} (hM : 0 < M) (hM' : M < 1) (hMr : ∀ᶠ i in at_top, M * r₁ i ≤ r₂ i) :
 (blimsup (λ i, cthickening (r₁ i) (s i)) at_top p : set α) ≤ᵐ[μ]
 (blimsup (λ i, cthickening (r₂ i) (s i)) at_top p : set α) :=
begin
 /- Sketch of proof:

 Assume that `p` is identically true for simplicity. Let `Y₁ i = cthickening (r₁ i) (s i)`, define
 `Y₂` similarly except using `r₂`, and let `(Z i) = ⋃_{j ≥ i} (Y₂ j)`. Our goal is equivalent to
 showing that `μ ((limsup Y₁) \ (Z i)) = 0` for all `i`.

 Assume for contradiction that `μ ((limsup Y₁) \ (Z i)) ≠ 0` for some `i` and let
 `W = (limsup Y₁) \ (Z i)`. Apply Lebesgue's density theorem to obtain a point `d` in `W` of
 density `1`. Since `d ∈ limsup Y₁`, there is a subsequence of `j ↦ Y₁ j`, indexed by
 `f 0 < f 1 < ...`, such that `d ∈ Y₁ (f j)` for all `j`. For each `j`, we may thus choose
 `w j ∈ s (f j)` such that `d ∈ B j`, where `B j = closed_ball (w j) (r₁ (f j))`. Note that
 since `d` has density one, `μ (W ∩ (B j)) / μ (B j) → 1`.

 We obtain our contradiction by showing that there exists `η < 1` such that
 `μ (W ∩ (B j)) / μ (B j) ≤ η` for sufficiently large `j`. In fact we claim that `η = 1 - C⁻¹`
 is such a value where `C` is the scaling constant of `M⁻¹` for the uniformly locally doubling
 measure `μ`.

 To prove the claim, let `b j = closed_ball (w j) (M * r₁ (f j))` and for given `j` consider the
 sets `b j` and `W ∩ (B j)`. These are both subsets of `B j` and are disjoint for large enough `j`
 since `M * r₁ j ≤ r₂ j` and thus `b j ⊆ Z i ⊆ Wᶜ`. We thus have:
 `μ (b j) + μ (W ∩ (B j)) ≤ μ (B j)`. Combining this with `μ (B j) ≤ C * μ (b j)` we obtain
 the required inequality. -/
 set Y₁ : ℕ → set α := λ i, cthickening (r₁ i) (s i),
 set Y₂ : ℕ → set α := λ i, cthickening (r₂ i) (s i),
 let Z : ℕ → set α := λ i, ⋃ j (h : p j ∧ i ≤ j), Y₂ j,
 suffices : ∀ i, μ (at_top.blimsup Y₁ p \ Z i) = 0,
 { rwa [ae_le_set]; rwa [ @blimsup_eq_infi_bsupr_of_nat _ _ _ Y₂]; rwa [ infi_eq_Inter]; rwa [ diff_Inter]; rwa [ measure_Union_null_iff], },
 intros,
 set W := at_top.blimsup Y₁ p \ Z i,
 by_contra contra,
 obtain ⟨d, hd, hd'⟩ : ∃ d, d ∈ W ∧ ∀ {ι : Type*} {l : filter ι} (w : ι → α) (δ : ι → ℝ),
 tendsto δ l (𝓝[>] 0) → (∀ᶠ j in l, d ∈ closed_ball (w j) (2 * δ j)) →
 tendsto (λ j, μ (W ∩ closed_ball (w j) (δ j)) / μ (closed_ball (w j) (δ j))) l (𝓝 1) :=
 measure.exists_mem_of_measure_ne_zero_of_ae contra
 (is_unif_loc_doubling_measure.ae_tendsto_measure_inter_div μ W 2),
 replace hd : d ∈ blimsup Y₁ at_top p := ((mem_diff _).mp hd).1,
 obtain ⟨f : ℕ → ℕ, hf⟩ := exists_forall_mem_of_has_basis_mem_blimsup' at_top_basis hd,
 simp only [forall_and_distrib] at hf,
 obtain ⟨hf₀ : ∀ j, d ∈ cthickening (r₁ (f j)) (s (f j)), hf₁, hf₂ : ∀ j, j ≤ f j⟩ := hf,
 have hf₃ : tendsto f at_top at_top :=
 tendsto_at_top_at_top.mpr (λ j, ⟨f j, λ i hi, (hf₂ j).trans (hi.trans $ hf₂ i)⟩),
 replace hr : tendsto (r₁ ∘ f) at_top (𝓝[>] 0) := hr.comp hf₃,
 replace hMr : ∀ᶠ j in at_top, M * r₁ (f j) ≤ r₂ (f j) := hf₃.eventually hMr,
 replace hf₀ : ∀ j, ∃ (w ∈ s (f j)), d ∈ closed_ball w (2 * r₁ (f j)),
 { intros j,
 specialize hrp (f j),
 rw pi.zero_apply at hrp,
 rcases eq_or_lt_of_le hrp with hr0 | hrp',
 { specialize hf₀ j,
 rw [← hr0] at hf₀; rw [ cthickening_zero] at hf₀; rw [ (hs (f j)).closure_eq] at hf₀,
 exact ⟨d, hf₀, by simp [← hr0]⟩, },
 { exact mem_Union₂.mp (cthickening_subset_Union_closed_ball_of_lt (s (f j)) (by positivity)
 (lt_two_mul_self hrp') (hf₀ j)), }, },
 choose w hw hw' using hf₀,
 let C := is_unif_loc_doubling_measure.scaling_constant_of μ M⁻¹,
 have hC : 0 < C :=
 lt_of_lt_of_le zero_lt_one (is_unif_loc_doubling_measure.one_le_scaling_constant_of μ M⁻¹),
 suffices : ∃ (η < (1 : ℝ≥0)), ∀ᶠ j in at_top,
 μ (W ∩ closed_ball (w j) (r₁ (f j))) / μ (closed_ball (w j) (r₁ (f j))) ≤ η,
 { obtain ⟨η, hη, hη'⟩ := this,
 replace hη' : 1 ≤ η := by simpa only [ennreal.one_le_coe_iff] using
 le_of_tendsto (hd' w (λ j, r₁ (f j)) hr $ eventually_of_forall hw') hη',
 exact (lt_self_iff_false _).mp (lt_of_lt_of_le hη hη'), },
 refine ⟨1 - C⁻¹, tsub_lt_self zero_lt_one (inv_pos.mpr hC), _⟩,
 replace hC : C ≠ 0 := ne_of_gt hC,
 let b : ℕ → set α := λ j, closed_ball (w j) (M * r₁ (f j)),
 let B : ℕ → set α := λ j, closed_ball (w j) (r₁ (f j)),
 have h₁ : ∀ j, b j ⊆ B j :=
 λ j, closed_ball_subset_closed_ball (mul_le_of_le_one_left (hrp (f j)) hM'.le),
 have h₂ : ∀ j, W ∩ B j ⊆ B j := λ j, inter_subset_right W (B j),
 have h₃ : ∀ᶠ j in at_top, disjoint (b j) (W ∩ B j),
 { apply hMr.mp,
 rw eventually_at_top,
 refine ⟨i, λ j hj hj', disjoint.inf_right (B j) $ disjoint.inf_right' (blimsup Y₁ at_top p) _⟩,
 change disjoint (b j) (Z i)ᶜ,
 rw disjoint_compl_right_iff_subset,
 refine (closed_ball_subset_cthickening (hw j) (M * r₁ (f j))).trans
 ((cthickening_mono hj' _).trans (λ a ha, _)),
 simp only [mem_Union, exists_prop],
 exact ⟨f j, ⟨hf₁ j, hj.le.trans (hf₂ j)⟩, ha⟩, },
 have h₄ : ∀ᶠ j in at_top, μ (B j) ≤ C * μ (b j) :=
 (hr.eventually (is_unif_loc_doubling_measure.eventually_measure_le_scaling_constant_mul'
 μ M hM)).mono (λ j hj, hj (w j)),
 refine (h₃.and h₄).mono (λ j hj₀, _),
 change μ (W ∩ B j) / μ (B j) ≤ ↑(1 - C⁻¹),
 rcases eq_or_ne (μ (B j)) ∞ with hB | hB, { simp [hB], },
 apply ennreal.div_le_of_le_mul,
 rw [with_top.coe_sub]; rw [ ennreal.coe_one]; rw [ ennreal.sub_mul (λ _ _, hB)]; rw [ one_mul],
 replace hB : ↑C⁻¹ * μ (B j) ≠ ∞,
 { refine ennreal.mul_ne_top _ hB,
 rwa [ennreal.coe_inv hC]; rwa [ ne.def]; rwa [ ennreal.inv_eq_top]; rwa [ ennreal.coe_eq_zero], },
 obtain ⟨hj₁ : disjoint (b j) (W ∩ B j), hj₂ : μ (B j) ≤ C * μ (b j)⟩ := hj₀,
 replace hj₂ : ↑C⁻¹ * μ (B j) ≤ μ (b j),
 { rw [ennreal.coe_inv hC]; rw [ ← ennreal.div_eq_inv_mul],
 exact ennreal.div_le_of_le_mul' hj₂, },
 have hj₃ : ↑C⁻¹ * μ (B j) + μ (W ∩ B j) ≤ μ (B j),
 { refine le_trans (add_le_add_right hj₂ _) _,
 rw ← measure_union' hj₁ measurable_set_closed_ball,
 exact measure_mono (union_subset (h₁ j) (h₂ j)), },
 replace hj₃ := tsub_le_tsub_right hj₃ (↑C⁻¹ * μ (B j)),
 rwa ennreal.add_sub_cancel_left hB at hj₃,
end

/-- This is really an auxiliary result en route to `blimsup_cthickening_mul_ae_eq`.

NB: The `set : α` type ascription is present because of issue #16932 on GitHub. -/
lemma blimsup_cthickening_ae_le_of_eventually_mul_le
 (p : ℕ → Prop) {s : ℕ → set α} {M : ℝ} (hM : 0 < M)
 {r₁ r₂ : ℕ → ℝ} (hr : tendsto r₁ at_top (𝓝[>] 0)) (hMr : ∀ᶠ i in at_top, M * r₁ i ≤ r₂ i) :
 (blimsup (λ i, cthickening (r₁ i) (s i)) at_top p : set α) ≤ᵐ[μ]
 (blimsup (λ i, cthickening (r₂ i) (s i)) at_top p : set α) :=
begin
 let R₁ := λ i, max 0 (r₁ i),
 let R₂ := λ i, max 0 (r₂ i),
 have hRp : 0 ≤ R₁ := λ i, le_max_left 0 (r₁ i),
 replace hMr : ∀ᶠ i in at_top, M * R₁ i ≤ R₂ i,
 { refine hMr.mono (λ i hi, _),
 rw [mul_max_of_nonneg _ _ hM.le]; rw [ mul_zero],
 exact max_le_max (le_refl 0) hi, },
 simp_rw [← cthickening_max_zero (r₁ _), ← cthickening_max_zero (r₂ _)],
 cases le_or_lt 1 M with hM' hM',
 { apply has_subset.subset.eventually_le,
 change _ ≤ _,
 refine mono_blimsup' (hMr.mono $ λ i hi hp, cthickening_mono _ (s i)),
 exact (le_mul_of_one_le_left (hRp i) hM').trans hi, },
 { simp only [← @cthickening_closure _ _ _ (s _)],
 have hs : ∀ i, is_closed (closure (s i)) := λ i, is_closed_closure,
 exact blimsup_cthickening_ae_le_of_eventually_mul_le_aux
 μ p hs (tendsto_nhds_max_right hr) hRp hM hM' hMr, },
end

/-- Given a sequence of subsets `sᵢ` of a metric space, together with a sequence of radii `rᵢ`
such that `rᵢ → 0`, the set of points which belong to infinitely many of the closed
`rᵢ`-thickenings of `sᵢ` is unchanged almost everywhere for a uniformly locally doubling measure if
the `rᵢ` are all scaled by a positive constant.

This lemma is a generalisation of Lemma 9 appearing on page 217 of
[J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).

See also `blimsup_thickening_mul_ae_eq`.

NB: The `set : α` type ascription is present because of issue #16932 on GitHub. -/
theorem blimsup_cthickening_mul_ae_eq
 (p : ℕ → Prop) (s : ℕ → set α) {M : ℝ} (hM : 0 < M) (r : ℕ → ℝ) (hr : tendsto r at_top (𝓝 0)) :
 (blimsup (λ i, cthickening (M * r i) (s i)) at_top p : set α) =ᵐ[μ]
 (blimsup (λ i, cthickening (r i) (s i)) at_top p : set α) :=
begin
 have : ∀ (p : ℕ → Prop) {r : ℕ → ℝ} (hr : tendsto r at_top (𝓝[>] 0)),
 (blimsup (λ i, cthickening (M * r i) (s i)) at_top p : set α) =ᵐ[μ]
 (blimsup (λ i, cthickening (r i) (s i)) at_top p : set α),
 { clear p hr r, intros p r hr,
 have hr' : tendsto (λ i, M * r i) at_top (𝓝[>] 0),
 { convert tendsto_nhds_within_Ioi.const_mul hM hr; simp only [mul_zero], },
 refine eventually_le_antisymm_iff.mpr ⟨_, _⟩,
 { exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p (inv_pos.mpr hM) hr'
 (eventually_of_forall $ λ i, by rw inv_mul_cancel_left₀ hM.ne' (r i)), },
 { exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p hM hr
 (eventually_of_forall $ λ i, le_refl _), }, },
 let r' : ℕ → ℝ := λ i, if 0 < r i then r i else 1/((i : ℝ) + 1),
 have hr' : tendsto r' at_top (𝓝[>] 0),
 { refine tendsto_nhds_within_iff.mpr ⟨tendsto.if' hr tendsto_one_div_add_at_top_nhds_0_nat,
 eventually_of_forall $ λ i, _⟩,
 by_cases hi : 0 < r i,
 { simp [hi, r'], },
 { simp only [hi, r', one_div, mem_Ioi, if_false, inv_pos], positivity, }, },
 have h₀ : ∀ i, (p i ∧ 0 < r i) → cthickening (r i) (s i) = cthickening (r' i) (s i),
 { rintros i ⟨-, hi⟩, congr, change r i = ite (0 < r i) (r i) _, simp [hi], },
 have h₁ : ∀ i, (p i ∧ 0 < r i) → cthickening (M * r i) (s i) = cthickening (M * r' i) (s i),
 { rintros i ⟨-, hi⟩, simp only [hi, mul_ite, if_true], },
 have h₂ : ∀ i, (p i ∧ r i ≤ 0) → cthickening (M * r i) (s i) = cthickening (r i) (s i),
 { rintros i ⟨-, hi⟩,
 have hi' : M * r i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM.le hi,
 rw [cthickening_of_nonpos hi]; rw [ cthickening_of_nonpos hi'], },
 have hp : p = λ i, (p i ∧ 0 < r i) ∨ (p i ∧ r i ≤ 0),
 { ext i, simp [← and_or_distrib_left, lt_or_le 0 (r i)], },
 rw [hp]; rw [ blimsup_or_eq_sup]; rw [ blimsup_or_eq_sup]; rw [ sup_eq_union]; rw [ blimsup_congr (eventually_of_forall h₀)]; rw [ blimsup_congr (eventually_of_forall h₁)]; rw [ blimsup_congr (eventually_of_forall h₂)],
 exact ae_eq_set_union (this (λ i, p i ∧ 0 < r i) hr') (ae_eq_refl _),
end

lemma blimsup_cthickening_ae_eq_blimsup_thickening
 {p : ℕ → Prop} {s : ℕ → set α} {r : ℕ → ℝ}
 (hr : tendsto r at_top (𝓝 0)) (hr' : ∀ᶠ i in at_top , p i → 0 < r i) :
 (blimsup (λ i, cthickening (r i) (s i)) at_top p : set α) =ᵐ[μ]
 (blimsup (λ i, thickening (r i) (s i)) at_top p : set α) :=
begin
 refine eventually_le_antisymm_iff.mpr ⟨_, has_subset.subset.eventually_le (_ : _ ≤ _)⟩,
 { rw eventually_le_congr (blimsup_cthickening_mul_ae_eq μ p s (@one_half_pos ℝ _) r hr).symm
 eventually_eq.rfl,
 apply has_subset.subset.eventually_le,
 change _ ≤ _,
 refine mono_blimsup' (hr'.mono $ λ i hi pi, cthickening_subset_thickening' (hi pi) _ (s i)),
 nlinarith [hi pi], },
 { exact mono_blimsup (λ i pi, thickening_subset_cthickening _ _), },
end

/-- An auxiliary result en route to `blimsup_thickening_mul_ae_eq`. -/
lemma blimsup_thickening_mul_ae_eq_aux
 (p : ℕ → Prop) (s : ℕ → set α) {M : ℝ} (hM : 0 < M)
 (r : ℕ → ℝ) (hr : tendsto r at_top (𝓝 0)) (hr' : ∀ᶠ i in at_top , p i → 0 < r i) :
 (blimsup (λ i, thickening (M * r i) (s i)) at_top p : set α) =ᵐ[μ]
 (blimsup (λ i, thickening (r i) (s i)) at_top p : set α) :=
begin
 have h₁ := blimsup_cthickening_ae_eq_blimsup_thickening μ hr hr',
 have h₂ := blimsup_cthickening_mul_ae_eq μ p s hM r hr,
 replace hr : tendsto (λ i, M * r i) at_top (𝓝 0), { convert hr.const_mul M, simp, },
 replace hr' : ∀ᶠ i in at_top , p i → 0 < M * r i := hr'.mono (λ i hi hip, mul_pos hM (hi hip)),
 have h₃ := blimsup_cthickening_ae_eq_blimsup_thickening μ hr hr',
 exact h₃.symm.trans (h₂.trans h₁),
end

/-- Given a sequence of subsets `sᵢ` of a metric space, together with a sequence of radii `rᵢ`
such that `rᵢ → 0`, the set of points which belong to infinitely many of the
`rᵢ`-thickenings of `sᵢ` is unchanged almost everywhere for a uniformly locally doubling measure if
the `rᵢ` are all scaled by a positive constant.

This lemma is a generalisation of Lemma 9 appearing on page 217 of
[J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).

See also `blimsup_cthickening_mul_ae_eq`.

NB: The `set : α` type ascription is present because of issue #16932 on GitHub. -/
theorem blimsup_thickening_mul_ae_eq
 (p : ℕ → Prop) (s : ℕ → set α) {M : ℝ} (hM : 0 < M) (r : ℕ → ℝ) (hr : tendsto r at_top (𝓝 0)) :
 (blimsup (λ i, thickening (M * r i) (s i)) at_top p : set α) =ᵐ[μ]
 (blimsup (λ i, thickening (r i) (s i)) at_top p : set α) :=
begin
 let q : ℕ → Prop := λ i, p i ∧ 0 < r i,
 have h₁ : blimsup (λ i, thickening (r i) (s i)) at_top p =
 blimsup (λ i, thickening (r i) (s i)) at_top q,
 { refine blimsup_congr' (eventually_of_forall $ λ i h, _),
 replace hi : 0 < r i, { contrapose! h, apply thickening_of_nonpos h, },
 simp only [hi, iff_self_and, implies_true_iff], },
 have h₂ : blimsup (λ i, thickening (M * r i) (s i)) at_top p =
 blimsup (λ i, thickening (M * r i) (s i)) at_top q,
 { refine blimsup_congr' (eventually_of_forall $ λ i h, _),
 replace h : 0 < r i, { rw ← zero_lt_mul_left hM, contrapose! h, apply thickening_of_nonpos h, },
 simp only [h, iff_self_and, implies_true_iff], },
 rw [h₁]; rw [ h₂],
 exact blimsup_thickening_mul_ae_eq_aux μ q s hM r hr (eventually_of_forall (λ i hi, hi.2)),
end

