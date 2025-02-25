/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.computation.translations
import algebra.continued_fractions.terminated_stable
import algebra.continued_fractions.continuants_recurrence
import order.filter.at_top_bot
import tactic.field_simp

/-!
# Correctness of Terminating Continued Fraction Computations (`generalized_continued_fraction.of`)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We show the correctness of the
algorithm computing continued fractions (`generalized_continued_fraction.of`) in case of termination
in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the last
denominator of the fraction described by `(generalized_continued_fraction.of v).convergents' n`.
The residual term will be zero exactly when the continued fraction terminated; otherwise, the
residual term will be given by the fractional part stored in
`generalized_continued_fraction.int_fract_pair.stream v n`.

For an example, refer to
`generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some` and for more
information about the computation process, refer to `algebra.continued_fraction.computation.basic`.

## Main definitions

- `generalized_continued_fraction.comp_exact_value` can be used to compute the exact value
 approximated by the continued fraction `generalized_continued_fraction.of v` by adding a residual
 term as described in the summary.

## Main Theorems

- `generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some` shows that
 `generalized_continued_fraction.comp_exact_value` indeed returns the value `v` when given the
 convergent and fractional part as described in the summary.
- `generalized_continued_fraction.of_correctness_of_terminated_at` shows the equality
 `v = (generalized_continued_fraction.of v).convergents n` if `generalized_continued_fraction.of v`
 terminated at position `n`.
-/

namespace generalized_continued_fraction
open generalized_continued_fraction (of)

variables {K : Type*} [linear_ordered_field K] {v : K} {n : ℕ}

/--
Given two continuants `pconts` and `conts` and a value `fr`, this function returns
- `conts.a / conts.b` if `fr = 0`
- `exact_conts.a / exact_conts.b` where `exact_conts = next_continuants 1 fr⁻¹ pconts conts`
 otherwise.

This function can be used to compute the exact value approxmated by a continued fraction
`generalized_continued_fraction.of v` as described in lemma
`comp_exact_value_correctness_of_stream_eq_some`.
-/
protected def comp_exact_value
 (pconts conts : pair K) (fr : K) : K :=
-- if the fractional part is zero, we exactly approximated the value by the last continuants
if fr = 0 then conts.a / conts.b
-- otherwise, we have to include the fractional part in a final continuants step.
else let exact_conts := next_continuants 1 fr⁻¹ pconts conts in
 exact_conts.a / exact_conts.b

variable [floor_ring K]

/-- Just a computational lemma we need for the next main proof. -/
protected lemma comp_exact_value_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
 (fract_a_ne_zero : int.fract a ≠ 0) :
 ((⌊a⌋ : K) * b + c) / (int.fract a) + b = (b * a + c) / int.fract a :=
by { field_simp [fract_a_ne_zero], rw int.fract, ring }

open generalized_continued_fraction
 (comp_exact_value comp_exact_value_correctness_of_stream_eq_some_aux_comp)

/--
Shows the correctness of `comp_exact_value` in case the continued fraction
`generalized_continued_fraction.of v` did not terminate at position `n`. That is, we obtain the
value `v` if we pass the two successive (auxiliary) continuants at positions `n` and `n + 1` as well
as the fractional part at `int_fract_pair.stream n` to `comp_exact_value`.

The correctness might be seen more readily if one uses `convergents'` to evaluate the continued
fraction. Here is an example to illustrate the idea:

Let `(v : ℚ) := 3.4`. We have
- `generalized_continued_fraction.int_fract_pair.stream v 0 = some ⟨3, 0.4⟩`, and
- `generalized_continued_fraction.int_fract_pair.stream v 1 = some ⟨2, 0.5⟩`.
Now `(generalized_continued_fraction.of v).convergents' 1 = 3 + 1/2`, and our fractional term at
position `2` is `0.5`. We hence have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`. This computation
corresponds exactly to the one using the recurrence equation in `comp_exact_value`.
-/
lemma comp_exact_value_correctness_of_stream_eq_some :
 ∀ {ifp_n : int_fract_pair K}, int_fract_pair.stream v n = some ifp_n →
 v = comp_exact_value ((of v).continuants_aux n) ((of v).continuants_aux $ n + 1) ifp_n.fr :=
begin
 let g := of v,
 induction n with n IH,
 { assume ifp_zero stream_zero_eq, -- nat.zero
 have : int_fract_pair.of v = ifp_zero, by
 { have : int_fract_pair.stream v 0 = some (int_fract_pair.of v), from rfl,
 simpa only [this] using stream_zero_eq },
 cases this,
 cases decidable.em (int.fract v = 0) with fract_eq_zero fract_ne_zero,
 -- int.fract v = 0; we must then have `v = ⌊v⌋`
 { suffices : v = ⌊v⌋,
 by simpa [continuants_aux, fract_eq_zero, comp_exact_value],
 calc
 v = int.fract v + ⌊v⌋ : by rw int.fract_add_floor
 ... = ⌊v⌋ : by simp [fract_eq_zero] },
 -- int.fract v ≠ 0; the claim then easily follows by unfolding a single computation step
 { field_simp [continuants_aux, next_continuants, next_numerator, next_denominator,
 of_h_eq_floor, comp_exact_value, fract_ne_zero] } },
 { assume ifp_succ_n succ_nth_stream_eq, -- nat.succ
 obtain ⟨ifp_n, nth_stream_eq, nth_fract_ne_zero, -⟩ :
 ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
 ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n, from
 int_fract_pair.succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq,
 -- introduce some notation
 let conts := g.continuants_aux (n + 2),
 set pconts := g.continuants_aux (n + 1) with pconts_eq,
 set ppconts := g.continuants_aux n with ppconts_eq,
 cases decidable.em (ifp_succ_n.fr = 0) with ifp_succ_n_fr_eq_zero ifp_succ_n_fr_ne_zero,
 -- ifp_succ_n.fr = 0
 { suffices : v = conts.a / conts.b, by
 simpa [comp_exact_value, ifp_succ_n_fr_eq_zero],
 -- use the IH and the fact that ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ to prove this case
 obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_inv_eq_floor⟩ :
 ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋, from
 int_fract_pair.exists_succ_nth_stream_of_fr_zero succ_nth_stream_eq ifp_succ_n_fr_eq_zero,
 have : ifp_n' = ifp_n, by injection (eq.trans (nth_stream_eq').symm nth_stream_eq),
 cases this,
 have s_nth_eq : g.s.nth n = some ⟨1, ⌊ifp_n.fr⁻¹⌋⟩, from
 nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero nth_stream_eq nth_fract_ne_zero,
 rw [←ifp_n_fract_inv_eq_floor] at s_nth_eq,
 suffices : v = comp_exact_value ppconts pconts ifp_n.fr, by
 simpa [conts, continuants_aux, s_nth_eq, comp_exact_value, nth_fract_ne_zero] using this,
 exact (IH nth_stream_eq) },
 -- ifp_succ_n.fr ≠ 0
 { -- use the IH to show that the following equality suffices
 suffices : comp_exact_value ppconts pconts ifp_n.fr =
 comp_exact_value pconts conts ifp_succ_n.fr, by
 { have : v = comp_exact_value ppconts pconts ifp_n.fr,
 from IH nth_stream_eq,
 conv_lhs { rw this }, assumption },
 -- get the correspondence between ifp_n and ifp_succ_n
 obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_ne_zero, ⟨refl⟩⟩ :
 ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
 ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n, from
 int_fract_pair.succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq,
 have : ifp_n' = ifp_n, by injection (eq.trans (nth_stream_eq').symm nth_stream_eq),
 cases this,
 -- get the correspondence between ifp_n and g.s.nth n
 have s_nth_eq : g.s.nth n = some ⟨1, (⌊ifp_n.fr⁻¹⌋ : K)⟩, from
 nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero nth_stream_eq ifp_n_fract_ne_zero,
 -- the claim now follows by unfolding the definitions and tedious calculations
 -- some shorthand notation
 let ppA := ppconts.a, let ppB := ppconts.b,
 let pA := pconts.a, let pB := pconts.b,
 have : comp_exact_value ppconts pconts ifp_n.fr
 = (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB), by
 -- unfold comp_exact_value and the convergent computation once
 { field_simp [ifp_n_fract_ne_zero, comp_exact_value,
 next_continuants, next_numerator, next_denominator], ac_refl },
 rw this,
 -- two calculations needed to show the claim
 have tmp_calc :=
 comp_exact_value_correctness_of_stream_eq_some_aux_comp pA ppA ifp_succ_n_fr_ne_zero,
 have tmp_calc' :=
 comp_exact_value_correctness_of_stream_eq_some_aux_comp pB ppB ifp_succ_n_fr_ne_zero,
 rw inv_eq_one_div at tmp_calc tmp_calc',
 have : int.fract (1 / ifp_n.fr) ≠ 0, by simpa using ifp_succ_n_fr_ne_zero,
 -- now unfold the recurrence one step and simplify both sides to arrive at the conclusion
 field_simp [conts, comp_exact_value,
 (continuants_aux_recurrence s_nth_eq ppconts_eq pconts_eq), next_continuants,
 next_numerator, next_denominator, this, tmp_calc, tmp_calc'],
 ac_refl } }
end

open generalized_continued_fraction (of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none)

/-- The convergent of `generalized_continued_fraction.of v` at step `n - 1` is exactly `v` if the
`int_fract_pair.stream` of the corresponding continued fraction terminated at step `n`. -/
lemma of_correctness_of_nth_stream_eq_none
 (nth_stream_eq_none : int_fract_pair.stream v n = none) :
 v = (of v).convergents (n - 1) :=
begin
 induction n with n IH,
 case nat.zero { contradiction }, -- int_fract_pair.stream v 0 ≠ none
 case nat.succ
 { rename nth_stream_eq_none succ_nth_stream_eq_none,
 let g := of v,
 change v = g.convergents n,
 have : int_fract_pair.stream v n = none
 ∨ ∃ ifp, int_fract_pair.stream v n = some ifp ∧ ifp.fr = 0, from
 int_fract_pair.succ_nth_stream_eq_none_iff.elim_left succ_nth_stream_eq_none,
 rcases this with ⟨nth_stream_eq_none⟩ | ⟨ifp_n, nth_stream_eq, nth_stream_fr_eq_zero⟩,
 { cases n with n',
 { contradiction }, -- int_fract_pair.stream v 0 ≠ none
 { have : g.terminated_at n', from
 of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none.elim_right
 nth_stream_eq_none,
 have : g.convergents (n' + 1) = g.convergents n', from
 convergents_stable_of_terminated n'.le_succ this,
 rw this,
 exact (IH nth_stream_eq_none) } },
 { simpa [nth_stream_fr_eq_zero, comp_exact_value] using
 (comp_exact_value_correctness_of_stream_eq_some nth_stream_eq) } }
end

/--
If `generalized_continued_fraction.of v` terminated at step `n`, then the `n`th convergent is
exactly `v`.
-/
theorem of_correctness_of_terminated_at (terminated_at_n : (of v).terminated_at n) :
 v = (of v).convergents n :=
have int_fract_pair.stream v (n + 1) = none, from
 of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none.elim_left terminated_at_n,
of_correctness_of_nth_stream_eq_none this

/--
If `generalized_continued_fraction.of v` terminates, then there is `n : ℕ` such that the `n`th
convergent is exactly `v`.
-/
lemma of_correctness_of_terminates (terminates : (of v).terminates) :
 ∃ (n : ℕ), v = (of v).convergents n :=
exists.elim terminates
( assume n terminated_at_n,
 exists.intro n (of_correctness_of_terminated_at terminated_at_n) )

open filter

/--
If `generalized_continued_fraction.of v` terminates, then its convergents will eventually always
be `v`.
-/
lemma of_correctness_at_top_of_terminates (terminates : (of v).terminates) :
 ∀ᶠ n in at_top, v = (of v).convergents n :=
begin
 rw eventually_at_top,
 obtain ⟨n, terminated_at_n⟩ : ∃ n, (of v).terminated_at n,
 from terminates,
 use n,
 assume m m_geq_n,
 rw (convergents_stable_of_terminated m_geq_n terminated_at_n),
 exact of_correctness_of_terminated_at terminated_at_n
end

end generalized_continued_fraction

