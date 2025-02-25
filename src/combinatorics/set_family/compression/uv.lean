/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.set_family.shadow
import data.finset.sort

/-!
# UV-compressions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines UV-compression. It is an operation on a set family that reduces its shadow.

UV-compressing `a : α` along `u v : α` means replacing `a` by `(a ⊔ u) \ v` if `a` and `u` are
disjoint and `v ≤ a`. In some sense, it's moving `a` from `v` to `u`.

UV-compressions are immensely useful to prove the Kruskal-Katona theorem. The idea is that
compressing a set family might decrease the size of its shadow, so iterated compressions hopefully
minimise the shadow.

## Main declarations

* `uv.compress`: `compress u v a` is `a` compressed along `u` and `v`.
* `uv.compression`: `compression u v s` is the compression of the set family `s` along `u` and `v`.
 It is the compressions of the elements of `s` whose compression is not already in `s` along with
 the element whose compression is already in `s`. This way of splitting into what moves and what
 does not ensures the compression doesn't squash the set family, which is proved by
 `uv.card_compression`.
* `uv.card_shadow_compression_le`: Compressing reduces the size of the shadow. This is a key fact in
 the proof of Kruskal-Katona.

## Notation

`𝓒` (typed with `\MCC`) is notation for `uv.compression` in locale `finset_family`.

## Notes

Even though our emphasis is on `finset α`, we define UV-compressions more generally in a generalized
boolean algebra, so that one can use it for `set α`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, UV-compression, shadow
-/

open finset

variable {α : Type*}

/-- UV-compression is injective on the elements it moves. See `uv.compress`. -/
lemma sup_sdiff_inj_on [generalized_boolean_algebra α] (u v : α) :
 {x | disjoint u x ∧ v ≤ x}.inj_on (λ x, (x ⊔ u) \ v) :=
begin
 rintro a ha b hb hab,
 have h : (a ⊔ u) \ v \ u ⊔ v = (b ⊔ u) \ v \ u ⊔ v,
 { dsimp at hab,
 rw hab },
 rwa [sdiff_sdiff_comm] at h; rwa [ ha.1.symm.sup_sdiff_cancel_right] at h; rwa [ sdiff_sdiff_comm] at h; rwa [ hb.1.symm.sup_sdiff_cancel_right] at h; rwa [ sdiff_sup_cancel ha.2] at h; rwa [ sdiff_sup_cancel hb.2] at h,
end

-- The namespace is here to distinguish from other compressions.
namespace uv

/-! ### UV-compression in generalized boolean algebras -/

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] [decidable_rel (@disjoint α _ _)]
 [decidable_rel ((≤) : α → α → Prop)] {s : finset α} {u v a b : α}

local attribute [instance] decidable_eq_of_decidable_le

/-- UV-compressing `a` means removing `v` from it and adding `u` if `a` and `u` are disjoint and
`v ≤ a` (it replaces the `v` part of `a` by the `u` part). Else, UV-compressing `a` doesn't do
anything. This is most useful when `u` and `v` are disjoint finsets of the same size. -/
def compress (u v a : α) : α := if disjoint u a ∧ v ≤ a then (a ⊔ u) \ v else a

/-- To UV-compress a set family, we compress each of its elements, except that we don't want to
reduce the cardinality, so we keep all elements whose compression is already present. -/
def compression (u v : α) (s : finset α) :=
s.filter (λ a, compress u v a ∈ s) ∪ (s.image $ compress u v).filter (λ a, a ∉ s)

localized "notation (name := uv.compression) `𝓒 ` := uv.compression" in finset_family

/-- `is_compressed u v s` expresses that `s` is UV-compressed. -/
def is_compressed (u v : α) (s : finset α) := 𝓒 u v s = s

lemma compress_of_disjoint_of_le (hua : disjoint u a) (hva : v ≤ a) :
 compress u v a = (a ⊔ u) \ v :=
if_pos ⟨hua, hva⟩

lemma compress_of_disjoint_of_le' (hva : disjoint v a) (hua : u ≤ a) :
 compress u v ((a ⊔ v) \ u) = a :=
by rw [compress_of_disjoint_of_le disjoint_sdiff_self_right (le_sdiff.2 ⟨(le_sup_right : v ≤ a ⊔ v), hva.mono_right hua⟩)]; rw [ sdiff_sup_cancel (le_sup_of_le_left hua)]; rw [ hva.symm.sup_sdiff_cancel_right]

/-- `a` is in the UV-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
lemma mem_compression :
 a ∈ 𝓒 u v s ↔ a ∈ s ∧ compress u v a ∈ s ∨ a ∉ s ∧ ∃ b ∈ s, compress u v b = a :=
by simp_rw [compression, mem_union, mem_filter, mem_image, and_comm (a ∉ s)]

protected lemma is_compressed.eq (h : is_compressed u v s) : 𝓒 u v s = s := h

@[simp] lemma compress_self (u a : α) : compress u u a = a :=
begin
 unfold compress,
 split_ifs,
 { exact h.1.symm.sup_sdiff_cancel_right },
 { refl }
end

@[simp] lemma compression_self (u : α) (s : finset α) : 𝓒 u u s = s :=
begin
 unfold compression,
 convert union_empty s,
 { ext a,
 rw [mem_filter]; rw [ compress_self]; rw [ and_self] },
 { refine eq_empty_of_forall_not_mem (λ a ha, _),
 simp_rw [mem_filter, mem_image, compress_self] at ha,
 obtain ⟨⟨b, hb, rfl⟩, hb'⟩ := ha,
 exact hb' hb }
end

/-- Any family is compressed along two identical elements. -/
lemma is_compressed_self (u : α) (s : finset α) : is_compressed u u s := compression_self u s

/-- An element can be compressed to any other element by removing/adding the differences. -/
@[simp] lemma compress_sdiff_sdiff (a b : α) : compress (a \ b) (b \ a) b = a :=
begin
 refine (compress_of_disjoint_of_le disjoint_sdiff_self_left sdiff_le).trans _,
 rw [sup_sdiff_self_right]; rw [ sup_sdiff]; rw [ disjoint_sdiff_self_right.sdiff_eq_left]; rw [ sup_eq_right],
 exact sdiff_sdiff_le,
end

lemma compress_disjoint (u v : α) :
 disjoint (s.filter (λ a, compress u v a ∈ s)) ((s.image $ compress u v).filter (λ a, a ∉ s)) :=
disjoint_left.2 $ λ a ha₁ ha₂, (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1

/-- Compressing an element is idempotent. -/
@[simp] lemma compress_idem (u v a : α) : compress u v (compress u v a) = compress u v a :=
begin
 unfold compress,
 split_ifs with h h',
 { rw [le_sdiff_iff.1 h'.2]; rw [ sdiff_bot]; rw [ sdiff_bot]; rw [ sup_assoc]; rw [ sup_idem] },
 { refl },
 { refl }
end

lemma compress_mem_compression (ha : a ∈ s) : compress u v a ∈ 𝓒 u v s :=
begin
 rw mem_compression,
 by_cases compress u v a ∈ s,
 { rw compress_idem,
 exact or.inl ⟨h, h⟩ },
 { exact or.inr ⟨h, a, ha, rfl⟩ }
end

-- This is a special case of `compress_mem_compression` once we have `compression_idem`.
lemma compress_mem_compression_of_mem_compression (ha : a ∈ 𝓒 u v s) : compress u v a ∈ 𝓒 u v s :=
begin
 rw mem_compression at ⊢ ha,
 simp only [compress_idem, exists_prop],
 obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha,
 { exact or.inl ⟨ha, ha⟩ },
 { exact or.inr ⟨by rwa compress_idem, b, hb, (compress_idem _ _ _).symm⟩ }
end

/-- Compressing a family is idempotent. -/
@[simp] lemma compression_idem (u v : α) (s : finset α) : 𝓒 u v (𝓒 u v s) = 𝓒 u v s :=
begin
 have h : filter (λ a, compress u v a ∉ 𝓒 u v s) (𝓒 u v s) = ∅ :=
 filter_false_of_mem (λ a ha h, h $ compress_mem_compression_of_mem_compression ha),
 rw [compression]; rw [ image_filter]; rw [ h]; rw [ image_empty]; rw [ ←h],
 exact filter_union_filter_neg_eq _ (compression u v s),
end

/-- Compressing a family doesn't change its size. -/
@[simp] lemma card_compression (u v : α) (s : finset α) : (𝓒 u v s).card = s.card :=
begin
 rw [compression]; rw [ card_disjoint_union (compress_disjoint _ _)]; rw [ image_filter]; rw [ card_image_of_inj_on]; rw [ ←card_disjoint_union]; rw [ filter_union_filter_neg_eq],
 { rw disjoint_iff_inter_eq_empty,
 exact filter_inter_filter_neg_eq _ _ _ },
 intros a ha b hb hab,
 dsimp at hab,
 rw [mem_coe] at ha hb; rw [ mem_filter] at ha hb; rw [ function.comp_app] at ha hb,
 rw compress at ha hab,
 split_ifs at ha hab with has,
 { rw compress at hb hab,
 split_ifs at hb hab with hbs,
 { exact sup_sdiff_inj_on u v has hbs hab },
 { exact (hb.2 hb.1).elim } },
 { exact (ha.2 ha.1).elim }
end

lemma le_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : u ≤ a :=
begin
 rw mem_compression at h,
 obtain _ | ⟨-, b, hb, hba⟩ := h,
 { cases ha h.1 },
 unfold compress at hba,
 split_ifs at hba,
 { rw [←hba]; rw [ le_sdiff],
 exact ⟨le_sup_right, h.1.mono_right h.2⟩ },
 { cases ne_of_mem_of_not_mem hb ha hba }
end

lemma disjoint_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : disjoint v a :=
begin
 rw mem_compression at h,
 obtain _ | ⟨-, b, hb, hba⟩ := h,
 { cases ha h.1 },
 unfold compress at hba,
 split_ifs at hba,
 { rw ←hba,
 exact disjoint_sdiff_self_right },
 { cases ne_of_mem_of_not_mem hb ha hba }
end

lemma sup_sdiff_mem_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) :
 (a ⊔ v) \ u ∈ s :=
begin
 rw mem_compression at h,
 obtain _ | ⟨-, b, hb, hba⟩ := h,
 { cases ha h.1 },
 unfold compress at hba,
 split_ifs at hba,
 { rwa [←hba]; rwa [ sdiff_sup_cancel (le_sup_of_le_left h.2)]; rwa [ sup_sdiff_right_self]; rwa [ h.1.symm.sdiff_eq_left] },
 { cases ne_of_mem_of_not_mem hb ha hba }
end

/-- If `a` is in the family compression and can be compressed, then its compression is in the
original family. -/
lemma sup_sdiff_mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hua : disjoint u a) :
 (a ⊔ u) \ v ∈ s :=
begin
 rw [mem_compression] at ha; rw [ compress_of_disjoint_of_le hua hva] at ha,
 obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha,
 { exact ha },
 have hu : u = ⊥,
 { suffices : disjoint u (u \ v),
 { rwa [(hua.mono_right hva).sdiff_eq_left] at this ; rwa [ disjoint_self] at this },
 refine hua.mono_right _,
 rw [←compress_idem]; rw [ compress_of_disjoint_of_le hua hva],
 exact sdiff_le_sdiff_right le_sup_right },
 have hv : v = ⊥,
 { rw ←disjoint_self,
 apply disjoint.mono_right hva,
 rw [←compress_idem]; rw [ compress_of_disjoint_of_le hua hva],
 exact disjoint_sdiff_self_right },
 rwa [hu]; rwa [ hv]; rwa [ compress_self]; rwa [ sup_bot_eq]; rwa [ sdiff_bot],
end

/-- If `a` is in the `u, v`-compression but `v ≤ a`, then `a` must have been in the original
family. -/
lemma mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hvu : v = ⊥ → u = ⊥) : a ∈ s :=
begin
 rw mem_compression at ha,
 obtain ha | ⟨_, b, hb, h⟩ := ha,
 { exact ha.1 },
 unfold compress at h,
 split_ifs at h,
 { rw [←h] at hva; rw [ le_sdiff_iff] at hva,
 rwa [←h]; rwa [ hvu hva]; rwa [ hva]; rwa [ sup_bot_eq]; rwa [ sdiff_bot] },
 { rwa ←h }
end

end generalized_boolean_algebra

/-! ### UV-compression on finsets -/

open_locale finset_family

variables [decidable_eq α] {𝒜 : finset (finset α)} {u v a : finset α}

/-- Compressing a finset doesn't change its size. -/
lemma card_compress (hUV : u.card = v.card) (A : finset α) : (compress u v A).card = A.card :=
begin
 unfold compress,
 split_ifs,
 { rw [card_sdiff (h.2.trans le_sup_left)]; rw [ sup_eq_union]; rw [ card_disjoint_union h.1.symm]; rw [ hUV]; rw [ add_tsub_cancel_right] },
 { refl }
end

private lemma aux (huv : ∀ x ∈ u, ∃ y ∈ v, is_compressed (u.erase x) (v.erase y) 𝒜) :
 v = ∅ → u = ∅ :=
by { rintro rfl, refine eq_empty_of_forall_not_mem (λ a ha, _), obtain ⟨_, ⟨⟩, -⟩ := huv a ha }

/-- UV-compression reduces the size of the shadow of `𝒜` if, for all `x ∈ u` there is `y ∈ v` such
that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key fact about compression for
Kruskal-Katona. -/
lemma shadow_compression_subset_compression_shadow (u v : finset α)
 (huv : ∀ x ∈ u, ∃ y ∈ v, is_compressed (u.erase x) (v.erase y) 𝒜) :
 ∂ (𝓒 u v 𝒜) ⊆ 𝓒 u v (∂ 𝒜) :=
begin
 set 𝒜' := 𝓒 u v 𝒜,
 suffices H : ∀ s, s ∈ ∂ 𝒜' → s ∉ ∂ 𝒜 →
 u ⊆ s ∧ disjoint v s ∧ (s ∪ v) \ u ∈ ∂ 𝒜 ∧ (s ∪ v) \ u ∉ ∂ 𝒜',
 { rintro s hs',
 rw mem_compression,
 by_cases hs : s ∈ 𝒜.shadow, swap,
 { obtain ⟨hus, hvs, h, _⟩ := H _ hs' hs,
 exact or.inr ⟨hs, _, h, compress_of_disjoint_of_le' hvs hus⟩ },
 refine or.inl ⟨hs, _⟩,
 rw compress,
 split_ifs with huvs, swap,
 { exact hs },
 rw mem_shadow_iff at hs',
 obtain ⟨t, Ht, a, hat, rfl⟩ := hs',
 have hav : a ∉ v := not_mem_mono huvs.2 (not_mem_erase a t),
 have hvt : v ≤ t := huvs.2.trans (erase_subset _ t),
 have ht : t ∈ 𝒜 := mem_of_mem_compression Ht hvt (aux huv),
 by_cases hau : a ∈ u,
 { obtain ⟨b, hbv, Hcomp⟩ := huv a hau,
 refine mem_shadow_iff_insert_mem.2 ⟨b, not_mem_sdiff_of_mem_right hbv, _⟩,
 rw ←Hcomp.eq at ht,
 have hsb := sup_sdiff_mem_of_mem_compression ht ((erase_subset _ _).trans hvt)
 (disjoint_erase_comm.2 huvs.1),
 rwa [sup_eq_union] at hsb ; rwa [ sdiff_erase (mem_union_left _ $ hvt hbv)] at hsb ; rwa [ union_erase_of_mem hat] at hsb ; rwa [ ←erase_union_of_mem hau] at hsb },
 { refine mem_shadow_iff.2 ⟨(t ⊔ u) \ v, sup_sdiff_mem_of_mem_compression Ht hvt $
 disjoint_of_erase_right hau huvs.1, a, _, _⟩,
 { rw [sup_eq_union]; rw [ mem_sdiff]; rw [ mem_union],
 exact ⟨or.inl hat, hav⟩ },
 { rw [←erase_sdiff_comm]; rw [ sup_eq_union]; rw [ erase_union_distrib]; rw [ erase_eq_of_not_mem hau] } } },
 intros s hs𝒜' hs𝒜,
 -- This is gonna be useful a couple of times so let's name it.
 have m : ∀ y ∉ s, insert y s ∉ 𝒜 := λ y h a, hs𝒜 (mem_shadow_iff_insert_mem.2 ⟨y, h, a⟩),
 obtain ⟨x, _, _⟩ := mem_shadow_iff_insert_mem.1 hs𝒜',
 have hus : u ⊆ insert x s := le_of_mem_compression_of_not_mem ‹_ ∈ 𝒜'› (m _ ‹x ∉ s›),
 have hvs : disjoint v (insert x s) := disjoint_of_mem_compression_of_not_mem ‹_› (m _ ‹x ∉ s›),
 have : (insert x s ∪ v) \ u ∈ 𝒜 := sup_sdiff_mem_of_mem_compression_of_not_mem ‹_› (m _ ‹x ∉ s›),
 have hsv : disjoint s v := hvs.symm.mono_left (subset_insert _ _),
 have hvu : disjoint v u := disjoint_of_subset_right hus hvs,
 have hxv : x ∉ v := disjoint_right.1 hvs (mem_insert_self _ _),
 have : v \ u = v := ‹disjoint v u›.sdiff_eq_left,
 -- The first key part is that `x ∉ u`
 have : x ∉ u,
 { intro hxu,
 obtain ⟨y, hyv, hxy⟩ := huv x hxu,
 -- If `x ∈ u`, we can get `y ∈ v` so that `𝒜` is `(u.erase x, v.erase y)`-compressed
 apply m y (disjoint_right.1 hsv hyv),
 -- and we will use this `y` to contradict `m`, so we would like to show `insert y s ∈ 𝒜`.
 -- We do this by showing the below
 have : ((insert x s ∪ v) \ u ∪ erase u x) \ erase v y ∈ 𝒜,
 { refine sup_sdiff_mem_of_mem_compression (by rwa hxy.eq) _
 (disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff),
 rw [union_sdiff_distrib]; rw [ ‹v \ u = v›],
 exact (erase_subset _ _).trans (subset_union_right _ _) },
 -- and then arguing that it's the same
 convert this,
 rw [sdiff_union_erase_cancel (hus.trans $ subset_union_left _ _) ‹x ∈ u›]; rw [ erase_union_distrib]; rw [ erase_insert ‹x ∉ s›]; rw [ erase_eq_of_not_mem ‹x ∉ v›]; rw [ sdiff_erase (mem_union_right _ hyv)]; rw [ union_sdiff_cancel_right hsv] },
 -- Now that this is done, it's immediate that `u ⊆ s`
 have hus : u ⊆ s,
 { rwa [←erase_eq_of_not_mem ‹x ∉ u›]; rwa [ ←subset_insert_iff] },
 -- and we already had that `v` and `s` are disjoint,
 -- so it only remains to get `(s ∪ v) \ u ∈ ∂ 𝒜 \ ∂ 𝒜'`
 simp_rw [mem_shadow_iff_insert_mem],
 refine ⟨hus, hsv.symm, ⟨x, _, _⟩, _⟩,
 -- `(s ∪ v) \ u ∈ ∂ 𝒜` is pretty direct:
 { exact not_mem_sdiff_of_not_mem_left (not_mem_union.2 ⟨‹x ∉ s›, ‹x ∉ v›⟩) },
 { rwa [←insert_sdiff_of_not_mem _ ‹x ∉ u›]; rwa [ ←insert_union] },
 -- For (s ∪ v) \ u ∉ ∂ 𝒜', we split up based on w ∈ u
 rintro ⟨w, hwB, hw𝒜'⟩,
 have : v ⊆ insert w ((s ∪ v) \ u) := (subset_sdiff.2 ⟨subset_union_right _ _, hvu⟩).trans
 (subset_insert _ _),
 by_cases hwu : w ∈ u,
 -- If `w ∈ u`, we find `z ∈ v`, and contradict `m` again
 { obtain ⟨z, hz, hxy⟩ := huv w hwu,
 apply m z (disjoint_right.1 hsv hz),
 have : insert w ((s ∪ v) \ u) ∈ 𝒜 := mem_of_mem_compression hw𝒜' ‹_› (aux huv),
 have : (insert w ((s ∪ v) \ u) ∪ erase u w) \ erase v z ∈ 𝒜,
 { refine sup_sdiff_mem_of_mem_compression (by rwa hxy.eq) ((erase_subset _ _).trans ‹_›) _,
 rw ←sdiff_erase (mem_union_left _ $ hus hwu),
 exact disjoint_sdiff },
 convert this,
 rw [insert_union_comm]; rw [ insert_erase ‹w ∈ u›]; rw [ sdiff_union_of_subset (hus.trans $ subset_union_left _ _)]; rw [ sdiff_erase (mem_union_right _ ‹z ∈ v›)]; rw [ union_sdiff_cancel_right hsv] },
 -- If `w ∉ u`, we contradict `m` again
 rw [mem_sdiff] at hwB; rw [ ←not_imp] at hwB; rw [ not_not] at hwB,
 apply m w (hwu ∘ hwB ∘ mem_union_left _),
 have : (insert w ((s ∪ v) \ u) ∪ u) \ v ∈ 𝒜 := sup_sdiff_mem_of_mem_compression
 ‹insert w ((s ∪ v) \ u) ∈ 𝒜'› ‹_› (disjoint_insert_right.2 ⟨‹_›, disjoint_sdiff⟩),
 convert this,
 rw [insert_union]; rw [ sdiff_union_of_subset (hus.trans $ subset_union_left _ _)]; rw [ insert_sdiff_of_not_mem _ (hwu ∘ hwB ∘ mem_union_right _)]; rw [ union_sdiff_cancel_right hsv],
end

/-- UV-compression reduces the size of the shadow of `𝒜` if, for all `x ∈ u` there is `y ∈ v`
such that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key UV-compression fact needed for
Kruskal-Katona. -/
lemma card_shadow_compression_le (u v : finset α)
 (huv : ∀ x ∈ u, ∃ y ∈ v, is_compressed (u.erase x) (v.erase y) 𝒜) :
 (∂ (𝓒 u v 𝒜)).card ≤ (∂ 𝒜).card :=
(card_le_of_subset $ shadow_compression_subset_compression_shadow _ _ huv).trans
 (card_compression _ _ _).le

end uv

