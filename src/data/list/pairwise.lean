/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.count
import data.list.lex
import logic.pairwise
import logic.relation

/-!
# Pairwise relations on a list

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides basic results about `list.pairwise` and `list.pw_filter` (definitions are in
`data.list.defs`).
`pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`pairwise (≠) l` means that all elements of `l` are distinct, and `pairwise (<) l` means that `l`
is strictly increasing.
`pw_filter r l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`pairwise r l'`.

## Tags

sorted, nodup
-/

open nat function

namespace list
variables {α β : Type*} {R S T: α → α → Prop} {a : α} {l : list α}

mk_iff_of_inductive_prop list.pairwise list.pairwise_iff

/-! ### Pairwise -/

lemma rel_of_pairwise_cons (p : (a :: l).pairwise R) : ∀ {a'}, a' ∈ l → R a a' :=
(pairwise_cons.1 p).1

lemma pairwise.of_cons (p : (a :: l).pairwise R) : pairwise R l := (pairwise_cons.1 p).2

theorem pairwise.tail : ∀ {l : list α} (p : pairwise R l), pairwise R l.tail
| [] h := h
| (a :: l) h := h.of_cons

theorem pairwise.drop : ∀ {l : list α} {n : ℕ}, list.pairwise R l → list.pairwise R (l.drop n)
| _ 0 h := h
| [] (n + 1) h := list.pairwise.nil
| (a :: l) (n + 1) h := pairwise.drop (pairwise_cons.mp h).right

theorem pairwise.imp_of_mem {S : α → α → Prop} {l : list α}
 (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : pairwise R l) : pairwise S l :=
begin
 induction p with a l r p IH generalizing H; constructor,
 { exact ball.imp_right
 (λ x h, H (mem_cons_self _ _) (mem_cons_of_mem _ h)) r },
 { exact IH (λ a b m m', H
 (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')) }
end

lemma pairwise.imp (H : ∀ a b, R a b → S a b) : pairwise R l → pairwise S l :=
pairwise.imp_of_mem (λ a b _ _, H a b)

lemma pairwise_and_iff : l.pairwise (λ a b, R a b ∧ S a b) ↔ l.pairwise R ∧ l.pairwise S :=
⟨λ h, ⟨h.imp (λ a b h, h.1), h.imp (λ a b h, h.2)⟩,
 λ ⟨hR, hS⟩, begin
 clear_, induction hR with a l R1 R2 IH;
 simp only [pairwise.nil, pairwise_cons] at *,
 exact ⟨λ b bl, ⟨R1 b bl, hS.1 b bl⟩, IH hS.2⟩
 end⟩

lemma pairwise.and (hR : l.pairwise R) (hS : l.pairwise S) : l.pairwise (λ a b, R a b ∧ S a b) :=
pairwise_and_iff.2 ⟨hR, hS⟩

lemma pairwise.imp₂ (H : ∀ a b, R a b → S a b → T a b) (hR : l.pairwise R) (hS : l.pairwise S) :
 l.pairwise T :=
(hR.and hS).imp $ λ a b, and.rec (H a b)

theorem pairwise.iff_of_mem {S : α → α → Prop} {l : list α}
 (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : pairwise R l ↔ pairwise S l :=
⟨pairwise.imp_of_mem (λ a b m m', (H m m').1),
 pairwise.imp_of_mem (λ a b m m', (H m m').2)⟩

theorem pairwise.iff {S : α → α → Prop}
 (H : ∀ a b, R a b ↔ S a b) {l : list α} : pairwise R l ↔ pairwise S l :=
pairwise.iff_of_mem (λ a b _ _, H a b)

theorem pairwise_of_forall {l : list α} (H : ∀ x y, R x y) : pairwise R l :=
by induction l; [exact pairwise.nil,
simp only [*, pairwise_cons, forall_2_true_iff, and_true]]

theorem pairwise.and_mem {l : list α} :
 pairwise R l ↔ pairwise (λ x y, x ∈ l ∧ y ∈ l ∧ R x y) l :=
pairwise.iff_of_mem (by simp only [true_and, iff_self, forall_2_true_iff] {contextual := tt})

theorem pairwise.imp_mem {l : list α} :
 pairwise R l ↔ pairwise (λ x y, x ∈ l → y ∈ l → R x y) l :=
pairwise.iff_of_mem
 (by simp only [forall_prop_of_true, iff_self, forall_2_true_iff] {contextual := tt})

protected lemma pairwise.sublist : Π {l₁ l₂ : list α}, l₁ <+ l₂ → pairwise R l₂ → pairwise R l₁
| ._ ._ sublist.slnil h := h
| ._ ._ (sublist.cons l₁ l₂ a s) (pairwise.cons i h) := h.sublist s
| ._ ._ (sublist.cons2 l₁ l₂ a s) (pairwise.cons i h) :=
 (h.sublist s).cons (ball.imp_left s.subset i)

lemma pairwise.forall_of_forall_of_flip (h₁ : ∀ x ∈ l, R x x) (h₂ : l.pairwise R)
 (h₃ : l.pairwise (flip R)) :
 ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
begin
 induction l with a l ih,
 { exact forall_mem_nil _ },
 rw pairwise_cons at h₂ h₃,
 rintro x (rfl | hx) y (rfl | hy),
 { exact h₁ _ (l.mem_cons_self _) },
 { exact h₂.1 _ hy },
 { exact h₃.1 _ hx },
 { exact ih (λ x hx, h₁ _ $ mem_cons_of_mem _ hx) h₂.2 h₃.2 hx hy }
end

lemma pairwise.forall_of_forall (H : symmetric R) (H₁ : ∀ x ∈ l, R x x) (H₂ : l.pairwise R) :
 ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
H₂.forall_of_forall_of_flip H₁ $ by rwa H.flip_eq

lemma pairwise.forall (hR : symmetric R) (hl : l.pairwise R) :
 ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b :=
pairwise.forall_of_forall
 (λ a b h hne, hR (h hne.symm))
 (λ _ _ h, (h rfl).elim)
 (hl.imp $ λ _ _ h _, h)

lemma pairwise.set_pairwise (hl : pairwise R l) (hr : symmetric R) : {x | x ∈ l}.pairwise R :=
hl.forall hr

theorem pairwise_singleton (R) (a : α) : pairwise R [a] :=
by simp only [pairwise_cons, mem_singleton, forall_prop_of_false (not_mem_nil _), forall_true_iff,
 pairwise.nil, and_true]

theorem pairwise_pair {a b : α} : pairwise R [a, b] ↔ R a b :=
by simp only [pairwise_cons, mem_singleton, forall_eq, forall_prop_of_false (not_mem_nil _),
 forall_true_iff, pairwise.nil, and_true]

theorem pairwise_append {l₁ l₂ : list α} : pairwise R (l₁++l₂) ↔
 pairwise R l₁ ∧ pairwise R l₂ ∧ ∀ x ∈ l₁, ∀ y ∈ l₂, R x y :=
by induction l₁ with x l₁ IH; [simp only [list.pairwise.nil, forall_prop_of_false (not_mem_nil _),
 forall_true_iff, and_true, true_and, nil_append],
simp only [cons_append, pairwise_cons, forall_mem_append, IH, forall_mem_cons, forall_and_distrib,
 and_assoc, and.left_comm]]

theorem pairwise_append_comm (s : symmetric R) {l₁ l₂ : list α} :
 pairwise R (l₁++l₂) ↔ pairwise R (l₂++l₁) :=
have ∀ l₁ l₂ : list α,
 (∀ (x : α), x ∈ l₁ → ∀ (y : α), y ∈ l₂ → R x y) →
 (∀ (x : α), x ∈ l₂ → ∀ (y : α), y ∈ l₁ → R x y),
from λ l₁ l₂ a x xm y ym, s (a y ym x xm),
by simp only [pairwise_append, and.left_comm]; rw iff.intro (this l₁ l₂) (this l₂ l₁)

theorem pairwise_middle (s : symmetric R) {a : α} {l₁ l₂ : list α} :
 pairwise R (l₁ ++ a :: l₂) ↔ pairwise R (a :: (l₁++l₂)) :=
show pairwise R (l₁ ++ ([a] ++ l₂)) ↔ pairwise R ([a] ++ l₁ ++ l₂),
by rw [← append_assoc]; rw [ pairwise_append]; rw [ @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s];
 simp only [mem_append, or_comm]

theorem pairwise_map (f : β → α) :
 ∀ {l : list β}, pairwise R (map f l) ↔ pairwise (λ a b : β, R (f a) (f b)) l
| [] := by simp only [map, pairwise.nil]
| (b :: l) :=
 have (∀ a b', b' ∈ l → f b' = a → R (f b) a) ↔ ∀ (b' : β), b' ∈ l → R (f b) (f b'), from
 forall_swap.trans $ forall_congr $ λ a, forall_swap.trans $ by simp only [forall_eq'],
 by simp only [map, pairwise_cons, mem_map, exists_imp_distrib, and_imp, this, pairwise_map]

lemma pairwise.of_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
 (p : pairwise S (map f l)) : pairwise R l :=
((pairwise_map f).1 p).imp H

lemma pairwise.map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
 (p : pairwise R l) : pairwise S (map f l) :=
(pairwise_map f).2 $ p.imp H

theorem pairwise_filter_map (f : β → option α) {l : list β} :
 pairwise R (filter_map f l) ↔ pairwise (λ a a' : β, ∀ (b ∈ f a) (b' ∈ f a'), R b b') l :=
let S (a a' : β) := ∀ (b ∈ f a) (b' ∈ f a'), R b b' in
begin
 simp only [option.mem_def], induction l with a l IH,
 { simp only [filter_map, pairwise.nil] },
 cases e : f a with b,
 { rw [filter_map_cons_none _ _ e]; rw [ IH]; rw [ pairwise_cons],
 simp only [e, forall_prop_of_false not_false, forall_3_true_iff, true_and] },
 rw [filter_map_cons_some _ _ _ e],
 simp only [pairwise_cons, mem_filter_map, exists_imp_distrib, and_imp, IH, e, forall_eq'],
 show (∀ (a' : α) (x : β), x ∈ l → f x = some a' → R b a') ∧ pairwise S l ↔
 (∀ (a' : β), a' ∈ l → ∀ (b' : α), f a' = some b' → R b b') ∧ pairwise S l,
 from and_congr ⟨λ h b mb a ma, h a b mb ma, λ h a b mb ma, h b mb a ma⟩ iff.rfl
end

theorem pairwise.filter_map {S : β → β → Prop} (f : α → option β)
 (H : ∀ (a a' : α), R a a' → ∀ (b ∈ f a) (b' ∈ f a'), S b b') {l : list α}
 (p : pairwise R l) : pairwise S (filter_map f l) :=
(pairwise_filter_map _).2 $ p.imp H

theorem pairwise_filter (p : α → Prop) [decidable_pred p] {l : list α} :
 pairwise R (filter p l) ↔ pairwise (λ x y, p x → p y → R x y) l :=
begin
 rw [← filter_map_eq_filter]; rw [ pairwise_filter_map],
 apply pairwise.iff, intros, simp only [option.mem_def, option.guard_eq_some, and_imp, forall_eq'],
end

lemma pairwise.filter (p : α → Prop) [decidable_pred p] : pairwise R l → pairwise R (filter p l) :=
pairwise.sublist (filter_sublist _)

theorem pairwise_pmap {p : β → Prop} {f : Π b, p b → α} {l : list β} (h : ∀ x ∈ l, p x) :
 pairwise R (l.pmap f h) ↔
 pairwise (λ b₁ b₂, ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l :=
begin
 induction l with a l ihl, { simp },
 obtain ⟨ha, hl⟩ : p a ∧ ∀ b, b ∈ l → p b, by simpa using h,
 simp only [ihl hl, pairwise_cons, bex_imp_distrib, pmap, and.congr_left_iff, mem_pmap],
 refine λ _, ⟨λ H b hb hpa hpb, H _ _ hb rfl, _⟩,
 rintro H _ b hb rfl,
 exact H b hb _ _
end

theorem pairwise.pmap {l : list α} (hl : pairwise R l)
 {p : α → Prop} {f : Π a, p a → β} (h : ∀ x ∈ l, p x) {S : β → β → Prop}
 (hS : ∀ ⦃x⦄ (hx : p x) ⦃y⦄ (hy : p y), R x y → S (f x hx) (f y hy)) :
 pairwise S (l.pmap f h) :=
begin
 refine (pairwise_pmap h).2 (pairwise.imp_of_mem _ hl),
 intros, apply hS, assumption
end

theorem pairwise_join {L : list (list α)} : pairwise R (join L) ↔
 (∀ l ∈ L, pairwise R l) ∧ pairwise (λ l₁ l₂, ∀ (x ∈ l₁) (y ∈ l₂), R x y) L :=
begin
 induction L with l L IH,
 {simp only [join, pairwise.nil, forall_prop_of_false (not_mem_nil _), forall_const, and_self]},
 have : (∀ (x : α), x ∈ l → ∀ (y : α) (x_1 : list α), x_1 ∈ L → y ∈ x_1 → R x y) ↔
 ∀ (a' : list α), a' ∈ L → ∀ (x : α), x ∈ l → ∀ (y : α), y ∈ a' → R x y :=
 ⟨λ h a b c d e, h c d e a b, λ h c d e a b, h a b c d e⟩,
 simp only [join, pairwise_append, IH, mem_join, exists_imp_distrib, and_imp, this,
 forall_mem_cons, pairwise_cons],
 simp only [and_assoc, and_comm, and.left_comm],
end

lemma pairwise_bind {R : β → β → Prop} {l : list α} {f : α → list β} :
 list.pairwise R (l.bind f) ↔
 (∀ a ∈ l, pairwise R (f a)) ∧ pairwise (λ a₁ a₂, ∀ (x ∈ f a₁) (y ∈ f a₂), R x y) l :=
by simp [list.bind, list.pairwise_join, list.mem_map, list.pairwise_map]

@[simp] theorem pairwise_reverse : ∀ {R} {l : list α},
 pairwise R (reverse l) ↔ pairwise (λ x y, R y x) l :=
suffices ∀ {R l}, @pairwise α R l → pairwise (λ x y, R y x) (reverse l),
from λ R l, ⟨λ p, reverse_reverse l ▸ this p, this⟩,
λ R l p, by induction p with a l h p IH;
 [apply pairwise.nil, simpa only [reverse_cons, pairwise_append, IH,
 pairwise_cons, forall_prop_of_false (not_mem_nil _), forall_true_iff,
 pairwise.nil, mem_reverse, mem_singleton, forall_eq, true_and] using h]

lemma pairwise_of_reflexive_on_dupl_of_forall_ne [decidable_eq α] {l : list α} {r : α → α → Prop}
 (hr : ∀ a, 1 < count a l → r a a)
 (h : ∀ (a ∈ l) (b ∈ l), a ≠ b → r a b) : l.pairwise r :=
begin
 induction l with hd tl IH,
 { simp },
 { rw list.pairwise_cons,
 split,
 { intros x hx,
 by_cases H : hd = x,
 { rw H,
 refine hr _ _,
 simpa [count_cons, H, nat.succ_lt_succ_iff, count_pos] using hx },
 { exact h hd (mem_cons_self _ _) x (mem_cons_of_mem _ hx) H } },
 { refine IH _ _,
 { intros x hx,
 refine hr _ _,
 rw count_cons,
 split_ifs,
 { exact hx.trans (nat.lt_succ_self _) },
 { exact hx } },
 { intros x hx y hy,
 exact h x (mem_cons_of_mem _ hx) y (mem_cons_of_mem _ hy) } } }
end

lemma pairwise_of_forall_mem_list {l : list α} {r : α → α → Prop} (h : ∀ (a ∈ l) (b ∈ l), r a b) :
 l.pairwise r :=
begin
 classical,
 refine pairwise_of_reflexive_on_dupl_of_forall_ne (λ a ha', _) (λ a ha b hb _, h a ha b hb),
 have ha := list.one_le_count_iff_mem.1 ha'.le,
 exact h a ha a ha
end

lemma pairwise_of_reflexive_of_forall_ne {l : list α} {r : α → α → Prop}
 (hr : reflexive r) (h : ∀ (a ∈ l) (b ∈ l), a ≠ b → r a b) : l.pairwise r :=
by { classical, exact pairwise_of_reflexive_on_dupl_of_forall_ne (λ _ _, hr _) h }

theorem pairwise_iff_nth_le {R} : ∀ {l : list α},
 pairwise R l ↔ ∀ i j (h₁ : j < length l) (h₂ : i < j),
 R (nth_le l i (lt_trans h₂ h₁)) (nth_le l j h₁)
| [] := by simp only [pairwise.nil, true_iff]; exact λ i j h, (nat.not_lt_zero j).elim h
| (a :: l) := begin
 rw [pairwise_cons]; rw [ pairwise_iff_nth_le],
 refine ⟨λ H i j h₁ h₂, _, λ H, ⟨λ a' m, _,
 λ i j h₁ h₂, H _ _ (succ_lt_succ h₁) (succ_lt_succ h₂)⟩⟩,
 { cases j with j, {exact (nat.not_lt_zero _).elim h₂},
 cases i with i,
 { exact H.1 _ (nth_le_mem l _ _) },
 { exact H.2 _ _ (lt_of_succ_lt_succ h₁) (lt_of_succ_lt_succ h₂) } },
 { rcases nth_le_of_mem m with ⟨n, h, rfl⟩,
 exact H _ _ (succ_lt_succ h) (succ_pos _) }
end

lemma pairwise_replicate {α : Type*} {r : α → α → Prop} {x : α} (hx : r x x) :
 ∀ (n : ℕ), pairwise r (replicate n x)
| 0 := by simp
| (n+1) := by simp [hx, mem_replicate, pairwise_replicate n]

/-! ### Pairwise filtering -/

variable [decidable_rel R]

@[simp] theorem pw_filter_nil : pw_filter R [] = [] := rfl

@[simp] theorem pw_filter_cons_of_pos {a : α} {l : list α} (h : ∀ b ∈ pw_filter R l, R a b) :
 pw_filter R (a :: l) = a :: pw_filter R l := if_pos h

@[simp] theorem pw_filter_cons_of_neg {a : α} {l : list α} (h : ¬ ∀ b ∈ pw_filter R l, R a b) :
 pw_filter R (a :: l) = pw_filter R l := if_neg h

theorem pw_filter_map (f : β → α) :
 Π (l : list β), pw_filter R (map f l) = map f (pw_filter (λ x y, R (f x) (f y)) l)
| [] := rfl
| (x :: xs) :=
 if h : ∀ b ∈ pw_filter R (map f xs), R (f x) b
 then have h' : ∀ (b : β), b ∈ pw_filter (λ (x y : β), R (f x) (f y)) xs → R (f x) (f b),
 from λ b hb, h _ (by rw [pw_filter_map]; apply mem_map_of_mem _ hb),
 by rw [map]; rw [pw_filter_cons_of_pos h]; rw [pw_filter_cons_of_pos h']; rw [pw_filter_map]; rw [map]
 else have h' : ¬∀ (b : β), b ∈ pw_filter (λ (x y : β), R (f x) (f y)) xs → R (f x) (f b),
 from λ hh, h $ λ a ha,
 by { rw [pw_filter_map] at ha; rw [mem_map] at ha, rcases ha with ⟨b,hb₀,hb₁⟩,
 subst a, exact hh _ hb₀, },
 by rw [map]; rw [pw_filter_cons_of_neg h]; rw [pw_filter_cons_of_neg h']; rw [pw_filter_map]

theorem pw_filter_sublist : ∀ (l : list α), pw_filter R l <+ l
| [] := nil_sublist _
| (x :: l) := begin
 by_cases (∀ y ∈ pw_filter R l, R x y),
 { rw [pw_filter_cons_of_pos h],
 exact (pw_filter_sublist l).cons_cons _ },
 { rw [pw_filter_cons_of_neg h],
 exact sublist_cons_of_sublist _ (pw_filter_sublist l) },
end

theorem pw_filter_subset (l : list α) : pw_filter R l ⊆ l :=
(pw_filter_sublist _).subset

theorem pairwise_pw_filter : ∀ (l : list α), pairwise R (pw_filter R l)
| [] := pairwise.nil
| (x :: l) := begin
 by_cases (∀ y ∈ pw_filter R l, R x y),
 { rw [pw_filter_cons_of_pos h],
 exact pairwise_cons.2 ⟨h, pairwise_pw_filter l⟩ },
 { rw [pw_filter_cons_of_neg h],
 exact pairwise_pw_filter l },
end

theorem pw_filter_eq_self {l : list α} : pw_filter R l = l ↔ pairwise R l :=
⟨λ e, e ▸ pairwise_pw_filter l, λ p, begin
 induction l with x l IH, {refl},
 cases pairwise_cons.1 p with al p,
 rw [pw_filter_cons_of_pos (ball.imp_left (pw_filter_subset l) al)]; rw [ IH p],
end⟩

alias pw_filter_eq_self ↔ _ pairwise.pw_filter

attribute [protected] pairwise.pw_filter

@[simp] lemma pw_filter_idempotent : pw_filter R (pw_filter R l) = pw_filter R l :=
(pairwise_pw_filter l).pw_filter

theorem forall_mem_pw_filter (neg_trans : ∀ {x y z}, R x z → R x y ∨ R y z)
 (a : α) (l : list α) : (∀ b ∈ pw_filter R l, R a b) ↔ (∀ b ∈ l, R a b) :=
⟨begin
 induction l with x l IH, { exact λ _ _, false.elim },
 simp only [forall_mem_cons],
 by_cases (∀ y ∈ pw_filter R l, R x y); dsimp at h,
 { simp only [pw_filter_cons_of_pos h, forall_mem_cons, and_imp],
 exact λ r H, ⟨r, IH H⟩ },
 { rw [pw_filter_cons_of_neg h],
 refine λ H, ⟨_, IH H⟩,
 cases e : find (λ y, ¬ R x y) (pw_filter R l) with k,
 { refine h.elim (ball.imp_right _ (find_eq_none.1 e)),
 exact λ y _, not_not.1 },
 { have := find_some e,
 exact (neg_trans (H k (find_mem e))).resolve_right this } }
end, ball.imp_left (pw_filter_subset l)⟩

end list

