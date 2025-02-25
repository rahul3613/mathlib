/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import algebra.big_operators.basic
import data.finset.option

/-!
# Lemmas about products and sums over finite sets in `option α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove formulas for products and sums over `finset.insert_none s` and
`finset.erase_none s`.
-/

open_locale big_operators
open function

namespace finset

variables {α M : Type*} [comm_monoid M]

@[simp, to_additive] lemma prod_insert_none (f : option α → M) (s : finset α) :
 ∏ x in s.insert_none, f x = f none * ∏ x in s, f (some x) :=
by simp [insert_none]

@[to_additive] lemma prod_erase_none (f : α → M) (s : finset (option α)) :
 ∏ x in s.erase_none, f x = ∏ x in s, option.elim 1 f x :=
by classical;
calc ∏ x in s.erase_none, f x = ∏ x in s.erase_none.map embedding.some, option.elim 1 f x :
 (prod_map s.erase_none embedding.some $ option.elim 1 f).symm
... = ∏ x in s.erase none, option.elim 1 f x : by rw map_some_erase_none
... = ∏ x in s, option.elim 1 f x : prod_erase _ rfl

end finset

