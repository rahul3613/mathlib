/-
Copyright (c) 2021 Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lutz, Oliver Nash
-/

/-!
# Bracket Notation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides notation which can be used for the Lie bracket, for the commutator of two
subgroups, and for other similar operations.

## Main Definitions

* `has_bracket L M` for a binary operation that takes something in `L` and something in `M` and
produces something in `M`. Defining an instance of this structure gives access to the notation `⁅ ⁆`

## Notation

We introduce the notation `⁅x, y⁆` for the `bracket` of any `has_bracket` structure. Note that
these are the Unicode "square with quill" brackets rather than the usual square brackets.
-/

/-- The has_bracket class has three intended uses:

 1. for certain binary operations on structures, like the product `⁅x, y⁆` of two elements
 `x`, `y` in a Lie algebra or the commutator of two elements `x` and `y` in a group.

 2. for certain actions of one structure on another, like the action `⁅x, m⁆` of an element `x`
 of a Lie algebra on an element `m` in one of its modules (analogous to `has_smul` in the
 associative setting).

 3. for binary operations on substructures, like the commutator `⁅H, K⁆` of two subgroups `H` and
 `K` of a group. -/
class has_bracket (L M : Type*) := (bracket : L → M → M)

notation `⁅`x`, `y`⁆` := has_bracket.bracket x y

