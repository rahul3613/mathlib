/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Johan Commelin
-/
import tactic.wlog

section wlog

example {x y : ℕ} : true :=
begin
 wlog h : x ≤ y,
 { guard_hyp h : ¬x ≤ y,
 guard_hyp this : ∀ {x y : ℕ}, x ≤ y → true, -- `wlog` generalizes by default
 guard_target true,
 trivial },
 { guard_hyp h : x ≤ y,
 guard_target true,
 trivial },
end

example {x y : ℕ} : true :=
begin
 wlog h : x ≤ y generalizing x,
 { guard_hyp h : ¬x ≤ y,
 guard_hyp this : ∀ {x : ℕ}, x ≤ y → true, -- only `x` was generalized
 guard_target true,
 trivial },
 { guard_hyp h : x ≤ y,
 guard_target true,
 trivial },
end

example {x y z : ℕ} : true :=
begin
 wlog h : x ≤ y + z with H,
 { guard_hyp h : ¬ x ≤ y + z,
 guard_hyp H : ∀ {x y z : ℕ}, x ≤ y + z → true, -- wlog-claim is named `H` instead of `this`
 guard_target true,
 trivial },
 { guard_hyp h : x ≤ y + z,
 guard_target true,
 trivial },
end

end wlog

