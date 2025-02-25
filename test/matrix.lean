import data.matrix.notation
import linear_algebra.matrix.determinant
import group_theory.perm.fin
import tactic.norm_swap

variables {α β : Type} [semiring α] [ring β]

namespace matrix

open_locale matrix

/-! Test that the dimensions are inferred correctly, even for empty matrices -/
section dimensions

set_option pp.universes true
set_option pp.all true

meta def get_dims (e : pexpr) : tactic (expr × expr) :=
do
 elem_t ← tactic.mk_meta_var (expr.sort level.zero.succ),
 e ← tactic.to_expr ``(%%e : matrix _ _ %%elem_t) tt ff,
 t ← tactic.infer_type e,
 `(matrix.{0 0 0} (fin %%m) (fin %%n) %%elem_t) ← tactic.infer_type e,
 return (m, n)

-- we test equality of expressions here to ensure that we have `2` and not `1.succ` in the type
run_cmd do d ← get_dims ``(!![]), guard $ d = (`(0), `(0))
run_cmd do d ← get_dims ``(!![;]), guard $ d = (`(1), `(0))
run_cmd do d ← get_dims ``(!![;;]), guard $ d = (`(2), `(0))
run_cmd do d ← get_dims ``(!![,]), guard $ d = (`(0), `(1))
run_cmd do d ← get_dims ``(!![,,]), guard $ d = (`(0), `(2))
run_cmd do d ← get_dims ``(!![1]), guard $ d = (`(1), `(1))
run_cmd do d ← get_dims ``(!![1,]), guard $ d = (`(1), `(1))
run_cmd do d ← get_dims ``(!![1;]), guard $ d = (`(1), `(1))
run_cmd do d ← get_dims ``(!![1,2;3,4]), guard $ d = (`(2), `(2))

end dimensions

run_cmd guard $ (!![1;2]) = of ![![1], ![2]]
run_cmd guard $ (!![1,3]) = of ![![1,3]]
run_cmd guard $ (!![1,2;3,4]) = of ![![1,2], ![3,4]]
run_cmd guard $ (!![1,2;3,4;]) = of ![![1,2], ![3,4]]
run_cmd guard $ (!![1,2,;3,4,]) = of ![![1,2], ![3,4]]

example {a a' b b' c c' d d' : α} :
 !![a, b; c, d] + !![a', b'; c', d'] = !![a + a', b + b'; c + c', d + d'] :=
by simp

example {a a' b b' c c' d d' : β} :
 !![a, b; c, d] - !![a', b'; c', d'] = !![a - a', b - b'; c - c', d - d'] :=
by simp

example {a a' b b' c c' d d' : α} :
 !![a, b; c, d] ⬝ !![a', b'; c', d'] =
 !![a * a' + b * c', a * b' + b * d'; c * a' + d * c', c * b' + d * d'] :=
by simp [-equiv.perm.coe_subsingleton]

example {a b c d x y : α} :
 mul_vec !![a, b; c, d] ![x, y] = ![a * x + b * y, c * x + d * y] :=
by simp

example {a b c d : α} : submatrix !![a, b; c, d] ![1, 0] ![0] = !![c; a] :=
by { ext, simp }

example {a b c : α} : ![a, b, c] 0 = a := by simp
example {a b c : α} : ![a, b, c] 1 = b := by simp
example {a b c : α} : ![a, b, c] 2 = c := by simp

example {a b c d : α} : ![a, b, c, d] 0 = a := by simp
example {a b c d : α} : ![a, b, c, d] 1 = b := by simp
example {a b c d : α} : ![a, b, c, d] 2 = c := by simp
example {a b c d : α} : ![a, b, c, d] 3 = d := by simp
example {a b c d : α} : ![a, b, c, d] 42 = c := by simp

example {a b c d e : α} : ![a, b, c, d, e] 0 = a := by simp
example {a b c d e : α} : ![a, b, c, d, e] 1 = b := by simp
example {a b c d e : α} : ![a, b, c, d, e] 2 = c := by simp
example {a b c d e : α} : ![a, b, c, d, e] 3 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 4 = e := by simp
example {a b c d e : α} : ![a, b, c, d, e] 5 = a := by simp
example {a b c d e : α} : ![a, b, c, d, e] 6 = b := by simp
example {a b c d e : α} : ![a, b, c, d, e] 7 = c := by simp
example {a b c d e : α} : ![a, b, c, d, e] 8 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 9 = e := by simp
example {a b c d e : α} : ![a, b, c, d, e] 123 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 123456789 = e := by simp

example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 5 = f := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 7 = h := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 37 = f := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 99 = d := by simp

example {α : Type*} [comm_ring α] {a b c d : α} :
 matrix.det !![a, b; c, d] = a * d - b * c :=
begin
 simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
 /-
 Try this: simp only [det_succ_row_zero, fin.sum_univ_succ, neg_mul, mul_one,
 fin.default_eq_zero, fin.coe_zero, one_mul, cons_val_one, fin.coe_succ, univ_unique,
 submatrix_apply, pow_one, fin.zero_succ_above, fin.succ_succ_above_zero, finset.sum_singleton,
 cons_val_zero, cons_val_succ, det_fin_zero, pow_zero]
 -/
 ring
end

example {α : Type*} [comm_ring α] {a b c d e f g h i : α} :
 matrix.det !![a, b, c; d, e, f; g, h, i] =
 a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
begin
 simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
 /-
 Try this: simp only [det_succ_row_zero, fin.sum_univ_succ, neg_mul, cons_append,
 mul_one, fin.default_eq_zero, fin.coe_zero, cons_vec_bit0_eq_alt0, one_mul, cons_val_one,
 cons_vec_alt0, fin.succ_succ_above_one, fin.coe_succ, univ_unique, submatrix_apply, pow_one,
 fin.zero_succ_above, fin.succ_zero_eq_one, fin.succ_succ_above_zero, nat.neg_one_sq,
 finset.sum_singleton, cons_val_zero, cons_val_succ, det_fin_zero, head_cons, pow_zero]
 -/
 ring
end

end matrix

