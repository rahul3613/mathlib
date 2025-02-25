import tactic.linarith

example : ∀ (y : ℕ), y ≤ 37 → y < 40 :=
begin
 refine λ y hy, _,
 -- The type of `hy` is a (solved but not instantiated) metavariable
 do { tactic.get_local `hy >>= tactic.infer_type >>= guardb ∘ expr.is_mvar },
 -- But linarith should still work
 linarith
end

example {α : Type} (_inst : Π (a : Prop), decidable a)
 [linear_ordered_field α]
 {a b c : α}
 (ha : a < 0)
 (hb : ¬b = 0)
 (hc' : c = 0)
 (h : (1 - a) * (b * b) ≤ 0)
 (hc : 0 ≤ 0)
 (this : -(a * -b * -b + b * -b + 0) = (1 - a) * (b * b))
 (h : (1 - a) * (b * b) ≤ 0) :
 0 < 1 - a :=
begin
 linarith
end

example (e b c a v0 v1 : ℚ) (h1 : v0 = 5*a) (h2 : v1 = 3*b) (h3 : v0 + v1 + c = 10) :
 v0 + 5 + (v1 - 3) + (c - 2) = 10 :=
by linarith

example (u v r s t : ℚ) (h : 0 < u*(t*v + t*r + s)) : 0 < (t*(r + v) + s)*3*u :=
by linarith

example (A B : ℚ) (h : 0 < A * B) : 0 < 8*A*B :=
begin
 linarith
end

example (A B : ℚ) (h : 0 < A * B) : 0 < A*8*B :=
begin
 linarith
end

example (A B : ℚ) (h : 0 < A * B) : 0 < A*B/8 :=
begin
 linarith
end

example (A B : ℚ) (h : 0 < A * B) : 0 < A/8*B :=
begin
 linarith
end

example (ε : ℚ) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε :=
 by linarith

example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + z/2 < 0)
 (h3 : 12*y - z < 0) : false :=
by linarith

example (ε : ℚ) (h1 : ε > 0) : ε / 2 < ε :=
by linarith

example (ε : ℚ) (h1 : ε > 0) : ε / 3 + ε / 3 + ε / 3 = ε :=
by linarith

example (a b c : ℚ) (h2 : b + 2 > 3 + b) : false :=
by linarith {discharger := `[ring]}

example (a b c : ℚ) (h2 : b + 2 > 3 + b) : false :=
by linarith

example (a b c : ℚ) (x y : ℤ) (h1 : x ≤ 3*y) (h2 : b + 2 > 3 + b) : false :=
by linarith {restrict_type := ℚ}

example (g v V c h : ℚ) (h1 : h = 0) (h2 : v = V) (h3 : V > 0) (h4 : g > 0)
 (h5 : 0 ≤ c) (h6 : c < 1) :
 v ≤ V :=
by linarith

constant nat.prime : ℕ → Prop

example (x y z : ℚ) (h1 : 2*x + ((-3)*y) < 0) (h2 : (-4)*x + 2*z < 0)
 (h3 : 12*y + (-4)* z < 0) (h4 : nat.prime 7) : false :=
by linarith

example (x y z : ℚ) (h1 : 2*1*x + (3)*(y*(-1)) < 0) (h2 : (-2)*x*2 < -(z + z))
 (h3 : 12*y + (-4)* z < 0) (h4 : nat.prime 7) : false :=
by linarith

example (x y z : ℤ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
 (h3 : 12*y - 4* z < 0) : false :=
by linarith

example (x y z : ℤ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : x*y < 5)
 (h3 : 12*y - 4* z < 0) : false :=
by linarith

example (x y z : ℤ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : x*y < 5) :
 ¬ 12*y - 4* z < 0 :=
by linarith

example (w x y z : ℤ) (h1 : 4*x + (-3)*y + 6*w ≤ 0) (h2 : (-1)*x < 0)
 (h3 : y < 0) (h4 : w ≥ 0) (h5 : nat.prime x.nat_abs) : false :=
by linarith

example (a b c : ℚ) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10)
 (h4 : a + b - c < 3) : false :=
by linarith

example (a b c : ℚ) (h2 : b > 0) (h3 : ¬ b ≥ 0) : false :=
by linarith

example (a b c : ℚ) (h2 : (2 : ℚ) > 3) : a + b - c ≥ 3 :=
by linarith {exfalso := ff}

example (x : ℚ) (hx : x > 0) (h : x.num < 0) : false :=
by linarith [rat.num_pos_iff_pos.mpr hx, h]

example (x : ℚ) (hx : x > 0) (h : x.num < 0) : false :=
by linarith only [rat.num_pos_iff_pos.mpr hx, h]

example (x y z : ℚ) (hx : x ≤ 3*y) (h2 : y ≤ 2*z) (h3 : x ≥ 6*z) : x = 3*y :=
by linarith

example (x y z : ℕ) (hx : x ≤ 3*y) (h2 : y ≤ 2*z) (h3 : x ≥ 6*z) : x = 3*y :=
by linarith

example (x y z : ℚ) (hx : ¬ x > 3*y) (h2 : ¬ y > 2*z) (h3 : x ≥ 6*z) : x = 3*y :=
by linarith

example (h1 : (1 : ℕ) < 1) : false :=
by linarith

example (a b c : ℚ) (h2 : b > 0) (h3 : b < 0) : nat.prime 10 :=
by linarith

example (a b c : ℕ) : a + b ≥ a :=
by linarith

example (a b c : ℕ) : ¬ a + b < a :=
by linarith

example (x y : ℚ) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) (h' : (x + 4) * x ≥ 0)
 (h'' : (6 + 3 * y) * y ≥ 0) : false :=
by linarith

example (x y : ℚ)
 (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3 ∧ (x + 4) * x ≥ 0 ∧ (6 + 3 * y) * y ≥ 0) : false :=
by linarith

example (a b i : ℕ) (h1 : ¬ a < i) (h2 : b < i) (h3 : a ≤ b) : false :=
by linarith

example (n : ℕ) (h1 : n ≤ 3) (h2 : n > 2) : n = 3 := by linarith

example (z : ℕ) (hz : ¬ z ≥ 2) (h2 : ¬ z + 1 ≤ 2) : false :=
by linarith

example (z : ℕ) (hz : ¬ z ≥ 2) : z + 1 ≤ 2 :=
by linarith

example (a b c : ℚ) (h1 : 1 / a < b) (h2 : b < c) : 1 / a < c :=
by linarith

example
(N : ℕ) (n : ℕ) (Hirrelevant : n > N)
(A : ℚ) (l : ℚ) (h : A - l ≤ -(A - l)) (h_1 : ¬A ≤ -A) (h_2 : ¬l ≤ -l)
(h_3 : -(A - l) < 1) : A < l + 1 := by linarith

example (d : ℚ) (q n : ℕ) (h1 : ((q : ℚ) - 1)*n ≥ 0) (h2 : d = 2/3*(((q : ℚ) - 1)*n)) :
 d ≤ ((q : ℚ) - 1)*n :=
by linarith

example (d : ℚ) (q n : ℕ) (h1 : ((q : ℚ) - 1)*n ≥ 0) (h2 : d = 2/3*(((q : ℚ) - 1)*n)) :
 ((q : ℚ) - 1)*n - d = 1/3 * (((q : ℚ) - 1)*n) :=
by linarith

example (a : ℚ) (ha : 0 ≤ a) : 0 * 0 ≤ 2 * a :=
by linarith

example (x : ℚ) : id x ≥ x :=
by success_if_fail {linarith}; linarith!

example (x y z : ℚ) (hx : x < 5) (hx2 : x > 5) (hy : y < 5000000000) (hz : z > 34*y) : false :=
by linarith only [hx, hx2]

example (x y z : ℚ) (hx : x < 5) (hy : y < 5000000000) (hz : z > 34*y) : x ≤ 5 :=
by linarith only [hx]

example (x y : ℚ) (h : x < y) : x ≠ y := by linarith

example (x y : ℚ) (h : x < y) : ¬ x = y := by linarith

example (u v x y A B : ℚ)
(a : 0 < A)
(a_1 : 0 <= 1 - A)
(a_2 : 0 <= B - 1)
(a_3 : 0 <= B - x)
(a_4 : 0 <= B - y)
(a_5 : 0 <= u)
(a_6 : 0 <= v)
(a_7 : 0 < A - u)
(a_8 : 0 < A - v) :
 u * y + v * x + u * v < 3 * A * B :=
 by nlinarith

example (u v x y A B : ℚ) : (0 < A) → (A ≤ 1) → (1 ≤ B)
→ (x ≤ B) → ( y ≤ B)
→ (0 ≤ u ) → (0 ≤ v )
→ (u < A) → ( v < A)
→ (u * y + v * x + u * v < 3 * A * B) :=
begin
 intros,
 nlinarith
end

example (a b c z : ℚ) (_ : a ≤ z) (E0 : b ≤ c) (E1 : c ≤ a) (E2 : 0 ≤ c) : b ≤ a + c := by linarith

example (u v x y A B : ℚ)
(a_7 : 0 < A - u)
(a_8 : 0 < A - v) :
(0 ≤ A * (1 - A))
→ (0 ≤ A * (B - 1))
→ (0 < A * (A - u))
→ (0 ≤ (B - 1) * (A - u))
→ (0 ≤ (B - 1) * (A - v))
→ (0 ≤ (B - x) * v)
→ (0 ≤ (B - y) * u)
→ (0 ≤ u * (A - v))
→ u * y + v * x + u * v < 3 * A * B :=
begin
 intros,
 linarith
end

example (u v x y A B : ℚ)
(a : 0 < A)
(a_1 : 0 <= 1 - A)
(a_2 : 0 <= B - 1)
(a_3 : 0 <= B - x)
(a_4 : 0 <= B - y)
(a_5 : 0 <= u)
(a_6 : 0 <= v)
(a_7 : 0 < A - u)
(a_8 : 0 < A - v) :
 (0 < A * A)
-> (0 <= A * (1 - A))
-> (0 <= A * (B - 1))
-> (0 <= A * (B - x))
-> (0 <= A * (B - y))
-> (0 <= A * u)
-> (0 <= A * v)
-> (0 < A * (A - u))
-> (0 < A * (A - v))
-> (0 <= (1 - A) * A)
-> (0 <= (1 - A) * (1 - A))
-> (0 <= (1 - A) * (B - 1))
-> (0 <= (1 - A) * (B - x))
-> (0 <= (1 - A) * (B - y))
-> (0 <= (1 - A) * u)
-> (0 <= (1 - A) * v)
-> (0 <= (1 - A) * (A - u))
-> (0 <= (1 - A) * (A - v))
-> (0 <= (B - 1) * A)
-> (0 <= (B - 1) * (1 - A))
-> (0 <= (B - 1) * (B - 1))
-> (0 <= (B - 1) * (B - x))
-> (0 <= (B - 1) * (B - y))
-> (0 <= (B - 1) * u)
-> (0 <= (B - 1) * v)
-> (0 <= (B - 1) * (A - u))
-> (0 <= (B - 1) * (A - v))
-> (0 <= (B - x) * A)
-> (0 <= (B - x) * (1 - A))
-> (0 <= (B - x) * (B - 1))
-> (0 <= (B - x) * (B - x))
-> (0 <= (B - x) * (B - y))
-> (0 <= (B - x) * u)
-> (0 <= (B - x) * v)
-> (0 <= (B - x) * (A - u))
-> (0 <= (B - x) * (A - v))
-> (0 <= (B - y) * A)
-> (0 <= (B - y) * (1 - A))
-> (0 <= (B - y) * (B - 1))
-> (0 <= (B - y) * (B - x))
-> (0 <= (B - y) * (B - y))
-> (0 <= (B - y) * u)
-> (0 <= (B - y) * v)
-> (0 <= (B - y) * (A - u))
-> (0 <= (B - y) * (A - v))
-> (0 <= u * A)
-> (0 <= u * (1 - A))
-> (0 <= u * (B - 1))
-> (0 <= u * (B - x))
-> (0 <= u * (B - y))
-> (0 <= u * u)
-> (0 <= u * v)
-> (0 <= u * (A - u))
-> (0 <= u * (A - v))
-> (0 <= v * A)
-> (0 <= v * (1 - A))
-> (0 <= v * (B - 1))
-> (0 <= v * (B - x))
-> (0 <= v * (B - y))
-> (0 <= v * u)
-> (0 <= v * v)
-> (0 <= v * (A - u))
-> (0 <= v * (A - v))
-> (0 < (A - u) * A)
-> (0 <= (A - u) * (1 - A))
-> (0 <= (A - u) * (B - 1))
-> (0 <= (A - u) * (B - x))
-> (0 <= (A - u) * (B - y))
-> (0 <= (A - u) * u)
-> (0 <= (A - u) * v)
-> (0 < (A - u) * (A - u))
-> (0 < (A - u) * (A - v))
-> (0 < (A - v) * A)
-> (0 <= (A - v) * (1 - A))
-> (0 <= (A - v) * (B - 1))
-> (0 <= (A - v) * (B - x))
-> (0 <= (A - v) * (B - y))
-> (0 <= (A - v) * u)
-> (0 <= (A - v) * v)
-> (0 < (A - v) * (A - u))
-> (0 < (A - v) * (A - v))
->
 u * y + v * x + u * v < 3 * A * B :=
begin
 intros,
 linarith
end

example (A B : ℚ) : (0 < A) → (1 ≤ B) → (0 < A / 8 * B) :=
begin
 intros, nlinarith
end

example (x y : ℚ) : 0 ≤ x ^2 + y ^2 :=
by nlinarith

example (x y : ℚ) : 0 ≤ x*x + y*y :=
by nlinarith

example (x y : ℚ) : x = 0 → y = 0 → x*x + y*y = 0 :=
by intros; nlinarith

lemma norm_eq_zero_iff {x y : ℚ} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 :=
begin
 split,
 { intro, split; nlinarith },
 { intro, nlinarith }
end

lemma norm_nonpos_right {x y : ℚ} (h1 : x * x + y * y ≤ 0) : y = 0 :=
by nlinarith

lemma norm_nonpos_left (x y : ℚ) (h1 : x * x + y * y ≤ 0) : x = 0 :=
by nlinarith

variables {E : Type*} [add_group E]
example (f : ℤ → E) (h : 0 = f 0) : 1 ≤ 2 := by nlinarith
example (a : E) (h : a = a) : 1 ≤ 2 := by nlinarith

-- test that the apply bug doesn't affect linarith preprocessing

constant α : Type
variable [fact false] -- we work in an inconsistent context below
def leα : α → α → Prop := λ a b, ∀ c : α, true

noncomputable instance : linear_ordered_field α :=
by refine_struct { le := leα }; exact (fact.out false).elim

example (a : α) (ha : a < 2) : a ≤ a :=
by linarith

example (p q r s t u v w : ℕ) (h1 : p + u = q + t) (h2 : r + w = s + v) :
 p * r + q * s + (t * w + u * v) = p * s + q * r + (t * v + u * w) :=
by nlinarith

-- Tests involving a norm, including that squares in a type where `sq_nonneg` does not apply
-- do not cause an exception
variables {R : Type*} [ring R] (abs : R → ℚ)

lemma abs_nonneg' : ∀ r, 0 ≤ abs r := (fact.out false).elim

example (t : R) (a b : ℚ) (h : a ≤ b) : abs (t^2) * a ≤ abs (t^2) * b :=
by nlinarith [abs_nonneg' abs (t^2)]

example (t : R) (a b : ℚ) (h : a ≤ b) : a ≤ abs (t^2) + b :=
by linarith [abs_nonneg' abs (t^2)]

example (t : R) (a b : ℚ) (h : a ≤ b) : abs t * a ≤ abs t * b :=
by nlinarith [abs_nonneg' abs t]

constant T : Type

attribute [instance]
constant T_zero : ordered_ring T

namespace T

lemma zero_lt_one : (0 : T) < 1 := (fact.out false).elim

lemma works {a b : ℕ} (hab : a ≤ b) (h : b < a) : false :=
begin
 linarith,
end

end T

example (a b c : ℚ) (h : a ≠ b) (h3 : b ≠ c) (h2 : a ≥ b) : b ≠ c :=
by linarith {split_ne := tt}

example (a b c : ℚ) (h : a ≠ b) (h2 : a ≥ b) (h3 : b ≠ c) : a > b :=
by linarith {split_ne := tt}

example (x y : ℚ) (h₁ : 0 ≤ y) (h₂ : y ≤ x) : y * x ≤ x * x := by nlinarith

example (x y : ℚ) (h₁ : 0 ≤ y) (h₂ : y ≤ x) : y * x ≤ x ^ 2 := by nlinarith

axiom foo {x : int} : 1 ≤ x → 1 ≤ x*x
lemma bar (x y: int)(h : 0 ≤ y ∧ 1 ≤ x) : 1 ≤ y + x*x := by linarith [foo h.2]

-- issue #9822
lemma mytest (j : ℕ) (h : 0 < j) : j-1 < j:=
begin
 linarith,
end

