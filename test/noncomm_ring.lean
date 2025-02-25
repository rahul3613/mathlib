import tactic.noncomm_ring

local notation (name := commutator) `⁅`a`, `b`⁆` := a * b - b * a
local infix (name := op) ` ⚬ `:70 := λ a b, a * b + b * a

variables {R : Type*} [ring R]
variables (a b c : R)

example : 0 = 0 := by noncomm_ring
example : a = a := by noncomm_ring

example : (a + b) * c = a * c + b * c := by noncomm_ring
example : a * (b + c) = a * b + a * c := by noncomm_ring
example : a - b = a + -b := by noncomm_ring
example : a * b * c = a * (b * c) := by noncomm_ring
example : a + a = a * 2 := by noncomm_ring
example : a + a = 2 * a := by noncomm_ring
example : -a = (-1) * a := by noncomm_ring
example : a + a + a = 3 * a := by noncomm_ring
example : a ^ 2 = a * a := by noncomm_ring
example : a ^ 3 = a * a * a := by noncomm_ring
example : (-a) * b = -(a * b) := by noncomm_ring
example : a * (-b) = -(a * b) := by noncomm_ring
example : a * (b + c + b + c - 2*b) = 2*a*c := by noncomm_ring
example : a * (b + c + b + c - (2 : ℕ) • b) = 2*a*c := by noncomm_ring
example : (a + b)^2 = a^2 + a*b + b*a + b^2 := by noncomm_ring
example : (a - b)^2 = a^2 - a*b - b*a + b^2 := by noncomm_ring
example : (a + b)^3 = a^3 + a^2*b + a*b*a + a*b^2 + b*a^2 + b*a*b + b^2*a + b^3 := by noncomm_ring
example : (a - b)^3 = a^3 - a^2*b - a*b*a + a*b^2 - b*a^2 + b*a*b + b^2*a - b^3 := by noncomm_ring

example : ⁅a, a⁆ = 0 := by noncomm_ring
example : ⁅a, b⁆ = -⁅b, a⁆ := by noncomm_ring
example : ⁅a + b, c⁆ = ⁅a, c⁆ + ⁅b, c⁆ := by noncomm_ring
example : ⁅a, b + c⁆ = ⁅a, b⁆ + ⁅a, c⁆ := by noncomm_ring
example : ⁅a, ⁅b, c⁆⁆ + ⁅b, ⁅c, a⁆⁆ + ⁅c, ⁅a, b⁆⁆ = 0 := by noncomm_ring
example : ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by noncomm_ring
example : ⁅a, ⁅b, c⁆⁆ = ⁅⁅a, b⁆, c⁆ + ⁅b, ⁅a, c⁆⁆ := by noncomm_ring
example : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ := by noncomm_ring
example : ⁅a * b, c⁆ = a * ⁅b, c⁆ + ⁅a, c⁆ * b := by noncomm_ring
example : ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := by noncomm_ring
example : ⁅3 * a, a⁆ = 0 := by noncomm_ring
example : ⁅a * -5, a⁆ = 0 := by noncomm_ring
example : ⁅a^3, a⁆ = 0 := by noncomm_ring

example : a ⚬ a = 2*a^2 := by noncomm_ring
example : (2 * a) ⚬ a = 4*a^2 := by noncomm_ring
example : a ⚬ b = b ⚬ a := by noncomm_ring
example : a ⚬ (b + c) = a ⚬ b + a ⚬ c := by noncomm_ring
example : (a + b) ⚬ c = a ⚬ c + b ⚬ c := by noncomm_ring
example : (a ⚬ b) ⚬ (a ⚬ a) = a ⚬ (b ⚬ (a ⚬ a)) := by noncomm_ring

example : ⁅a, b ⚬ c⁆ = ⁅a, b⁆ ⚬ c + b ⚬ ⁅a, c⁆ := by noncomm_ring
example : ⁅a ⚬ b, c⁆ = a ⚬ ⁅b, c⁆ + ⁅a, c⁆ ⚬ b := by noncomm_ring
example : (a ⚬ b) ⚬ c - a ⚬ (b ⚬ c) = -⁅⁅a, b⁆, c⁆ + ⁅a, ⁅b, c⁆⁆ := by noncomm_ring

example : a + -b = -b + a := by noncomm_ring

