import group_theory.group_action.basic

variables (R M S : Type*)

/-- Some arbitrary type depending on `has_smul R M` -/
@[irreducible, nolint has_nonempty_instance unused_arguments]
def foo [has_smul R M] : Type* := ℕ

variables [has_smul R M] [has_smul S R] [has_smul S M]

/-- This instance is incompatible with `has_smul.comp.is_scalar_tower`.
However, all its parameters are (instance) implicits or irreducible defs, so it
should not be dangerous. -/
@[nolint unused_arguments]
instance foo.has_smul [is_scalar_tower S R M] : has_smul S (foo R M) :=
⟨λ _ _, by { unfold foo, exact 37 }⟩

-- If there is no `is_scalar_tower S R M` parameter, this should fail quickly,
-- not loop forever.
example : has_smul S (foo R M) :=
begin
 tactic.success_if_fail_with_msg tactic.interactive.apply_instance
 "tactic.mk_instance failed to generate instance for
 has_smul S (foo R M)",
 unfold foo,
 exact ⟨λ _ _, 37⟩
end

/-
local attribute [instance] has_smul.comp.is_scalar_tower
-- When `has_smul.comp.is_scalar_tower` is an instance, this recurses indefinitely.
example : has_smul S (foo R M) :=
begin
 tactic.success_if_fail_with_msg tactic.interactive.apply_instance
 "maximum class-instance resolution depth has been reached (the limit can be increased by setting option 'class.instance_max_depth') (the class-instance resolution trace can be visualized by setting option 'trace.class_instances')",
 unfold foo,
 exact ⟨λ _ _, 37⟩
end
-/

