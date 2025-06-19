
theorem proj2 : ∀ P Q : Prop, P ∧ Q → Q := by
  intro P Q h
  cases h with
  | intro h₁ h₂ => exact h₂

theorem and_commut : ∀ P Q : Prop, P ∧ Q → Q ∧ P := by
  intro P Q h
  cases h with
  | intro h₁ h₂ =>
    constructor
    exact h₂
    exact h₁

theorem iff_sym : ∀ P Q : Prop, (P ↔ Q) → (Q ↔ P) := by
  intro P Q h
  cases h with
  | intro h₁ h₂ =>
    constructor
    assumption
    assumption
