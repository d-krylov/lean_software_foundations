import LogicalFoundations.Basics
import LogicalFoundations.Induction

open Basics

theorem silly_ex : ∀ p,
  (∀ n, Even n = true → Even n.S = false) →
  (∀ n, Even n = false → Odd n = true) →
  Even p = true → Odd p.S = true := by
  intro p h₁ h₂ h₃
  apply h₂
  apply h₁
  exact h₃
