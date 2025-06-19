import LogicalFoundations.Basics

open Basics

theorem add_0_r : ∀ n : N, Add n N.O = n := by
  intro n
  induction n with
  | O => rfl
  | S v ih => simp [Basics.Add]; exact ih

theorem add_n_Sm : ∀ n m: N, N.S (n + m) = n + (N.S m) := by
  intro n m
  induction n with
  | O => rfl
  | S v ih => simp [Basics.Add]; exact ih

theorem add_comm : ∀ n m : N, n + m = m + n := by
  intro n m
  induction n with
  | O => simp [Basics.Add]; rw [add_0_r]
  | S v ih => simp [Basics.Add]; rw [<- add_n_Sm, ih]

theorem add_assoc : ∀ n m p : N, n + (m + p) = (n + m) + p := by
  intro n m p
  induction n with
  | O => rfl
  | S v ih => simp [Basics.Add]; exact ih

def Double (n: N) :=
  match n with
  | N.O => N.O
  | N.S v => N.S (N.S (Double v))

theorem double_plus : ∀ n, Double n = n + n := by
  intro n
  induction n with
  | O => rfl
  | S v ih => simp [Basics.Add, Double]; rw [ih, <- add_n_Sm];

def Even (n: N): Bool :=
  match n with
  | N.O => true
  | N.S n₁ =>
    match n₁ with
    | N.O => false
    | N.S n₂ => Even n₂

def Odd (n: N) : Bool := not (Even n)

theorem add_shuffle3 : ∀ n m p : N, n + (m + p) = m + (n + p) := by
  intro n m p
  induction n with
  | O => rfl
  | S v ih =>
    simp [add_assoc]
    rw [add_comm v.S m]

theorem mul_0_r: ∀ n: N, n * N.O = N.O := by
  intro n
  induction n with
  | O => rfl
  | S v ih => simp [Basics.Mul, ih, add_0_r]

theorem mul_m_nS : ∀ m n : N, m * n.S = m + m * n := by
  intros m n
  induction m with
  | O => rfl
  | S v ih => simp [Basics.Mul, ih, add_assoc, Basics.Add, add_comm];

theorem mul_comm : ∀ m n : N, m * n = n * m := by
  intro m n
  induction m with
  | O => simp [Basics.Mul, mul_0_r]
  | S v ih => simp [Basics.Mul, mul_m_nS, ih]
