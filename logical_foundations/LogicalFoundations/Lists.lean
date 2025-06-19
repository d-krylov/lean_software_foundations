import LogicalFoundations.Basics

open Basics

namespace Lists

inductive NatList where
  | nil : NatList
  | cons : Basics.N → NatList → NatList

instance : Coe (List N) NatList where
  coe := fun l => l.foldr NatList.cons NatList.nil

def Length (l: NatList) : Nat :=
  match l with
  | NatList.nil => 0
  | NatList.cons _ v => (Length v) + 1

def Append (l₁ l₂ : NatList) : NatList :=
  match l₁ with
  | NatList.nil => l₂
  | NatList.cons h t => NatList.cons h (Append t l₂)

def Reverse (l : NatList) : NatList :=
  match l with
  | NatList.nil => NatList.nil
  | NatList.cons h t => Append (Reverse t) [h]

def ToList (l : NatList) : List Nat :=
  match l with
  | NatList.nil => []
  | NatList.cons v t => (ToNat v) :: ToList t

infixl:65 " ++ " => Append

theorem append_assoc : ∀ l₁ l₂ l₃ : NatList, (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  intro l₁ l₂ l₃
  induction l₁ with
  | nil => rfl
  | cons h t ih => simp [Append, ih]

theorem append_length : ∀ l₁ l₂ : NatList, Length (l₁ ++ l₂) = (Length l₁) + (Length l₂) := by
  intros l₁ l₂
  induction l₁ with
  | nil => simp [Append, Length]
  | cons h t ih => simp [Append, Length, ih, Nat.add_comm, Nat.add_assoc];


end Lists
