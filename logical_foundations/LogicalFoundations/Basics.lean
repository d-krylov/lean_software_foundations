
namespace Basics

inductive N where
  | O : N
  | S : N → N

def ToNat (x : N) : Nat :=
  match x with
  | N.O => 0
  | N.S v  => Nat.succ (ToNat v)

def FromNat (x : Nat) : N :=
  match x with
  | 0 => N.O
  | Nat.succ v  => N.S (FromNat v)

def Add (x y: N) : N :=
  match x with
  | N.O => y
  | N.S v => N.S (Add v y)

def Sub (x y: N) : N :=
  match x, y with
  | N.O, _ => N.O
  | N.S _, N.O => x
  | N.S v₁, N.S v₂ => Sub v₁ v₂

def Mul (x y: N) : N :=
  match x with
  | N.O => N.O
  | N.S v => Add y (Mul v y)

infixl:65 " + " => Add
infixl:70 " * " => Mul

end Basics
