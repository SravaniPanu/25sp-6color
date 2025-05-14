import Mathlib.Tactic

def isEvenPrime (n : Nat) : Bool :=
  n.Prime ∧ n = 2
