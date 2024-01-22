import Mathlib.Data.Nat.Prime

variable (p q : ℕ)
example (h : ↑p ∣ ↑q - ↑1) (hn : ¬p ∣ q - 1 ) : false := by contradiction
