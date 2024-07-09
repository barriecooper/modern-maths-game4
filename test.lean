import Mathlib.Data.Real.Basic
import Mathlib.Tactic
--import Mathlib.Util.Delaborators

--open Nat

variable (a b c d : ℕ)

example : a * b = b * a := by ring

#check Even

example : ∀ a, Even (2*a) := by
  intro a
  use a
  ring
