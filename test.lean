import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d : ℕ)

example : a * b = b * a := by ring

#check Even
#check Odd

example : ∀ a, Even (2*a) := by
  intro a
  use a
  ring

example : ∀ a, Odd (2*a + 1) := by
  intro a
  use a

#check a^2

example : ∀ a, (Even a) → (Even (a^2 : ℕ)) := by
  intro a h
  let ⟨k,hk⟩ := h
  use 2*k^2
  rw [hk]
  ring

example : ∀ a, (Odd a) → (Odd (a^2 : ℕ)) := by
  intro a h
  let ⟨k,hk⟩ := h
  use 2*(k^2 + k)
  rw [hk]
  ring

example : a^2 = a * a := by
  ring

def Queven (n : Nat) : Prop :=
  ∃ k : ℕ, n = 4*k

def Quodd (n : Nat) : Prop :=
  ∃ k : ℕ, n = 4*k + 1

#check Queven
#check Quodd

example : Queven 4 := by
  use 1

example : Quodd 5 := by
  use 1

example : Quodd 1 := by
  use 0

example : ∀ a, (Even a) → (Queven (a^2 : ℕ)) := by
  intro a h
  let ⟨k,hk⟩ := h
  use k^2
  rw [hk]
  ring

example : ∀ a, (Odd a) → (Quodd (a^2 : ℕ)) := by
  intro a h
  let ⟨k,hk⟩ := h
  use k^2 + k
  rw [hk]
  ring


def Threeven (n : Nat) : Prop :=
  ∃ k : ℕ, n = 3*k

def Throdd (n : Nat) : Prop :=
  ∃ k : ℕ, n = 3*k + 1

example : Threeven 3 := by
  use 1

example : Throdd 4 := by
  use 1

example : Throdd 1 := by
  use 0

example : ∀ a, (Threeven a) → (Threeven (a^3 : ℕ)) := by
  intro a h
  let ⟨k,hk⟩ := h
  use 9 * k^3
  rw [hk]
  ring

example : ∀ a, (Throdd a) → (Throdd (a^3 : ℕ)) := by
  intro a h
  let ⟨k,hk⟩ := h
  use 9 * k^3 + 9 * k^2 + 3 * k
  rw [hk]
  ring
