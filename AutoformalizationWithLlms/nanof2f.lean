import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- Nanof2f is like minif2f but even smaller!

def hello := "world"

example : forall (p q: Prop), Or p q -> Or q p := by
  intro p q h
  rcases h with hp | hq
  right
  exact hp
  left
  exact hq

example : forall (p q : Prop), p ∧ q → q ∧ p := by
  intro p q h
  constructor
  exact h.right
  exact h.left

example (p q : Prop) : ¬(p → q) ↔ p ∧ ¬q := by
  constructor
  intro h
  sorry -- TODO: add proof
  intro h
  sorry

example (x y : ℝ) : x * y = 0 → x = 0 ∨ y = 0 := by
  contrapose
  rw [not_or]
  intro ⟨hx, hy⟩
  exact mul_ne_zero hx hy

example (a b : ℝ) (h : a = b) : a + a = b + b := by
  have h' : a + a = a + b := by rw [h]
  rw [←h]

theorem my_thm (x y : ℝ) : x * y = 0 → x = 0 ∨ y = 0 := by
intro h
exact mul_eq_zero.mp h
