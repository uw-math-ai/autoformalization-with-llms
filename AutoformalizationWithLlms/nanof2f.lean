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

-- The following are GPT generated proofs

theorem my_thm (x y : ℝ) : x * y = 0 → x = 0 ∨ y = 0 := by
intro h
apply mul_eq_zero.mp h

theorem my_thm2 (x y : ℝ) : x * y = 0 → x = 0 ∨ y = 0 := by
intro h
apply eq_zero_or_eq_zero_of_mul_eq_zero h

theorem my_thm3 (x y : ℝ) : x * y = 0 → x = 0 ∨ y = 0 := by
intro h
rw [mul_eq_zero] at h
exact h

theorem Prime.dvd_iff_eq {p a : ℕ} (hp : p.Prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a := by
  apply Nat.Prime.dvd_iff_eq hp a1

-- this proof was given by our search using 4o
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c) (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  have h₃ : b = (7 / 4) * a := by field_simp [h₂]
  have h₄ : 9 * (7 / 4 * a) = 20 * c := by rw [←h₁, h₃]
  linarith [h₄]
