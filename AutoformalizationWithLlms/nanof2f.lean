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
