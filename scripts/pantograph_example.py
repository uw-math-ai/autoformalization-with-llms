# the Python code to perform autoformalization
# The following is a bunch of examples of proofs begin solved with goal_tactic

from pantograph.server import Server

if __name__ == '__main__':
    imports = [
    "Mathlib.Data.Nat.Factorization.Basic",
    "Mathlib.Data.Nat.Prime.Basic",
    "Mathlib.Data.Real.Basic",
    "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.FieldSimp",
    "Mathlib.Tactic.Ring"
    ]
    
    server = Server(project_path="./", imports=imports)

    # prove a theorem
    state0 = server.goal_start("forall (p q: Prop), Or p q -> Or q p")
    print("state0: ", state0, "\n")
    state1 = server.goal_tactic(state0, goal_id=0, tactic="intro p q h")
    print("Used tactic: `intro p q h`")
    print("state1:\n", state1, "\n")
    state2 = server.goal_tactic(state1, goal_id=0, tactic="rcases h with hp | hq")
    print("Used tactic: `rcases h with hp | hq`")
    print("state2:\n", state2, "\n")
    state3 = server.goal_tactic(state2, goal_id=0, tactic="right")
    print("Used tactic: `right`")
    print("state3:\n", state3, "\n")
    state4 = server.goal_tactic(state3, goal_id=0, tactic="exact hp")
    print("Used tactic: `exact hp`")
    print("state4:\n", state4, "\n")
    state5 = server.goal_tactic(state4, goal_id=0, tactic="left")
    print("Used tactic: `left` on goal 1")
    print("state5:\n", state5, "\n")
    state6 = server.goal_tactic(state5, goal_id=0, tactic="exact hq")
    print("Used tactic: `exact hq`")
    print("state6:\n", state6, "\n")
    assert state6.is_solved
    
    state0 = server.goal_start("forall (x y : ℝ), x * y = 0 → x = 0 ∨ y = 0")
    print("state0:\n", state0, "\n")
    state1 = server.goal_tactic(state0, goal_id=0, tactic="intro x y")
    print("Used tactic: `intro x y`")
    print("state1:\n", state1, "\n")
    state2 = server.goal_tactic(state1, goal_id=0, tactic="contrapose")
    print("Used tactic: `contrapose`")
    print("state2:\n", state2, "\n")
    state3 = server.goal_tactic(state2, goal_id=0, tactic="rw [not_or]")
    print("Used tactic: `rw [not_or]`")
    print("state3:\n", state3, "\n")
    state4 = server.goal_tactic(state3, goal_id=0, tactic="rintro ⟨hx, hy⟩")
    print("Used tactic: `rintro ⟨hx, hy⟩`")
    print("state4:\n", state4, "\n")
    state5 = server.goal_tactic(state4, goal_id=0, tactic="exact mul_ne_zero hx hy")
    print("Used tactic: `exact mul_ne_zero hx hy`")
    print("state5:\n", state5, "\n")
    assert state5.is_solved
    
    state0 = server.goal_start("forall (x y : ℝ), x * y = 0 → x = 0 ∨ y = 0")
    print("state0:\n", state0, "\n")
    state1 = server.goal_tactic(state0, goal_id=0, tactic="intro x y")
    print("Used tactic: `intro x y`")
    print("state1:\n", state1, "\n")
    state2 = server.goal_tactic(state1, goal_id=0, tactic="simp")
    print("Used tactic: `simp`")
    print("state2:\n", state2, "\n")    
    assert state5.is_solved
    
    state0 = server.goal_start("forall (a b : ℝ), (h : a = b) → a + a = b + b")
    print("state0:\n", state0, "\n")
    state1 = server.goal_tactic(state0, goal_id=0, tactic="intro a b h")
    print("Used tactic: `intro a b h`")
    print("state1:\n", state1, "\n")
    state2 = server.goal_tactic(state1, goal_id=0, tactic="have h' : a + a = a + b := by rw [h]")
    print("Used tactic: `have h' : a + a = a + b := by rw [h]`")
    print("state2:\n", state2, "\n")
    state3 = server.goal_tactic(state2, goal_id=0, tactic="rw [←h]")
    print("Used tactic: `rw [←h]`")
    print("state3:\n", state3, "\n")
    assert state3.is_solved