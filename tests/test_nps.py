import sys
sys.path.append("./src")
from neuralproofstate import NeuralProofState

import unittest
from pantograph.server import Server

class TestNeuralProofState(unittest.TestCase):
    def test_basic_proof(self):
        
        server = Server(project_path="./")

        root = NeuralProofState(thm_statement="∀ (p q: Prop), p ∨ q → q ∨ p", server=server)
        next = root.apply_tactic("intro p q h")
        next = next.apply_tactic("rcases h with hp | hq")
        next = next.apply_tactic("left", goal_id=1)
        next = next.apply_tactic("exact hq", goal_id=0)
        next = next.apply_tactic("right")
        next = next.apply_tactic("exact hp")
        
        self.assertTrue(next.state.is_solved)
        
    '''def test_make_valid_goal(self):
        
        server = Server(project_path="./")

        root = NeuralProofState(thm_statement="(p q : Prop) : ¬(p → q) ↔ p ∧ ¬q", server=server)
        self.assertEqual(str(root.state), "\n⊢ forall (p q : Prop), ¬(p → q) ↔ p ∧ ¬q")''' 
        
    def test_wrong_tactic(self):
        imports=["Mathlib.Data.Nat.Factorization.Basic","Mathlib.Data.Nat.Prime.Basic"]
        server = Server(project_path="./", imports=imports)
        root = NeuralProofState(thm_statement="theorem mathd_numbertheory_728 : (29^13 - 5^13) % 7 = 3 := by", server=server)
        print(f"root: {root}")
        child = root.apply_tactic("hellooooo")
        
        self.assertEqual(child, None)
        
    def test_phrasebook(self):
        imports=["Mathlib.Data.Nat.Factorization.Basic","Mathlib.Data.Nat.Prime.Basic"]
        server = Server(project_path="./", imports=imports)
        root = NeuralProofState(thm_statement="theorem mathd_numbertheory_728 : (29^13 - 5^13) % 7 = 3 := by", server=server)
        
        print(root.to_prompt())


if __name__ == '__main__':
    unittest.main()