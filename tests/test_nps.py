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
        
    def test_make_valid_goal(self):
        
        server = Server(project_path="./")
        
        root = NeuralProofState(thm_statement="(p q : Prop) : ¬(p → q) ↔ p ∧ ¬q", server=server)
        self.assertEqual(str(root.state), "\n⊢ forall (p q : Prop), ¬(p → q) ↔ p ∧ ¬q")
    
    # TODO: Write test for theorem with multiple context statements/hypothesis
    def test_complex_thm_statement(self):
        self.assertTrue(True)

if __name__ == '__main__':
    unittest.main()