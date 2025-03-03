import sys
sys.path.append("./src")
from neuralproofstate import NeuralProofState
from heuristics import *

import unittest
from pantograph.server import Server

class TestHeuristics(unittest.TestCase):
    def test_heuristics(self):
        heuristics_list = [goal_hypothesis_comparison, goal_based, hypothesis_based, prev_tactics_based]
        server = Server(project_path="./")
        root = NeuralProofState(thm_statement="∀ (p q: Prop), p ∨ q → q ∨ p", server=server)
        
        tactics_list = ['intro p q h', 'rcases h with hp | hq', 'right', 'exact hp', 'left', 'exact hq']
        
        for i, tactic in enumerate(tactics_list):
            print(root.state)
            for h in heuristics_list:
                print(f"{h.__name__}: {h(root)}")
            root = root.apply_tactic(tactic)

            
if __name__ == '__main__':
    unittest.main()