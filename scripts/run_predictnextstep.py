import sys

import os
import dotenv
sys.path.append(os.path.join(os.path.dirname(__file__), '../src'))

from predictnextstep import predict_next_step
from neuralproofstate import NeuralProofState

dotenv.load_dotenv()

os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")
os.environ["OPENAI_API_BASE"] = os.getenv("OPENAI_API_BASE", "https://api.openai.com/v1")

if __name__ == "__main__":
    # state = """theorem example (x y z : Nat) : x + (y + z) = (x + y) + z := by"""
    # prev_tactics = "rw [Nat.add_assoc]"

    # informal_info = """You may want to consider associativity of addition in this proof.
    #     The goal is to prove that addition is associative in natural numbers."""
    
    state = """theorem mathd_algebra_182 (y : ℂ) : 7 * (3 * y + 2) = 21 * y + 14 := by"""
    prev_tactics = None

    informal_info = None
        
        
    nps = NeuralProofState(state=state, prev_tactics=prev_tactics, informal_info=informal_info)

    tactics = predict_next_step(nps, num_tactics=5, temperature=1.3)

    print("Predicted next steps:")
    for tactic in tactics:
        print(f" ({tactic['log_probability']}) {tactic['tactic']}")
