import sys

import os
import dotenv
sys.path.append(os.path.join(os.path.dirname(__file__), '../src'))

from predictnextstep import predict_next_step

dotenv.load_dotenv()

os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")
os.environ["OPENAI_API_BASE"] = os.getenv("OPENAI_API_BASE", "https://api.openai.com/v1")

if __name__ == "__main__":
    state = """theorem example (x y z : Nat) : x + (y + z) = (x + y) + z := by"""
    prev_tactics = "rw [Nat.add_assoc]"

    informal_info = """You may want to consider associativity of addition in this proof.
        The goal is to prove that addition is associative in natural numbers."""

    tactics = predict_next_step(state, prev_tactics)

    print("Predicted next steps:")
    for tactic in tactics:
        print(f" ({tactic['log_probability']}) {tactic['tactic']}")
