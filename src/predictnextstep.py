# from neuralproofstate import NeuralProofState
# from openai import OpenAI
# import os
# import dotenv

# dotenv.load_dotenv()
# client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# def predict_next_step(state, prev_tactics, informal_info=None, num_tactics=5):
#     api_key = os.getenv("OPENAI_API_KEY")
#     proof_state = NeuralProofState(state=state, prev_tactics=prev_tactics, informal_info=informal_info)
#     prompt = proof_state.to_prompt()

#     try:
#         response = client.chat.completions.create(
#             model="gpt-3.5-turbo",
#             messages=[{"role": "system", "content": prompt}],
#             max_tokens=150,
#             temperature=0.7,
#             top_p=1,
#             n=num_tactics,
#         )

#         tactics = response.choices
#         tactics_list = []

#         for choice in tactics:
#             tactic = choice.text.strip()
#             log_prob = choice.logprobs.token_logprobs[0]  # get log prob for each tactic

#             tactics_list.append({
#                 "tactic": tactic,
#                 "log_probability": log_prob
#             })

#         return tactics_list

#     except Exception as e:
#         print(f"error {e}")
#         return []

# if __name__ == "__main__":
#     state = """theorem example (x y z : Nat) : x + (y + z) = (x + y) + z := by"""
#     prev_tactics = "rw [Nat.add_assoc]"

#     informal_info = """You may want to consider associativity of addition in this proof.
#         The goal is to prove that addition is associative in natural numbers."""

#     tactics = predict_next_step(state, prev_tactics)

#     print("Predicted next steps:")
#     for tactic in tactics:
#         print(f" ({tactic['log_probability']}) {tactic['tactic']}")

from neuralproofstate import NeuralProofState
import os
import dotenv
from litellm import text_completion

dotenv.load_dotenv()


os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")
os.environ["OPENAI_API_BASE"] = os.getenv("OPENAI_API_BASE", "https://api.openai.com/v1")

def predict_next_step(state, prev_tactics, informal_info=None, num_tactics=5):
    # api_key = os.getenv("OPENAI_API_KEY")
    proof_state = NeuralProofState(state=state, prev_tactics=prev_tactics, informal_info=informal_info)
    prompt = proof_state.to_prompt()

    try:
        response = text_completion(
            model="openai/gpt-3.5-turbo-instruct",
            prompt=prompt,
            max_tokens=150,
            temperature=0.8,
            top_p=1,
            n=num_tactics,
            logprobs=5, 
        )

        tactics_list = []

        for choice in response.choices:
            tactic = choice.text.strip()
            log_prob = choice.logprobs.token_logprobs[0] if choice.logprobs else None

            tactics_list.append({
                "tactic": tactic,
                "log_probability": log_prob
            })

        return tactics_list

    except Exception as e:
        print(f"error {e}")
        return []