from openai import OpenAI
import os
import dotenv

dotenv.load_dotenv()
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

def to_prompt(state, prev_tactics, informal_info=None):
    prompt = f"""Given the Lean 4 code: \n{state}\n Provide the next tactic to 
    close all goals and prove the theorem. The previous tactics used to prove this theorem are as follows: \n{prev_tactics}\n"""

    if informal_info:
        prompt += f"""You should also consider the following information when choosing a tactic: \n{informal_info}\n"""

    prompt += f"""Give a list of possible next tactics with their log probabilities. 
    Format your response as a JSON array of objects, each containing 'tactic' and 'log_probability' fields.
    Do not include 'by' at the start of your tactics, as it is already included in the theorem header."""

    return prompt

def predict_next_step(state, prev_tactics, informal_info=None, num_tactics=5):
    api_key = os.getenv("OPENAI_API_KEY")
    prompt = to_prompt(state, prev_tactics, informal_info)

    try:
        response = client.chat.completions.create(
            model="gpt-3.5-turbo",
            messages=[{"role": "system", "content": prompt}],
            max_tokens=150,
            temperature=0.7,
            top_p=1,
            n=num_tactics,
        )

        tactics = response.choices
        tactics_list = []

        for choice in tactics:
            tactic = choice.text.strip()
            log_prob = choice.logprobs.token_logprobs[0]  # get log prob for each tactic

            tactics_list.append({
                "tactic": tactic,
                "log_probability": log_prob
            })

        return tactics_list

    except Exception as e:
        print(f"error {e}")
        return []

if __name__ == "__main__":
    state = """theorem example (x y z : Nat) : x + (y + z) = (x + y) + z := by"""
    prev_tactics = "rw [Nat.add_assoc]"

    informal_info = """You may want to consider associativity of addition in this proof.
        The goal is to prove that addition is associative in natural numbers."""

    tactics = predict_next_step(state, prev_tactics)

    print("Predicted next steps:")
    for tactic in tactics:
        print(f" ({tactic['log_probability']}) {tactic['tactic']}")