from neuralproofstate import NeuralProofState
import os
import dotenv
from litellm import text_completion

dotenv.load_dotenv()

os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")
os.environ["OPENAI_API_BASE"] = os.getenv("OPENAI_API_BASE", "https://api.openai.com/v1")

def predict_next_step(state, prev_tactics, informal_info=None, num_tactics=5):
    proof_state = NeuralProofState(state=state, prev_tactics=prev_tactics, informal_info=informal_info)
    prompt = proof_state.to_prompt()

    try:
        response = text_completion(
            model="openai/gpt-3.5-turbo-instruct",
            prompt=prompt,
            max_tokens=200,
            temperature=0.5,
            top_p=1,
            n=num_tactics,
            logprobs=5, 
        )

        tactics_list = []

        for choice in response.choices:
            tactic = choice.text.strip()
            
            # tactic = tactic.replace("tactic:", "").strip()
            # tactic = tactic.replace("`", "").strip()
            # tactic = tactic.replace("tactic", "").strip()
            # tactic = tactic.replace(".", "").strip()

            log_prob = choice.logprobs.token_logprobs[0] if choice.logprobs else None

            tactics_list.append({
                "tactic": tactic,
                "log_probability": log_prob
            })

        return tactics_list

    except Exception as e:
        print(f"error {e}")
        return []