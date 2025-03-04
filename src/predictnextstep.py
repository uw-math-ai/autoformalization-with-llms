from neuralproofstate import NeuralProofState
import os
import dotenv
from litellm import completion

dotenv.load_dotenv()

os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")

def predict_next_step(nps: NeuralProofState, num_tactics=5, **kwargs):
    prompt = nps.to_prompt()
    
    params = {
        "model": "gpt-4o-mini",
        "messages": [{"role": "user", "content": prompt}],
        "max_tokens": 200,
        "temperature": 0.5,
        "top_p": 1,
        "n": num_tactics,
        "logprobs": True, 
    }
    
    params.update(kwargs)

    try:
        response = completion(**params)
        # print(f'{response['choices'][0]['logprobs']}')
        # choice = response['choices'][0]  # Assuming you want the first choice
        # logprobs = [token.logprob for token in choice['logprobs']['content']]
        # print(choice['message'])
        # print(logprobs)
        
        # print(response)

        tactics_list = []

        for choice in response.choices:
            tactic = choice.message["content"].strip()
            if choice.logprobs:
                sum_logprob = sum(token.logprob for token in choice.logprobs.content)
            else:
                sum_logprob = None

            tactics_list.append({
                "tactic": tactic,
                "log_probability": sum_logprob
            })

        return tactics_list

    except Exception as e:
        print(f"error {e}")
        return []