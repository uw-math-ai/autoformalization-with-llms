# from neuralproofstate import NeuralProofState
# import os
# import dotenv
# from litellm import completion

# dotenv.load_dotenv()

# os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")


# def predict_next_step(nps: NeuralProofState, num_tactics=5, **kwargs):
#     prompt = nps.to_prompt()
    
#     params = {
#         #"model": "gpt-4o-mini",
#         #"model": "gpt-4-turbo-preview",
#         #"model": "gpt-4-turbo",
#         "model": "o3-mini",
#         #"model": "gpt-4o",
#         "messages": [{"role": "user", "content": prompt}],
#         "max_tokens": 200,
#         "temperature": 0.5,
#         "top_p": 1,
#         "n": num_tactics,
#         "logprobs": True, 
#     }
    
#     params.update(kwargs)

#     try:
#         response = completion(**params)

#         tactics_list = []

#         for choice in response.choices:
#             tactic = choice.message["content"].strip()
#             if choice.logprobs:
#                 sum_logprob = sum(token.logprob for token in choice.logprobs.content)
#             else:
#                 sum_logprob = None

#             tactics_list.append({
#                 "tactic": tactic,
#                 "log_probability": sum_logprob
#             })

#         return tactics_list

#     except Exception as e:
#         print(f"error {e}")
#         return []

####################################################################

from neuralproofstate import NeuralProofState
import os
import dotenv
import litellm
from litellm import completion

dotenv.load_dotenv()

# os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")
#os.environ["GEMINI_API_KEY"] = os.getenv("GEMINI_API_KEY")
#os.environ["ANTHROPIC_API_KEY"] = os.getenv("ANTHROPIC_API_KEY")

os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")

litellm.drop_params=True

def predict_next_step(nps: NeuralProofState, num_tactics=2, **kwargs):
    prompt = nps.to_prompt()
    
    params = {
        #"model": "gpt-4o-mini",
        #"model": "o3-mini",
        "model": "gpt-4o", # this has given the best results of the openai models in terms of not messing up syntax
        #"model": "claude-3-5-sonnet-20240620",
        #"model": "gemini/gemini-2.0-flash", 
        "messages": [{"role": "user", "content": prompt}],
        "max_tokens": 5000,
        "temperature": 0.5,
        "top_p": 1,
        "n": num_tactics,
    }
    
    params.update(kwargs)

    try:
        response = completion(**params)

        tactics_list = []

        for choice in response.choices:
            tactic = choice.message["content"].strip()
            if len(tactic) < 150: # occasionally getting some weird, very long tactics as bugs
                tactics_list.append({
                    "tactic": tactic,
                })

        return tactics_list

    except Exception as e:
        print(f"error {e}")
        return []


#############################################

# from neuralproofstate import NeuralProofState
# import os
# import dotenv
# from litellm import completion

# dotenv.load_dotenv()

# #os.environ["ANTHROPIC_API_KEY"] = os.getenv("ANTHROPIC_API_KEY")
# os.environ["DEEPSEEK_API_KEY"] = os.getenv("DEEPSEEK_API_KEY")

# def predict_next_step(nps: NeuralProofState, num_tactics=5, **kwargs):
#     prompt = nps.to_prompt()

#     params = {
#         #"model": "claude-3-5-sonnet-20240620",
#         "model": "deepseek/deepseek-reasoner",
#         "messages": [{"role": "user", "content": prompt}],
#         "max_tokens": 500,
#         "temperature": 0.5,
#         "top_p": 1,
#     }
    
#     params.update(kwargs)

#     tactics_list = []

#     try:
#         for _ in range(num_tactics):  # Send multiple requests
#             response = completion(**params)
#             tactic = response.choices[0].message["content"].strip()
#             tactics_list.append({"tactic": tactic})

#         return tactics_list

#     except Exception as e:
#         print(f"error {e}")
#         return []