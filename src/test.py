# import os
# import dotenv
# from litellm import completion

# dotenv.load_dotenv()
# os.environ["ANTHROPIC_API_KEY"] = os.getenv("ANTHROPIC_API_KEY")

# messages = [{"role": "user", "content": "Hey! how's it going?"}]
# response = completion(model="claude-3-opus-20240229", messages=messages)
# print(response)

# import os
# import dotenv
# import anthropic

# # Set your API key
# dotenv.load_dotenv()
# os.environ["ANTHROPIC_API_KEY"] = os.getenv("ANTHROPIC_API_KEY")
# client = anthropic.Anthropic()

# # Request with log probabilities
# response = client.messages.create(
#     model="claude-3-opus-20240229",
#     max_tokens=1024,
#     messages=[{"role": "user", "content": "Hey! how's it going?"}],
#     system="Respond briefly.",
#     stream=False,
#     logprobs=True,  # Enable log probabilities
#     top_logprobs=5   # Return top 5 probabilities per token
# )

# # Print the response
# print(response.content)

# # Access log probabilities
# if hasattr(response, 'logprobs'):
#     print("Log probabilities:", response.logprobs)

# from litellm import completion
# import os
# import dotenv

# dotenv.load_dotenv()
# os.environ["DEEPSEEK_API_KEY"] = os.getenv("DEEPSEEK_API_KEY")
# response = completion(
#     model="deepseek/deepseek-chat", 
#     messages=[
#        {"role": "user", "content": "hello from litellm"}
#    ],
# )
# print(response)

from litellm import completion
from google import genai
import os
import dotenv

dotenv.load_dotenv()
os.environ["GEMINI_API_KEY"] = os.getenv("GEMINI_API_KEY")
response = completion(
    model="gemini/gemini-2.0-flash", 
    messages=[{"role": "user", "content": "write code for saying hi from LiteLLM"}]
)
print(response)