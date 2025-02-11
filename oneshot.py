import requests
import json
import re
from neuralproofstate import NeuralProofState

def send_prompt(prompt, api_key):
    # Construct the URL with the API key.
    url = f"https://generativelanguage.googleapis.com/v1beta/models/gemini-1.5-flash:generateContent?key={api_key}"
    
    # Define the HTTP headers.
    headers = {'Content-Type': 'application/json'}
    
    # Create the payload using the prompt variable.
    payload = {
        "contents": [
            {
                "parts": [
                    {"text": prompt}
                ]
            }
        ]
    }
    
    # Send the POST request.
    response = requests.post(url, headers=headers, json=payload)
    
    # Check for HTTP errors.
    if response.status_code != 200:
        raise Exception(f"Request failed with status {response.status_code}: {response.text}")
    
    # Parse and return the JSON response.
    return response.json()

if __name__ == "__main__":
    # Customize your prompt here.
    prompt = "In the next line, you will find a theorem written in Lean 4. Please generate a sequence (list format) of Lean 4 tactics that prove the theorem. Return only the tactics, nothing else.\n"
    theorem = "forall (p q: Prop), Or p q -> Or q p"

    root = NeuralProofState(theorem, new_proof=True)
    print(root,"\n")
    
    # Replace 'GEMINI_API_KEY' with your actual Gemini API key.
    api_key = "AIzaSyCJSBALFfDUFjL4kpCTBjKqu1-JfpoigfY"
    
    try:
        result = send_prompt(prompt+theorem, api_key)
        parsed = result["candidates"][0]["content"]["parts"][0]["text"]
        # Pretty-print the parsed JSON response.
        print("Response from Gemini API:")
        print(parsed)
        tactics = re.findall(r'`([^`]*)`', parsed)
        print(tactics)
        # print(json.dumps(result, indent=2))
        for tactic in tactics:
            next = root.apply_tactic(tactic)
            print(next,"\n")

    except Exception as e:
        print("Error:", e)
