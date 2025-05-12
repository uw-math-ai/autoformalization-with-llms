from abc import abstractmethod
def Model():
    @abstractmethod
    def generate_tactics(self, state, prompt=None):
        raise NotImplementedError("Subclasses must implement generate_tactics")
class LLMModel():
    import litellm, os, dotenv
    litellm.drop_params = True
    dotenv.load_dotenv()
    os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")

    def __init__(self, **kwargs):
        self.params = {
            #"model": "gpt-4o-mini",
            #"model": "o3-mini",
            "model": "gpt-4o", # this has given the best results of the openai models in terms of not messing up syntax
            #"model": "claude-3-5-sonnet-20240620",
            #"model": "gemini/gemini-2.0-flash", 
            "max_tokens": 500,
            "temperature": 0.5,
            "top_p": 1,
            "n": 3,
        }
        self.params.update(kwargs)
    def generate_tactics(self, nps, prompt=None):
        if not prompt:
            prompt = nps.to_prompt()
        self.params["messages"] = [{"role": "user", "content": prompt}]
        response = self.litellm.completion(**self.params)
        tactics_list = []

        for choice in response.choices:
            tactic = choice.message["content"].strip()
            if len(tactic) < 150: # occasionally getting some weird, very long tactics as bugs
                tactics_list.append(tactic)
        return tactics_list
    
    
class AttilaModel():
    import litellm, os, dotenv
    litellm.drop_params = True
    dotenv.load_dotenv()
    os.environ["GEMINI_API_KEY"] = os.getenv("GEMINI_API_KEY")

    def __init__(self, theorem=None, theorem_statement=None, **kwargs):
        self.params = {
            #"model": "gpt-4o-mini",
            #"model": "o3-mini",
            #"model": "gpt-4o", # this has given the best results of the openai models in terms of not messing up syntax
            #"model": "claude-3-5-sonnet-20240620",
            #"model": "gemini/gemini-2.0-flash", 
            #"model": "gemini/gemini-2.5-flash", 
            "max_tokens": 500,
            "temperature": 0.7,
            "thinking": {"type": "enabled", "budget_tokens": 1024},
            "top_p": 1,
            "n": 3,
        }
        self.params.update(kwargs)

        prompt = None
        self.informal_proof = ""
        if theorem and theorem_statement:
            prompt =  f"Prove the following theorem: {theorem} \n\nYou may use the following Lean4 statement if it helps you: {theorem_statement} \n\n Do not start proving this theorem in Lean just yet, but you may reference any Lean4 code to help you solve the theorem in Lean eventually. "
        elif theorem_statement:
            prompt = f"Generate an informal proof (Not in lean, but as you would for a mathematical paper for example) for the following Lean4 theorem statement {theorem_statement}.  Do not start proving this theorem in Lean just yet, but you may reference any Lean4 code to help you solve the theorem in Lean eventually."
        if prompt:
            self.params["messages"] = [{"role": "user", "content": prompt}]
            self.informal_proof = self.litellm.completion(**self.params)
            print(self.informal_proof)
        self.prompt = self.informal_proof + "\n\n"
    """
    generate_tactics(self -> self,
                     current_state -> current goal state that the model uses to generate next tactic 
                     informal_proof -> the proof that the model generated that's not formalized in lean4
                     current_tactic=None -> the most recent tactic that was used to alter the goal state
    Notes: make sure that informal proof contains the theorem statement in both lean and informally.
    """
    def generate_tactics(self, current_state , current_tactic=None, theorem_statement=None):
        if current_tactic:
            prompt = f"Successfully applied {current_tactic} \n\n The goal state is now: {current_state}"
        elif theorem_statement:
            prompt = f"Now prove this same theorem in Lean4: \n {theorem_statement}. \n\n Provide only the tactic that you will use to solve this theorem, after thinking about how to solve it. In your output to the user only give the tactic that you want to use. \n\n The current goal state is {current_state}"
        else: 
            return "Must provide either current_tactic or theorem_statement!"
        if self.params.get("messages"):
            self.params["messages"].append({"role": "user", "content": prompt})
        else:
            self.params["messages"] = [{"role": "user", "content": prompt}]
        response = self.litellm.completion(**self.params)
        tactics_list = []

        for choice in response.choices:
            tactic = choice.message["content"].strip()
            if len(tactic) < 150: # occasionally getting some weird, very long tactics as bugs
                tactics_list.append(tactic.replace("`", ""))
        return tactics_list

class AttilaModel():
    import litellm, os, dotenv
    litellm.drop_params = True
    dotenv.load_dotenv()
    os.environ["GEMINI_API_KEY"] = os.getenv("GEMINI_API_KEY")

    def __init__(self, theorem=None, theorem_statement=None, **kwargs):
        self.params = {
            #"model": "gpt-4o-mini",
            #"model": "o3-mini",
            #"model": "gpt-4o", # this has given the best results of the openai models in terms of not messing up syntax
            #"model": "claude-3-5-sonnet-20240620",
            #"model": "gemini/gemini-2.0-flash", 
            #"model": "gemini/gemini-2.5-flash", 
            "max_tokens": 500,
            "temperature": 0.7,
            "thinking": {"type": "enabled", "budget_tokens": 1024},
            "top_p": 1,
            "n": 3,
        }
        self.params.update(kwargs)

        prompt = None
        self.informal_proof = ""
        if theorem and theorem_statement:
            prompt =  f"Prove the following theorem: {theorem} \n\nYou may use the following Lean4 statement if it helps you: {theorem_statement} \n\n Do not start proving this theorem in Lean just yet, but you may reference any Lean4 code to help you solve the theorem in Lean eventually. "
        elif theorem_statement:
            prompt = f"Generate an informal proof (Not in lean, but as you would for a mathematical paper for example) for the following Lean4 theorem statement {theorem_statement}.  Do not start proving this theorem in Lean just yet, but you may reference any Lean4 code to help you solve the theorem in Lean eventually."
        if prompt:
            self.params["messages"] = [{"role": "user", "content": prompt}]
            self.informal_proof = self.litellm.completion(**self.params)
            print(self.informal_proof)
        self.prompt = self.informal_proof + "\n\n"
    """
    generate_tactics(self -> self,
                     current_state -> current goal state that the model uses to generate next tactic 
                     informal_proof -> the proof that the model generated that's not formalized in lean4
                     current_tactic=None -> the most recent tactic that was used to alter the goal state
    Notes: make sure that informal proof contains the theorem statement in both lean and informally.
    """
    def generate_tactics(self, current_state , current_tactic=None, theorem_statement=None):
        if current_tactic:
            prompt = f"Successfully applied {current_tactic} \n\n The goal state is now: {current_state}"
        elif theorem_statement:
            prompt = f"Now prove this same theorem in Lean4: \n {theorem_statement}. \n\n Provide only the tactic that you will use to solve this theorem, after thinking about how to solve it. In your output to the user only give the tactic that you want to use. \n\n The current goal state is {current_state}"
        else: 
            return "Must provide either current_tactic or theorem_statement!"
        if self.params.get("messages"):
            self.params["messages"].append({"role": "user", "content": prompt})
        else:
            self.params["messages"] = [{"role": "user", "content": prompt}]
        response = self.litellm.completion(**self.params)
        tactics_list = []

        for choice in response.choices:
            tactic = choice.message["content"].strip()
            if len(tactic) < 150: # occasionally getting some weird, very long tactics as bugs
                tactics_list.append(tactic.replace("`", ""))
        return tactics_list

'''
import google.generativeai as genai
import os
import dotenv

class AttilaModel2:
    def __init__(self, theorem=None, theorem_statement=None, model_name="gemini-1.5-pro-latest", **kwargs):
        dotenv.load_dotenv()
        api_key = os.getenv("GEMINI_API_KEY")
        if not api_key:
            api_key = os.getenv("GOOGLE_API_KEY") 
        
        if not api_key:
            raise ValueError("GEMINI_API_KEY or GOOGLE_API_KEY not found in environment variables.")
        
        genai.configure(api_key=api_key)

        self.model = genai.GenerativeModel(model_name)
        
        default_params = {
            "max_output_tokens": 500,
            "temperature": 0.7,
            "top_p": 1.0,
            "candidate_count": 3
        }
        
        gemini_constructor_kwargs = {
            "temperature": kwargs.get("temperature", default_params["temperature"]),
            "top_p": kwargs.get("top_p", default_params["top_p"]),
            "max_output_tokens": kwargs.get("max_tokens", default_params["max_output_tokens"]),
            "candidate_count": kwargs.get("n", default_params["candidate_count"]),
        }
        self.generation_config = genai.types.GenerationConfig(**gemini_constructor_kwargs)

        self.history = []
        self.informal_proof = ""

        initial_prompt_text = None
        if theorem and theorem_statement:
            initial_prompt_text = (
                f"Prove the following theorem: {theorem} \n\n"
                f"You may use the following Lean4 statement if it helps you: {theorem_statement} \n\n"
                "Do not start proving this theorem in Lean just yet, but you may reference any Lean4 code "
                "to help you solve the theorem in Lean eventually. "
            )
        elif theorem_statement:
            initial_prompt_text = (
                "Generate an informal proof (Not in lean, but as you would for a mathematical paper for example) "
                f"for the following Lean4 theorem statement {theorem_statement}. "
                "Do not start proving this theorem in Lean just yet, but you may reference any Lean4 code "
                "to help you solve the theorem in Lean eventually."
            )

        if initial_prompt_text:
            call_history_for_informal_proof = [{'role': 'user', 'parts': [{'text': initial_prompt_text}]}]
            
            try:
                response = self.model.generate_content(
                    call_history_for_informal_proof,
                    generation_config=self.generation_config
                )
                
                if response.candidates and response.candidates[0].content and response.candidates[0].content.parts:
                    self.informal_proof = response.candidates[0].content.parts[0].text
                else:
                    self.informal_proof = "Error: Could not generate informal proof. The response was empty or invalid."
                    if response.prompt_feedback:
                         self.informal_proof += f" (Prompt Feedback: {response.prompt_feedback})"

            except Exception as e:
                self.informal_proof = f"Exception during informal proof generation: {str(e)}"
            
            print(f"Informal Proof Generation Output:\n{self.informal_proof}")

            self.history.append({'role': 'user', 'parts': [{'text': initial_prompt_text}]})
            if not self.informal_proof.startswith("Error:") and not self.informal_proof.startswith("Exception:"):
                 self.history.append({'role': 'model', 'parts': [{'text': self.informal_proof}]})

        self.prompt = self.informal_proof + "\n\n"

    def generate_tactics(self, current_state, current_tactic=None, theorem_statement=None):
        tactic_prompt_text = None
        if current_tactic:
            tactic_prompt_text = (
                f"Successfully applied {current_tactic} \n\n"
                f"The goal state is now: {current_state} \n\n"
                f"Provide only the tactic that you will use to advance this theorem by one step. Do not provide multiple tactics. Your output should contain only the tactic, do anything thinking in the corresponding area. Use Lean4 syntax."
            )
        elif theorem_statement:
            tactic_prompt_text = (
                f"Now prove this same theorem in Lean4: \n {theorem_statement}. \n\n"
                f"The current goal state is {current_state}"
                f"Provide only the tactic that you will use to advance this theorem by one step. Do not provide multiple tactics. Your output should contain only the tactic, do anything thinking in the corresponding area. Use Lean4 syntax."
            )
        else: 
            return ["Error: Must provide either current_tactic or theorem_statement!"]

        current_call_history = self.history + [{'role': 'user', 'parts': [{'text': tactic_prompt_text}]}]
        
        tactics_list = []
        try:
            response = self.model.generate_content(
                current_call_history,
                generation_config=self.generation_config
            )

            if response.candidates:
                for candidate in response.candidates:
                    if candidate.content and candidate.content.parts:
                        tactic_text = candidate.content.parts[0].text.strip()
                        if len(tactic_text) < 150: 
                            tactics_list.append(tactic_text.replace("`", ""))
            else:
                error_msg = "Error: No tactics generated. The response contained no candidates."
                if response.prompt_feedback:
                    error_msg += f" (Prompt Feedback: {response.prompt_feedback})"
                tactics_list.append(error_msg)

        except Exception as e:
            error_message = f"Exception during tactic generation: {str(e)}"
            print(error_message)
            return [error_message]
        return tactics_list
if __name__ == "__main__":
    from neuralproofstate import NeuralProofState
    # from eval_w_params import get_imports_val
    # imports, _ = get_imports_val()

    from pantograph import Server
    server = Server(project_path="./")
    theorem = "example : forall (p q: Prop), Or p q -> Or q p := by"
    nps = NeuralProofState(server=server, thm_statement=theorem)
    model = AttilaModel2()
    print(model.generate_tactics(nps.state, None, theorem))
'''