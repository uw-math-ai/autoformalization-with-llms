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

if __name__ == "__main__":
    from neuralproofstate import NeuralProofState
    # from eval_w_params import get_imports_val
    # imports, _ = get_imports_val()

    from pantograph import Server
    server = Server(project_path="./")
    nps = NeuralProofState(server=server, thm_statement="example : forall (p q: Prop), Or p q -> Or q p := by")
    model = LLMModel()
    print(model.generate_tactics(nps))
    
    
