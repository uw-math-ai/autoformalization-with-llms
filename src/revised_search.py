from abc import abstractmethod
from pantograph.server import Server
import re
import os

# from predictnextstep import predict_next_step
import heapq
import random

# Use only one of these below!

# from neuralproofstate_two import NeuralProofState # load_sorry version
from neuralproofstate import NeuralProofState # goal_tactic version - has some bugs right now


# This is an interface for the model, and it should not be used in production
class Model():
    @abstractmethod
    def generate_tactics(self, **kwargs):
        tactics = ["List", "of", "strings"]
        return tactics
class NPSModel(Model):
    def generate_tactics(self, nps):
        tactics = predict_next_step(nps)
        return tactics
class LLMModel(Model):
    import litellm
    litellm.drop_params = True
    import dotenv
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
        self.params["messages"] = [{"role": "user", "content": prompt}],
        response = litellm.completion(**self.params)
        tactics_list = []

        for choice in response.choices:
            tactic = choice.message["content"].strip()
            if len(tactic) < 150: # occasionally getting some weird, very long tactics as bugs
                tactics_list.append(tactic)
        return tactics_list
class AStarSearchAgent():
    # model, server, heuristic
    def __init__(self, model, server, heuristic=None):
        self.model = model 
        self.server = server 
        self.heuristic = heuristic if heuristic else self.default_heuristic
        
    def default_heuristic(self, current, neighbor=None):
        return random.uniform(0,1)
    
    def get_successors(self, nps, k_tries=3):
        successors = []

        for i in range(k_tries):
            tactics = self.model.generate_tactics(nps)
            failures = 0
            for tactic in tactics: 
                try:
                    tactic = tactic['tactic'] # for some reason the tactics are a dictionary, something in predictnextstep.py needs fixing
                    child = nps.apply_tactic(tactic)
                    if child is not None:
                        successors.append(child)
                    else:
                        nps.add_failed_tactic(tactic) # TODO: this is never called because NPS currently doesn't handle errors correctly
                        failures += 1
                except Exception as e:
                    # print(f"get successor error: {e}")
                    pass
            if failures == 0:
                break
                
        return successors

    def search(self, initial_sketch, max_steps, verbose):
        unit = self.server.load_sorry(initial_sketch + f"\nsorry")
        goal_state = unit[0].goal_state
        error_messages = [s for s in unit[0].messages if "error" in s]
        if goal_state is None: 
            if verbose:
                print("No goals to solve.")
            return [], False, 0, "No goals to solve."
        elif len(error_messages) > 0:
            if verbose:
                print(f"Failed to create a goal state, error messages = {error_messages}")
            return [], False, 0, f"Failed to create a goal state, error messages = {error_messages}"

        initial_state = NeuralProofState(thm_statement=initial_sketch, server=self.server)
                
        steps = 0
        p_queue = []
        heapq.heapify(p_queue)
        
        # sorts by heuristic output
        heapq.heappush(p_queue, (self.heuristic(initial_state), initial_state))

        while len(p_queue) > 0 and steps < max_steps:
            if verbose:
                # TODO: print the queue, possibly just one node
                pass
            _, nps = heapq.heappop(p_queue)
            successors = self.get_successors(nps)
            
            for successor in successors:
                goal_state = successor.state
                if goal_state is None or goal_state.__str__() is None or len(goal_state.__str__()) == 0: # TODO: not sure which one of these is actually required
                    return successor # TODO: some bug where very occasionally successor is a tuple? idk
                else:
                    heapq.heappush(p_queue, (self.heuristic(successor) + len(successor.prev_tactics), successor))
            
            if len(p_queue) == 0:
                heapq.heappush(p_queue, (self.heuristic(nps) + len(nps.prev_tactics), nps))
            
            steps += 1  
            
        return None
    
if __name__ == '__main__':
    model = NPSModel()
    imports = [
    "Mathlib.Data.Nat.Factorization.Basic",
    "Mathlib.Data.Nat.Prime.Basic",
    "Mathlib.Data.Real.Basic",
    "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.FieldSimp",
    "Mathlib.Tactic.Ring"
    ]
    # ['Mathlib.Data.Real.Sqrt', 'Mathlib.Data.Real.Basic']
    server = Server(project_path="./", imports=imports)
    lean_sketch = """theorem Prime.dvd_iff_eq {p a : ℕ} (hp : p.Prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a := by"""
    
    search_agent = AStarSearchAgent(model, server)
    nps = search_agent.search(initial_sketch=lean_sketch, max_steps=10, verbose=True)
    
    if nps is not None:
        print(f"Proof found!")
        nps.verbose_string()
        print(f"proof:\n")
        print(nps.get_proof())
    else:
        print(f"No proof found")
# Example if you want to try the LLMModel
"""
if __name__ == "__main__":


    model = LLMModel()

    state = \"""theorem amc12_2000_p11 (a b : ℝ) (h₀ : a ≠ 0 ∧ b ≠ 0) (h₁ : a * b = a - b) :
    a / b + b / a - a * b = 2 := by\"""
    nps = NeuralProofState(state=state)

    print(model.generate_tactics(nps))
"""
