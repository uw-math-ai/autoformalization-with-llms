from abc import abstractmethod
from pantograph.server import Server
import re

import heapq


# Contains information about the current proof state, including the unsolved goals and previously used tactics

class NeuralProofState():
    
    # TODO add server imports for definitions of real numbers, etc
    def __init__(self, state=None, thm_statement=None, prev_tactics=None, 
                 informal_info=None, server=None, neg_log_prob=None, parent=None):   

        self.informal_info = informal_info
        self.server = server
        self.thm_statement = thm_statement
        
        if thm_statement:  
            self.state = self.server.load_sorry(thm_statement + "\nsorry")
            self.prev_tactics = []
            self.neg_log_prob = 0
            self.parent = None
        else:
            self.state = state
            self.prev_tactics = prev_tactics
            self.neg_log_prob = neg_log_prob
            self.parent = parent
        
        self.tactics_to_child_states = {}
    
    # TODO currently have to specify a goal to apply a tactic, which isn't ideal. Would like to just check all goals
    # TODO add log probability as a parameter
    def apply_tactic(self, tactic, goal_id=0):
        new_state = self.server.load_sorry("\n".join([self.thm_statement] + self.prev_tactics + [tactic, "sorry"]))        
        child_node = NeuralProofState(state=new_state, prev_tactics=self.prev_tactics + [tactic], 
                                      informal_info=self.informal_info, server=self.server, parent=self)
        
        self.tactics_to_child_states[tactic] = child_node
        return child_node

    def to_prompt(self):
        prompt = f"""Given the Lean 4 code: \n{self.state}\n Provide the next tactic 
    to progress towards proving the theorem. The previous tactics used to prove this theorem are as follows: \n{self.prev_tactics}\n"""
        
        if self.informal_info:
            prompt += f"""You should also consider the following information when choosing a tactic: \n{self.informal_info}\n"""
        
        prompt += f"""Give only the next Lean tactic and no other information in your response. 
        Do not include 'by' at the start of your response, as it is already included in the theorem header."""
        
        return prompt
    
    def __str__(self):
        if len(self.state.__str__()) == 0:
            return "No more goals!"
        return self.state.__str__()
    
    def verbose_string(self):
        print("Neural Proof State Object: ")
        if len(self.state.__str__()) == 0:
            return "No more goals!"
        else:
            print(self.state)
        print(f"Previous tactics: {self.prev_tactics}")
        print(f"Number of child nodes: {len(self.tactics_to_child_states.keys())}")

class Model():
    @abstractmethod
    def generate_tactics(self, current, current_code):
        tactics = ["List", "of", "strings"]
        return tactics
class DojoModel(Model):
    def __init__(self, device = None, generate_config = None):
        model_name = "kaiyuy/leandojo-lean4-tacgen-byt5-small"
        self.device = device if device else "cpu"
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        self.model = AutoModelForSeq2SeqLM.from_pretrained(model_name)
        self.model.to(self.device)
        self.generate_config = {
            "max_length": 50,
            "num_beams": 15,
            "length_penalty": 0.0,
            "do_sample": True,
            "num_return_sequences": 10,
            "early_stopping": False,
            "output_scores": True,
            "return_dict_in_generate": True,
            "temperature": 1.0,
        }
        if generate_config:
            self.generate_config.update(generate_config)
    def format_prompt(self, current, goal_index=0):
        goal = current.state.goals[goal_index]
        return str(goal)

    def generate(self, prompt):
        inputs = self.tokenizer(prompt, return_tensors='pt').to(self.device)
        outputs = self.model.generate(inputs.input_ids)
        return outputs
    def format_output(self, outputs):
        tactics = []
        for i, seq in enumerate(outputs.sequences):
            tactics.append(self.tokenizer.decode(seq, skip_special_tokens=True))
        return tactics
    def generate_tactics(self, current, current_code):
        prompt = self.format_prompt(current)
        raw_output = self.generate(prompt)
        tactics = self.format_output(raw_output)

        return tactics

class AStarSearchAgent():
    # model, server, heuristic
    def __init__(self, model, server, heuristic=None):
        self.model = model 
        self.server = server 
        self.server = heuristic if heuristic else self.default_heuristic # is this a typo?
    def default_heuristic(self, current, neighbor):
        return 1.0
    def get_successors(self, current, current_code):
        tactics = self.model.generate_tactics(current, current_code)
        compiled_actions = []
        successors = []
        for tactic in tactics:
            next_state, success = current.apply_tactic(self, tactic)
            if success:
                compiled_actions.append(tactic)
                successors.append(next_state)
                
        return compiled_actions, successors


    def search(self, initial_sketch, max_steps, verbose):
        unit = self.server.load_sorry(initial_sketch + "\nsorry")
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

        #TODO: implement AStarSearch here.
        
        ### Right now this is technically best-first search - should change to A* ###
        heuristic = default_heuristic
        steps = 0
        
        p_queue = []
        heapq.heapify(priority_queue)
        
        # sorts by heuristic output
        heapq.heappush(p_queue, (heuristic(initial_state), heuristic))


        while len(p_queue) > 0 and steps < max_steps:
            if verbose:
                # TODO: print the queue, possibly just one node
                pass
            
            successors = self.get_successors() # TODO: what is current and current_code?
        
            # Outline:
            
            # reference src/search.py, and the AStarSearch built there
            # - check if successors solve all goals
            # - if not, add successors to p_queue
            # repeat

            # return NPS with full proof if solved
        
        return [], False, 0, "not implemented yet"
        # return tactics=List[str], success=bool, step=int, message=str
    
if __name__ == '__main__':
    model = DojoModel()
    server = Server(project_path="./", imports=['Mathlib.Data.Real.Sqrt', 'Mathlib.Data.Real.Basic'])
    lean_sketch = """theorem mathd_algebra_17
  (a : ℝ)
  (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
  a = 8 := by"""
    search_agent = AStarSearchAgent(model, server)
    tactics, solved, steps, feedback = search_agent.search(initial_sketch=lean_sketch, max_steps=5, verbose=True)
    if solved:
        print(f"Proof found in {steps} steps!")
        print("\n".join(tactics))
    else:
        print(f"No proof found: {feedback}")
