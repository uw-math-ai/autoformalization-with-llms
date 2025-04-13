from abc import abstractmethod
from pantograph.server import Server
import re

from predictnextstep import predict_next_step
import heapq
import random

# Use only one of these below!

from neuralproofstate_two import NeuralProofState # load_sorry version
# from neuralproofstate import NeuralProofState # goal_tactic version - has some bugs right now

class Model():
    @abstractmethod
    def generate_tactics(self, nps):
        tactics = predict_next_step(nps)
        return tactics

class AStarSearchAgent():
    # model, server, heuristic
    def __init__(self, model, server, heuristic=None):
        self.model = model 
        self.server = server 
        self.heuristic = heuristic if heuristic else self.default_heuristic
    def default_heuristic(self, current, neighbor=None):
        return random.uniform(0,1)
    def get_successors(self, nps):
        tactics = self.model.generate_tactics(nps)
        successors = []
        for tactic in tactics: 
            try:
                tactic = tactic['tactic'] # for some reason the tactics are a dictionary, something in predictnextstep.py needs fixing
                print(f"tactic:{tactic}")
                child = nps.apply_tactic(tactic)
                successors.append(child)
            except Exception as e:
                print(f"get successor error: {e}")
                
        return successors

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
        
        ### Right now this is technically best-first search - should change to A* ###
        
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
                    return successor
                else:
                    heapq.heappush(p_queue, (self.heuristic(successor), successor))
            
            steps += 1  
    
if __name__ == '__main__':
    model = Model()
    server = Server(project_path="./", imports=['Mathlib.Data.Real.Sqrt', 'Mathlib.Data.Real.Basic'])
    lean_sketch = """theorem my_thm (x y : ℝ) : x * y = 0 → x = 0 ∨ y = 0 := by"""
    
    search_agent = AStarSearchAgent(model, server)
    nps = search_agent.search(initial_sketch=lean_sketch, max_steps=3, verbose=True)
    
    if nps is not None:
        print(f"Proof found!")
        nps.verbose_string()
        print(f"proof:\n")
        print(nps.thm_statement)
    else:
        print(f"No proof found")
