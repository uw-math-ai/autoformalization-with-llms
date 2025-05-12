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


class AStarSearchAgent():
    # model, server, heuristic
    def __init__(self, model, server, heuristic=None):
        self.model = model 
        self.server = server 
        self.heuristic = heuristic if heuristic else self.default_heuristic
        
    def default_heuristic(self, current, neighbor=None):
        return random.uniform(0,1)
    
    def get_successors(self, nps, k_tries):
        successors = []

        for i in range(k_tries):
            tactics = self.model.generate_tactics(nps)
            print("generate_tactics returned:", tactics)
            failures = 0
            for tactic in tactics: 
                try:
                    child = nps.apply_tactic(tactic)
                    if child is not None:
                        successors.append(child)
                    else:
                        print(f"adding a failed tactic: {tactic}")
                        nps.add_failed_tactic(tactic) # TODO: this is never called because NPS currently doesn't handle errors correctly
                        failures += 1
                except Exception as e:
                    print(f"get successor error: {e}")
            if failures == 0:
                break
                
        return successors

    def search(self, initial_sketch, max_steps, verbose, k_tries=2,):
        
        unit = self.server.load_sorry(initial_sketch + f"\nsorry")
        goal_state = unit[0].goal_state
        print(f"starting search on a theorem, goal state: {goal_state}")
        error_messages = [s for s in unit[0].messages if "error" in s]
        if goal_state is None: 
            raise Exception("No goals - this may be because there weren't enough imports, or possibly something else")
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
            successors = self.get_successors(nps, k_tries)
            
            for successor in successors:
                goal_state = successor.state
                if goal_state is None or goal_state.__str__() is None or len(goal_state.__str__()) == 0: # TODO: not sure which one of these is actually required
                    return successor
                else:
                    heapq.heappush(p_queue, (self.heuristic(successor) + len(successor.prev_tactics), successor))
            
            if len(p_queue) == 0:
                heapq.heappush(p_queue, (self.heuristic(nps) + len(nps.prev_tactics), nps))
            
            steps += 1  
            
        return None
    
'''if __name__ == '__main__':
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
        print(f"No proof found")'''
# Example if you want to try the LLMModel

if __name__ == "__main__":


    model = LLMModel()

    state = """theorem amc12_2000_p11 (a b : ℝ) (h₀ : a ≠ 0 ∧ b ≠ 0) (h₁ : a * b = a - b) :
    a / b + b / a - a * b = 2 := by"""
    nps = NeuralProofState(state=state)

    print(model.generate_tactics(nps))

