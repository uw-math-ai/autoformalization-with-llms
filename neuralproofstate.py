from pantograph.server import Server

# Contains information about the current proof state, including the unsolved goals and previously used tactics

class NeuralProofState():
    def __init__(self, state, original_state=None, prev_tactics=None, informal_info=None, server=None, new_proof=False):   
   
        self.informal_info = informal_info
                    
        if new_proof:
            self.server = Server(project_path="./")
            self.state = self.server.goal_start(state)
            self.prev_tactics = []
            self.original_state = state
        else:
            self.server = server
            self.state = state
            self.prev_tactics = prev_tactics
            self.original_state = original_state
        
        self.tactics_to_child_states = {}
        
    # TODO currently have to specify a goal to apply a tactic, which isn't ideal. Would like to just check all goals
    def apply_tactic(self, tactic, goal_id=0):
        new_state = self.server.goal_tactic(self.state, goal_id=goal_id, tactic=tactic)
        
        child_node = NeuralProofState(new_state, original_state=self.original_state, 
            prev_tactics=self.prev_tactics + [tactic], informal_info=self.informal_info, server=self.server)
        
        self.tactics_to_child_states[tactic] = child_node
        return child_node

    def to_prompt(self):
        prompt = f"""Given the Lean 4 code: \n{self.state}\n Provide the next tactic to 
        close all goals and prove the theorem. The original goal for this theorem was: \n{self.original_state}\n 
        The previous tactics used to prove this theorem are as follows: \n{self.prev_tactics}\n"""
        
        if informal_info:
            prompt += f"""You should also consider the following information when choosing a tactic: \n{self.informal_info}\n"""
            
        prompt += f"""Give only the Lean tactic and no other information in your response. 
        Do not include 'by' at the start of your response, as it is already included in the theorem header."""
        
        return prompt
    
    def __str__(self):
        return self.state.__str__()
    
# Example proof tree
if __name__ == "__main__":  
      
    root = NeuralProofState("forall (p q: Prop), Or p q -> Or q p", new_proof=True)
    print(root,"\n")
    
    next = root.apply_tactic("intro p q h")
    print(next,"\n")
    
    next = next.apply_tactic("rcases h with hp | hq")
    print(next,"\n")
    
    next = next.apply_tactic("left", goal_id=1)
    print(next,"\n")

    next = next.apply_tactic("exact hq", goal_id=0)
    print(next, "\n")
    
    next = next.apply_tactic("right")
    print(next,"\n")
    
    next = next.apply_tactic("exact hp")
    print(next,"\n")
    