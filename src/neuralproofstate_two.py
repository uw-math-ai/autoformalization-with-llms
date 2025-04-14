
# Contains information about the current proof state, including the unsolved goals and previously used tactics
# This is the load_sorry version

class NeuralProofState():
    
    def __init__(self, state=None, thm_statement=None, prev_tactics=None, 
                 informal_info=None, server=None, neg_log_prob=None, parent=None):   
        
        self.informal_info = informal_info
        self.server = server
        self.thm_statement = thm_statement
        self.errors = False
        
        if state is None:
            unit, = self.server.load_sorry(thm_statement + f"\nsorry")
            self.state = unit.goal_state
            print(f"unit errors: {unit.messages}")
            if len(unit.messages) > 1: # check for errors caused by exact, rw, and similar
                self.errors = True
        else:
            self.state = state
            
        print(f"\n")
        print(f"creating new nps, state is:\n{self.state}")
        print(f"\n")
        
        if prev_tactics is None:
            self.prev_tactics = []
        else:
            self.prev_tactics = prev_tactics
            
        self.neg_log_prob = neg_log_prob
        self.parent = parent
        self.tactics_to_child_states = {}
    
    # Returns the new NPS after applying the tactic, or None if the tactic is invalid
    def apply_tactic(self, tactic, goal_id=0):
        child_node = NeuralProofState(thm_statement="\n".join([self.thm_statement] + [tactic]), 
                                      prev_tactics=self.prev_tactics + [tactic], 
                                      informal_info=self.informal_info,
                                      server=self.server, parent=self)
        if not child_node.errors:
            self.tactics_to_child_states[tactic] = child_node
            return child_node
        
        print(f"error, illegal tactic:{tactic}")
        return None

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
        
    def get_proof(self):
        return self.thm_statement