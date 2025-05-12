import re

# Contains information about the current proof state, including the unsolved goals and previously used tactics
# This is the goal_tactic version

class NeuralProofState():
    
    def __init__(self, state=None, thm_statement=None, prev_tactics=None,
                 informal_info=None, server=None, neg_log_prob=None, parent=None,
                 failed_tactics=None):

        self.informal_info = informal_info
        self.server = server
        
        if thm_statement:  
            try:
                self.state = self.server.load_sorry(thm_statement + f"\nsorry")[0].goal_state
            except Exception as e:
                try:
                    self.state = self.server.goal_start(thm_statement)
                except Exception as e2:
                    print("Couldn't turn the theorem into a valid goal state!")
                    print(f"errors: {e, e2}")
                        
            # print(f"\n")
            # print(f"creating new nps, state is:\n{self.state}")
            # print(f"\n")
                
            self.prev_tactics = []
            self.neg_log_prob = 0
            self.parent = None
            self.failed_tactics = []
        else:
            self.state = state
            self.prev_tactics = prev_tactics
            self.neg_log_prob = neg_log_prob
            self.parent = parent
            self.failed_tactics = failed_tactics
        
        self.tactics_to_child_states = {}
    
    def apply_tactic(self, tactic, goal_id=0):
        print(f"tactic: {tactic}, prev failures: {self.failed_tactics}")
        try:
            new_state = self.server.goal_tactic(self.state, goal_id=goal_id, tactic=tactic)
            child_node = NeuralProofState(state=new_state, prev_tactics=self.prev_tactics + [tactic], 
                                        informal_info=self.informal_info, server=self.server, parent=self, 
                                        failed_tactics=self.failed_tactics)
            self.tactics_to_child_states[tactic] = child_node
            
            return child_node
        except:
            return None
                    
    
    def add_failed_tactic(self, tactic):
        self.failed_tactics.append(tactic)
    
    def to_prompt(self):
        prompt = f"""Given the Lean 4 code: \n{self.state}\n Provide the next tactic 
    to progress towards proving the theorem. The previous tactics used to prove this theorem are as follows: \n{self.prev_tactics}\n"""
        
        if self.informal_info:
            prompt += f"""You should also consider the following information when choosing a tactic: \n{self.informal_info}\n"""
            
        if self.failed_tactics:
            prompt += f"""Note that you have previously tried the following tactics: \n{self.failed_tactics}\n
            They did not compile, either because of a syntax error, or because your code simply didn't make sense.
            Do not generate the exact same thing as a previously failed tactic.\n"""
        
        prompt += f"""Give only the next Lean tactic and no other information in your response.
        Do not include 'by' at the start of your response, as it is already included in the theorem header.
        Do not put any quotation or tick marks around your answer. Do not give Lean 3 syntax. Do not use the sorry tactic.
        Do not include the goal symbol in your response."""
        
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
        return f"\n".join(self.prev_tactics)
        