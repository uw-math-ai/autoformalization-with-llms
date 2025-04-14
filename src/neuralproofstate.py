import re

# Contains information about the current proof state, including the unsolved goals and previously used tactics
# This is the goal_tactic version

class NeuralProofState():
    
    # TODO add server imports for definitions of real numbers, etc
    def __init__(self, state=None, thm_statement=None, prev_tactics=None, 
                 informal_info=None, server=None, neg_log_prob=None, parent=None):   

        self.informal_info = informal_info
        self.server = server
        
        if thm_statement:  
            try:
                self.state = self.server.load_sorry(thm_statement + f"\nsorry")[0].goal_state
            except Exception as e:
                try:
                    self.state = self.server.goal_start(thm_statement)
                except Exception as e2:
                    try:
                        goal = self.make_valid_goal(thm_statement)
                        self.state = self.server.goal_start(goal)
                    except Exception as e3:
                        print("Couldn't turn the theorem into a valid goal state!")
                        print(f"errors: {e, e2, e3}")
                        
            # print(f"\n")
            # print(f"creating new nps, state is:\n{self.state}")
            # print(f"\n")
                
            self.prev_tactics = []
            self.neg_log_prob = 0
            self.parent = None
        else:
            self.state = state
            self.prev_tactics = prev_tactics
            self.neg_log_prob = neg_log_prob
            self.parent = parent
        
        self.tactics_to_child_states = {}
    
    # Turns a theorem statement into a valid goal
    # TODO make this work reliably for statements with multiple hypothesis
    def make_valid_goal(self, thm_statement):
        string_groups = re.match(r"\((.*?)\)\s*:\s*(.*)",thm_statement)
        if string_groups:
            context = string_groups.group(1)
            statement = string_groups.group(2)
            goal = f"forall ({context}), {statement}"
            return goal
        else:
            raise Exception("theorem statement is in an invalid format!")
    
    # TODO currently have to specify a goal to apply a tactic, which isn't ideal. Would like to just check all goals
    # TODO add log probability as a parameter
    def apply_tactic(self, tactic, goal_id=0):
        # print(f"tactic: {tactic}")
        new_state = self.server.goal_tactic(self.state, goal_id=goal_id, tactic=tactic)
        
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
        
    def get_proof(self):
        return f"\n".join(self.prev_tactics)
        