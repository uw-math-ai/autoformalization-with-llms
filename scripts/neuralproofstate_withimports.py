import sys
sys.path.append("./src")


from neuralproofstate import NeuralProofState
from pantograph.server import Server


class NeuralProofState_withImports(NeuralProofState):

    def __init__(self, state=None, thm_statement=None, new_proof=False, 
                prev_tactics=None, informal_info=None, server=None, imports=None,
                neg_log_prob=None, parent=None):   
        
        if imports != None:
            self.server = Server(imports=imports, project_path="./")
            self.informal_info = informal_info
                        
            if new_proof:
                self.server = Server(project_path="./", imports=imports)
                try:
                    self.state = self.server.goal_start(thm_statement)
                except Exception as e:
                    goal = self.make_valid_goal(thm_statement)
                    self.state = self.server.goal_start(goal)
                self.prev_tactics = []
                self.neg_log_prob = 0
                self.parent = None
            else:
                self.server = server
                self.state = state
                self.prev_tactics = prev_tactics
                self.neg_log_prob = neg_log_prob
                self.parent = parent
            self.tactics_to_child_states = {}
        else:
            super().__init__(state, thm_statement, new_proof, prev_tactics, informal_info, server,
                       neg_log_prob, parent)
            
    def apply_tactic(self, tactic, goal_id=0):
        try:
            new_state = self.server.goal_tactic(self.state, goal_id=goal_id, tactic=tactic)
            
            child_node = NeuralProofState(state=new_state, prev_tactics=self.prev_tactics + [tactic], 
                                        informal_info=self.informal_info, server=self.server, parent=self)
            
            self.tactics_to_child_states[tactic] = child_node
            return child_node
        except Exception as e:
            print("Error")
            return e    
        
if __name__ == "__main__":  
    
    '''root = NeuralProofState(thm_statement="(p q : Prop) : ¬(p → q) ↔ p ∧ ¬q", new_proof=True)
    print(root,"\n")'''
      
    next = NeuralProofState_withImports(thm_statement="forall (x y : ℝ) , x * y = 0 → x = 0 ∨ y = 0", new_proof=True, imports=["Mathlib.Data.Nat.Factorization.Basic", "Mathlib.Data.Nat.Prime.Basic", "Mathlib.Data.Real.Basic"])
    tactics = ["intro x y", "contrapose","rw [not_or]","intro ⟨hx, hy⟩","exact mul_ne_zero hx hy]"]
    print(next,"\n")
    
    for tactic in tactics: 
        next = next.apply_tactic(tactic=tactic)
        print(next, "\n")
