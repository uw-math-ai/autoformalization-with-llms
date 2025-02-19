from neuralproofstate import NeuralProofState

# some experimental heuristics for ordering fringe nodes
# search algo wants to minimize a given heuristic
# TODO: test each of these on nanoF2F and see how each heuristic fares

def goal_based(neural_proof_state):
    return str(neural_proof_state.state).count("⊢")

def hypothesis_based(neural_proof_state):
    optimal_hyp_num = 5
    hyp_num =  str(neural_proof_state).count("\n") - goal_based(neural_proof_state)
    return abs(optimal_hyp_num - hyp_num)

def prev_tactics_based(neural_proof_state):
    if neural_proof_state.prev_tactics is None:
        return 0
    else:
        return len(neural_proof_state.prev_tactics)

# TODO have not implemented this within API calls yet
def log_probability(neural_proof_state):
    return curr.neg_log_prob

# Uses tower rule to compute the given node's probability 
# given the (conditional) probabilities of all the previous nodes
def adjusted_log_probability(neural_proof_state):
    curr = neural_proof_state
    adjusted = 0
    while curr is not None:
        adjusted += curr.neg_log_prob
        curr = curr.parent
    return adjusted
    
if __name__ == "__main__":
    root = NeuralProofState(thm_statement="(p q : Prop) : ¬(p → q) ↔ p ∧ ¬q", new_proof=True)
    print(root.state)
    print("number of goals:", goal_based(root))
    print("number of hypothesis:", hypothesis_based(root))