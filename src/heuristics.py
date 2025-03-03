from neuralproofstate import NeuralProofState
from pantograph.server import Server

import numpy as np
import torch
import torch.nn.functional as F
from transformers import AutoTokenizer, AutoModel

# some experimental heuristics for ordering fringe nodes
# search algo wants to minimize a given heuristic
# TODO: test each of these on nanoF2F and see how each heuristic fares
# TODO add case for a state having no goals

def separate_goals_and_hyps(state):
    # Split the input state by newlines
    lines = state.split('\n')
    
    goals = []
    hyps = []
    
    for line in lines:
        if '⊢' in line:
            goals.append(line.strip())
        else:
            hyps.append(line.strip())
    
    return hyps, goals

# TODO: Add modes - maybe max cosine similarity is best metric, maybe average is better?
def goal_hypothesis_comparison(neural_proof_state, print_info=False):
    '''
    Gets the vector embeddings for the goals & hypothesis from an embedding model,
    then compares the cosine similarities of the goals & hypotheses
    '''
    # TODO get a list of unproved goals and a list of unproved hypotheses
    hyps, goals = separate_goals_and_hyps(str(neural_proof_state.state))
    
    model_path = "ibm-granite/granite-embedding-278m-multilingual"
    
    if len(goals) == 0 or len(hyps) == 0:
        return 0

    # Load the model and tokenizer
    model = AutoModel.from_pretrained(model_path)
    tokenizer = AutoTokenizer.from_pretrained(model_path)
    model.eval()
    
    tokenized_goals = tokenizer(goals, padding=True, truncation=True, return_tensors='pt')
    tokenized_hyps = tokenizer(hyps, padding=True, truncation=True, return_tensors='pt')
    
    # encode queries
    with torch.no_grad():
        goals_output = model(**tokenized_goals)
        hyps_output = model(**tokenized_hyps)

        # Perform pooling. granite-embedding-278m-multilingual uses CLS Pooling
        goal_embeddings = goals_output[0][:, 0]
        hyp_embeddings = hyps_output[0][:, 0]

    goal_embeddings = torch.nn.functional.normalize(goal_embeddings, dim=1)
    hyp_embeddings = torch.nn.functional.normalize(hyp_embeddings, dim=1)
    
    similarity_matrix = goal_embeddings @ hyp_embeddings.T
    if print_info:
        print("goals & hyps:", goals, hyps)
        print("cosine similarity scores:", similarity_matrix)
        print("max similarity:",np.max(np.ravel(similarity_matrix)))
        print("min similarity:", np.min(np.ravel(similarity_matrix)))
        print("mean similarity:", np.mean(np.ravel(similarity_matrix)))

    # TODO: Find a better monotonic function on [-1,1] (possibly [0,1])
    return (1 - np.max(np.ravel(similarity_matrix))) / 2
    
def compare_with_mathlib(neural_proof_state):
    pass

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

def log_probability(neural_proof_state):
    return curr.neg_log_prob

# Uses tower rule to compute the given node's probability 
# given the (conditional) probabilities of all the previous nodes
def adjusted_log_probability(neural_proof_state):
    '''
    Uses tower rule to compute the given node's probability, given
    the (conditional) probabilities of all the previous nodes
    '''
    curr = neural_proof_state
    adjusted = 0
    while curr is not None:
        adjusted += curr.neg_log_prob
        curr = curr.parent
    return adjusted

# TODO move this to tests folder
if __name__ == "__main__":
    server = Server(project_path="./")
    root = NeuralProofState(thm_statement="(p q : Prop) : ¬(p → q) ↔ p ∧ ¬q", server=server)
    root = root.apply_tactic("intro p q")
    print(root.state)
    print("number of goals:", goal_based(root))
    print("number of hypothesis:", hypothesis_based(root))
    print("vec comparison:", goal_hypothesis_comparison(root))