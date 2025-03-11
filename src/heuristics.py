from neuralproofstate import NeuralProofState
from pantograph.server import Server

import numpy as np
from functools import cache
import os
from openai import OpenAI
import dotenv

dotenv.load_dotenv()
os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")

# some experimental heuristics for ordering fringe nodes
# search algo wants to minimize a given heuristic
# TODO: test each of these on nanoF2F and see how each heuristic fares
# TODO add case for a state having no goals

def separate_goals_and_hyps(state_string):
    # Split the input state by newlines
    lines = state_string.split('\n')
    
    goals = []
    hyps = []
    
    for line in lines:
        if '⊢' in line:
            goals.append(line.strip())
        else:
            hyps.append(line.strip())
            
    print("hyps vector:"," ".join(hyps))
    print("goals vector:", " ".join(goals))
    
    return " ".join(hyps), " ".join(goals)

# TODO: Add modes - maybe max cosine similarity is best metric, maybe average is better?
@cache
def goal_hypothesis_comparison(proof_state, proof_string=None, print_info=False):
    '''
    Gets the vector embeddings for the goals & hypothesis from an embedding model,
    then compares the cosine similarities of the goals & hypotheses
    '''
    
    client = OpenAI()
    
    '''if neural_proof_state is not None:
        hyps, goals = separate_goals_and_hyps(str(neural_proof_state.state))
    else:
        hyps, goals = separate_goals_and_hyps(proof_string)'''
    
    if proof_state is not None:
        proof_string = str(proof_state.state)
    else:
        return 0
    hyps, goals = separate_goals_and_hyps(proof_string)
        
    if len(goals) == 0 or len(hyps) == 0:
        return 0

    response1 = client.embeddings.create(
        input=goals,
        model="text-embedding-3-small"
    )
    
    goal_embeddings = np.array(response1.data[0].embedding)
    
    response2 = client.embeddings.create(
        input=hyps,
        model="text-embedding-3-small"
    )
    
    hyp_embeddings = np.array(response2.data[0].embedding)
    
    # similarity_matrix = goal_embeddings @ hyp_embeddings.T
    
    if print_info:
        '''print("goals & hyps:", goals, hyps)
        print("cosine similarity scores:", similarity_matrix)
        print("max similarity:",np.max(np.ravel(similarity_matrix)))
        print("min similarity:", np.min(np.ravel(similarity_matrix)))
        print("mean similarity:", np.mean(np.ravel(similarity_matrix)))'''
        print("max similarity:", np.inner(goal_embeddings, hyp_embeddings))

    # return -1 * np.log(np.max(np.ravel(similarity_matrix))) # Assuming nonneg cosine similarity
    
    normalized = 0.5 * (np.inner(goal_embeddings, hyp_embeddings) + 1) # make nonneg
    
    if np.inner(goal_embeddings, hyp_embeddings) < 0:
        raise Exception("negative!")
    return -1 * np.log(normalized)
    
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
    print(root.state, "\n")
    # print("number of goals:", goal_based(root))
    # print("number of hypothesis:", hypothesis_based(root))
    print("vec comparison:", goal_hypothesis_comparison(root))