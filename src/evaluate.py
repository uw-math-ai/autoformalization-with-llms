
import csv
import os
import time
from tqdm import tqdm

from pantograph.server import Server
from utils import load_theorems, load_imports
from revised_search import AStarSearchAgent
from LLMModel import LLMModel

from neuralproofstate import NeuralProofState

from heuristics import goal_based

miniF2F_path = "data/test/minif2f-text-version.txt"
import_path = "data/test/minif2f-imports.txt"
theorems = load_theorems(miniF2F_path) # string versions of every theorem in minif2f
imports = load_imports(import_path) # string of all the things minif2f imports, plus a few more

server = Server(project_path="./", imports=imports) # server seems to like crashing, can't handle the imports ?
model = LLMModel()
search_agent = AStarSearchAgent(model, server)

output_path = "data/results/solved_theorems.txt"
solved_count = 0

with open(output_path, "w", encoding="utf-8") as out_file:
    for i, theorem in enumerate(tqdm(theorems, desc="Solving theorems")):
        try:
            if i % 2 == 0:
                server = Server(project_path="./", imports=imports)
                search_agent = AStarSearchAgent(model, server, heuristic=None)

            final_nps = search_agent.search(initial_sketch=theorem, max_steps=3, verbose=True)
            if final_nps is not None:
                proof_text = final_nps.get_proof()
                print(f"proof text:\n{proof_text}")
                out_file.write(f"\n{theorem}\n{proof_text}\n\n")
                solved_count += 1
                print(f"Solved theorem {solved_count}/{len(theorems)}")
            else:
                print("Unsolved")
        except Exception as e:
            print(f"Error while processing a theorem: {e}") # TODO print stacktrace

# Final summary
print(f"\nFinished. Solved {solved_count} out of {len(theorems)} theorems.")
print(f"Saved results to '{output_path}'")

