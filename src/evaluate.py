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
import traceback
import datetime

miniF2F_path = "data/test/minif2f-text-version.txt"
import_path = "data/test/minif2f-imports.txt"
theorems = load_theorems(miniF2F_path) # string versions of every theorem in minif2f
imports = load_imports(import_path) # string of all the things minif2f imports. DO NOT add extra newlines in imports doc, server may crash

server = Server(project_path="./", imports=imports)

search_params = {
    "max_steps": 5,
    "heuristic": None,
    "retries": 2,
}

model_params = {
    "model": "gpt-4o",
    "max_tokens": 100,
    "temperature": 0.4,
    "top_p": 1,
    "n": 2,
}

num_theorems = 100
theorems = theorems[:num_theorems]

model = LLMModel(**model_params)
search_agent = AStarSearchAgent(model, server, heuristic=search_params['heuristic'])

filename = f"{model_params['model']} temp {model_params['temperature']}"
output_path = f"data/results/solved/{filename}.txt"
solved_count = 0

theorem_results = []

error_messages = []

for i, theorem in enumerate(tqdm(theorems, desc="Solving theorems")):
    error_msg = None
    try:
        if i % 2 == 0:
            server = Server(project_path="./", imports=imports)
            search_agent = AStarSearchAgent(model, server, heuristic=search_params['heuristic'])
        
        final_nps = search_agent.search(initial_sketch=theorem, 
                                        max_steps=search_params['max_steps'], 
                                        verbose=True, 
                                        k_tries=search_params['retries'])
        if final_nps is not None:
            print(final_nps)
            proof_text = final_nps.get_proof()
            print(f"proof text:\n{proof_text}")
            theorem_results.append((theorem, proof_text, None))
            solved_count += 1
            print(f"Solved theorem {solved_count}/{len(theorems)}")
        else:
            print("Unsolved")
            theorem_results.append((theorem, None, None))
    except Exception as e:
        print(f"Error while processing a theorem: {e}")
        traceback.print_exc()
        error_msg = str(e)
        theorem_results.append((theorem, None, error_msg))

# Write results to file
timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
os.makedirs(os.path.dirname(output_path), exist_ok=True)
with open(output_path, "w", encoding="utf-8") as out_file:
    out_file.write("=== Experiment Metadata ===\n")
    out_file.write(f"Timestamp: {timestamp}\n")
    out_file.write(f"Model params: {model_params}\n")
    out_file.write(f"Search params: {search_params}\n")
    out_file.write(f"Theorems attempted: {len(theorems)}\n")
    out_file.write(f"Theorems proven: {solved_count}\n")
    out_file.write("==========================\n\n")

    for theorem, proof_text, error_msg in theorem_results:
        out_file.write(f"\n{theorem}\n")
        if proof_text:
            out_file.write(f"{proof_text}\n\n")
        elif error_msg:
            out_file.write(f"UNSOLVED (Error: {error_msg})\n\n")
        else:
            out_file.write("UNSOLVED\n\n")

# Final summary
print(f"\nFinished. Solved {solved_count} out of {len(theorems)} theorems.")
print(f"Saved solved theorems to {output_path}")

# TODO: compute statistics and save them to the csv as well. For example, average number of steps taken, most frequent tactics used, etc.

# Save summary to CSV
csv_output_path = "data/results/summary.csv"
row = {}
row.update(model_params)
row.update(search_params)
row["solved"] = solved_count
row["attempted"] = num_theorems
row["timestamp"] = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())

# Ensure the directory exists
os.makedirs(os.path.dirname(csv_output_path), exist_ok=True)

# Read existing fieldnames if file exists, else use current keys
if os.path.exists(csv_output_path):
    with open(csv_output_path, "r", newline="", encoding="utf-8") as csvfile:
        reader = csv.DictReader(csvfile)
        existing_fieldnames = reader.fieldnames if reader.fieldnames else []
else:
    existing_fieldnames = []

# Merge existing fieldnames with new keys
fieldnames = list(existing_fieldnames or [])
for key in row.keys():
    if key not in fieldnames:
        fieldnames.append(key)

write_header = not os.path.exists(csv_output_path) or set(fieldnames) != set(existing_fieldnames or [])

# Read all existing rows if we need to update columns
rows = []
if os.path.exists(csv_output_path) and write_header and existing_fieldnames:
    with open(csv_output_path, "r", newline="", encoding="utf-8") as csvfile:
        reader = csv.DictReader(csvfile)
        for r in reader:
            rows.append(r)

# Add the new row
rows.append(row)

# Write all rows with updated columns
with open(csv_output_path, "w", newline="", encoding="utf-8") as csvfile:
    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
    writer.writeheader()
    for r in rows:
        writer.writerow({k: r.get(k, "") for k in fieldnames})