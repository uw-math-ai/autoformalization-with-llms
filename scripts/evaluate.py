
import csv
import os
import time
from tqdm import tqdm

from search import AStarSearchAgent, DojoModel, PantographEnvironment, AStarSearchState
from utils import create_goal_state, create_minif2f_server, load_goals

max_steps = 20

miniF2F_path = "./miniF2F-lean4"
import_path = "./miniF2F-lean4/MiniF2F/Minif2fImport.lean"
lean_path = "./data/test/fold_6.lean"
filename = os.path.basename(lean_path).rsplit(".lean")[0]
csv_filename = f"./data/results/{filename}_results_{max_steps}.csv"
columns = ["theorem", "steps", "time", "success", "feedback", "proof"]

server = create_minif2f_server(project_path=miniF2F_path, import_path=import_path)
env = PantographEnvironment(server)
model = DojoModel()
search_agent = AStarSearchAgent(model, env)
goals = load_goals(lean_path)
print(f"Number of theorems to prove: {len(goals)}")
results = []

for name, goal in tqdm(goals.items()):
    start_time = time.time()
    try:
        sketch = goal.rsplit("sorry")[0].strip("\n ")
        actions, solved, step, feedback = search_agent.search(sketch, max_steps=max_steps, verbose=False)
        end_time = time.time()
        if solved:
            proof = "\n".join([action.to_code() for action in actions])
            result = {
                "theorem": name,
                "steps": step,
                "time": f"{(end_time - start_time):.2f}",
                "success": "True",
                "feedback": f"{feedback}",
                "proof": proof,
            }
        else:
            result = {
                "theorem": name,
                "steps": step,
                "time": f"{(end_time - start_time):.2f}",
                "success": "False",
                "feedback": f"{feedback}",
                "proof": "",
            }
        print(result)
        results.append(result)
    except Exception as e:
        end_time = time.time()
        result = {
            "theorem": name,
            "steps": 0,
            "time": f"{(end_time - start_time):.2f}",
            "success": "False",
            "feedback": f"Failed to search: {e}",
            "proof": "",
        }
        results.append(result)

with open(csv_filename, mode="w", newline="") as file:
    writer = csv.DictWriter(file, fieldnames=columns)
    writer.writeheader()
    writer.writerows(results)

print(f"Results successfully saved to {csv_filename}")
