"""
TODO: 
Store results in csv
Make a function
Incorporate the parameters: max_depth, temp, model, num_tactics(branching factor), heuristic
"""
import sys
sys.path.append("./src") # path to search.py 

from search import DojoModel, PantographEnvironment, AStarSearchAgent, AStarSearchState

from pantograph import Server
import requests

request = requests.get("https://raw.githubusercontent.com/yangky11/miniF2F-lean4/refs/heads/main/MiniF2F/Minif2fImport.lean")

imports = request.text.split("\n")
for i, module in enumerate(imports):
    imports[i] = module.replace("import ", "")
server = Server(project_path="./", imports=imports) # build the minif2f-imports file

request = requests.get("https://raw.githubusercontent.com/yangky11/miniF2F-lean4/refs/heads/main/MiniF2F/Valid.lean")
validation = request.text.split("\n\n")
validation = validation[3:]


model = DojoModel()
env = PantographEnvironment(server)
for sketch in validation:
    unit, = server.load_sorry(sketch)
    goal_state = unit.goal_state
    print(f"Initial state: {goal_state}")
    initial_state = AStarSearchState(
        goal_state=goal_state
    )
    search_agent = AStarSearchAgent(model, env)
    actions, solved, _, _ = search_agent.search(initial_state, max_steps=20, verbose=True)
    if solved:
        print("Proof found!")
        for action in actions:
            print(action.to_code())
    else:
        print("No proof found.")
