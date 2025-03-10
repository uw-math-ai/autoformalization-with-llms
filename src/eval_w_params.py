from search import DojoModel, PantographEnvironment, AStarSearchAgent, AStarSearchState

from pantograph import Server
import requests
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
def get_imports_val(imports_url = "https://raw.githubusercontent.com/yangky11/miniF2F-lean4/refs/heads/main/MiniF2F/Minif2fImport.lean",
                    validation_url = "https://raw.githubusercontent.com/yangky11/miniF2F-lean4/refs/heads/main/MiniF2F/Test.lean"):
    request = requests.get(imports_url)

    imports = request.text.split("\n")
    for i, module in enumerate(imports):
        imports[i] = module.replace("import ", "")
    server = Server(project_path="./", imports=imports) # build the minif2f-imports file

    request = requests.get(validation_url)
    validation = request.text.split("\n\n")
    validation = validation[3:27]
    return imports, validation

def evaluate_sketch(server, env, sketch, model, verbose, heuristic=None):
    try:
        # unit = server.load_sorry(sketch + " sorry")
        # goal_state = unit[0].goal_state
        # if goal_state is not None:
        #     initial_state = AStarSearchState(
        #         goal_state=goal_state,
        #         theorem = sketch
        #     )
        #     search_agent = AStarSearchAgent(model, env)
        # else:
        #     result = {
        #         "theorem": sketch,
        #         "steps": 0,
        #         "success": "False",
        #         "feedback": "No goals",
        #         "proof": "",
        #     }
        #     print(result)
        #     return result
        search_agent = AStarSearchAgent(model, env, heuristic) if heuristic else AStarSearchAgent(model, env)
        actions, solved, step, feedback = search_agent.search(sketch, max_steps=20, verbose=verbose)
        if solved:
            proof = "\n".join([action.to_code() for action in actions])
            result = {
                "theorem": sketch,
                "steps": step,
                "success": "True",
                "feedback": f"{feedback}",
                "proof": proof,
            }
            print(result)
        else:
            print(f"Managed to start searching but failed to prove")
            result = {
                "theorem": sketch,
                "steps": step,
                "success": "False",
                "feedback": f"{feedback}",
                "proof": "",
            }
            print(result)
        return result
    except Exception as e:
        result = {
            "theorem": sketch,
            "steps": 0,
            "success": "False",
            "feedback": f"{e}",
            "proof": "",
        }
        print(result)
        return result
def write_results(results):
    with open("results.csv", mode="w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=["theorem", "steps", "success", "feedback", "proof"])
        writer.writeheader()
        writer.writerows(results)
def evaluate(model=None, num_threads=4, verbose=False, heuristic=None):
    imports, validation = get_imports_val()
    server = Server(project_path="./", imports=imports) # build the minif2f-imports file
    if model is None:
        model = DojoModel()
    env = PantographEnvironment(server)
    results = []
    futures = []
    with ThreadPoolExecutor(max_workers=num_threads) as executor:
        for lean_code in validation:
            sketch = lean_code.split("sorry")[0]
            future = executor.submit(evaluate_sketch, server, env, sketch, model, verbose, heuristic)
            futures.append(future)
        
        for future in as_completed(futures):
            result = future.result()
            if result is not None:
                results.append(result)
    write_results(results)

if __name__ == "__main__":
    evaluate(num_threads=16)
