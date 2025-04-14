from typing import List
import re
import os

from pantograph.server import Server
from pantograph.expr import GoalState

# For making a list of theorem statements from minif2f or another source
def load_theorems(txt_path):
    with open(txt_path, 'r', encoding='utf-8') as file:
        lines = file.readlines()
    
    theorem_pattern = re.compile(r'^theorem\s+(\w+)')
    theorems = []
    collecting = False
    current_lines = []

    for line in lines:
        stripped = line.strip()

        if collecting:
            if stripped.endswith('sorry'):
                cleaned_line = stripped[:-len('sorry')].rstrip()
                current_lines.append(cleaned_line)
                flat_text = " ".join(current_lines).strip()
                theorems.append(flat_text)
                collecting = False
                current_lines = []
            else:
                current_lines.append(stripped)
        else:
            if theorem_pattern.match(stripped):
                collecting = True
                current_lines = [stripped]

    return theorems

# For getting a big list of imports
def load_imports(txt_path):
    imports = []
    with open(txt_path, 'r', encoding='utf-8') as file:
        for line in file:
            line = line.strip()
            if line.startswith('import '):
                imports.append(line[len('import '):].strip())
    return imports

def load_imports_list(lean_path) -> List[str]:
    """
    Load the imports list from a Lean file.
    """
    with open(lean_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    imports = []
    for line in lines:
        if line.startswith("import"):
            statement = line.split("import")[1].strip()
            if not statement:
                continue
            if not statement.startswith("Mathlib"):
                statement = "Mathlib." + statement
            imports.append(statement)
    return imports

def load_goals(lean_path) -> List[str]:
    """
    Load the goals from a Lean file.
    """
    with open(lean_path, 'r', encoding='utf-8') as file:
        lines = file.readlines()
    
    theorem_pattern = re.compile(r'^theorem\s+(\w+)')
    theorems = {}
    current_theorem = None
    current_lines = []
    
    for line in lines:
        if theorem_pattern.match(line):
            if current_theorem:
                theorems[current_theorem] = "\n".join(current_lines).strip()
            current_theorem = theorem_pattern.match(line).group(1)
            current_lines = [line.rstrip()]
        elif current_theorem:
            current_lines.append(line.rstrip())
    
    if current_theorem:
        theorems[current_theorem] = "\n".join(current_lines).strip()
    
    return theorems

def create_minif2f_server(project_path, import_path) -> Server:
    """
    Create a Pantograph server with the project path and imports for the MiniF2F project.
    """
    imports = load_imports_list(import_path)
    server = Server(project_path=project_path, imports=imports)
    return server

def create_goal_state(server: Server, goal: str) -> GoalState:
    """
    Create a goal state for the given goal string.
    """
    unit, = server.load_sorry(goal)
    state = unit.goal_state
    return state

def split_data(lean_path, output_dir="./", num_fold=10):
    """
    Split the goals into small folds and store them in seperate files.
    """
    goals = load_goals(lean_path)
    num_fold = 10

    keys = list(goals.keys())
    num_goals = len(keys)
    fold_size = num_goals // num_fold
    folds = []
    for i in range(num_fold):
        start = i * fold_size
        end = (i + 1) * fold_size if i != num_fold - 1 else num_goals
        fold = {keys[j]: goals[keys[j]] for j in range(start, end)}
        folds.append(fold)

    for i, fold in enumerate(folds):
        output_path = os.path.join(output_dir, f"fold_{i}.lean")
        with open(output_path, "w") as f:
            for _, value in fold.items():
                f.write(f"{value}\n\n")


if __name__ == "__main__":
    """
    Reminder: Please first clone the miniF2F-lean4 repository and follow
    the instructions in its README to set up the Lean environment:
        https://github.com/yangky11/miniF2F-lean4
    """
    # Example usage
    # miniF2F_path = "./miniF2F-lean4"
    # import_path = os.path.join(miniF2F_path, "MiniF2F/Minif2fImport.lean")
    # lean_path = os.path.join(miniF2F_path, "MiniF2F/Valid.lean")
    # theorems = load_goals(lean_path)
    # server = create_minif2f_server(miniF2F_path, import_path)
    # goal = theorems['amc12a_2019_p21']
    # print(goal)
    # goal_state = create_goal_state(server, goal)
    # print(goal_state)
    lean_path = "./miniF2F-lean4/MiniF2F/Test.lean"
    output_dir = "./data/test"
    split_data(lean_path, output_dir=output_dir)
