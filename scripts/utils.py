from typing import List
import re
import os

from pantograph.server import Server
from pantograph.expr import GoalState

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


if __name__ == "__main__":
    """
    Reminder: Please first clone the miniF2F-lean4 repository and follow
    the instructions in its README to set up the Lean environment:
        https://github.com/yangky11/miniF2F-lean4
    """
    # Example usage
    miniF2F_path = "./miniF2F-lean4"
    import_path = os.path.join(miniF2F_path, "MiniF2F/Minif2fImport.lean")
    lean_path = os.path.join(miniF2F_path, "MiniF2F/Valid.lean")
    theorems = load_goals(lean_path)
    server = create_minif2f_server(miniF2F_path, import_path)
    goal = theorems['amc12a_2019_p21']
    goal_state = create_goal_state(server, goal)
    print(goal_state)
