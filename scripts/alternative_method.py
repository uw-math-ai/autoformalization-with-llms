import sys
sys.path.append("./src")

from pantograph import Server
from neuralproofstate_withimports import NeuralProofState_withImports

def load_sorry(sketch, tactics):
    server = Server(project_path="./", imports=["Mathlib.Data.Real.Basic"])
    for tactic in tactics:
        sketch.append(tactic)
        unit, = server.load_sorry("\n".join(sketch+["sorry"]))
        print(unit.goal_state)

# TODO: this is a work in progress to get the load_sorry to work
class NeuralProofState_withLoadSorry(NeuralProofState_withImports):
    def __init__(self, sketch, state, server):
        self.sketch = sketch
        super().__init__(state=state)
    def apply_tactic(self, tactic):
        self.sketch.append(tactic)
        new_state, = server.load_sorry("\n".join(self.sketch+["sorry"]))
        return NeuralProofState_withImports(state=new_state, prev_tactics=self.prev_tactics + [tactic], informal_info=self.informal_info, server=self.server, parent=self, imports=self.imports)
if __name__ == "__main__":
    sketch = ["example (x y : ℝ) : x * y = 0 → x = 0 ∨ y = 0 := by"]
    tactics = ["contrapose", "rw [not_or]", "intro ⟨hx, hy⟩", "exact mul_ne_zero hx hy"]
    load_sorry(sketch, tactics)


# failed attempt at making tactic_invocations work
# import os
# from pathlib import Path
# example_file = "scripts/Example.lean"
# project_path = Path(os.getcwd()).resolve()
# with open(example_file, "w") as f:
#     f.write("import Mathlib.Data.Real.Basic\n\n")
#     f.write(sketch[0] + "\n")
#     for tactic in tactics:
#         f.write("  " + tactic + "\n")
#         print(f.read())
#         units = server.tactic_invocations(project_path / "Example.lean")
#         if len(units) > 0:
#             print(units[0].goal_state)
