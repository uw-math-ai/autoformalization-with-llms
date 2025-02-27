import sys
sys.path.append("./src")

from pantograph import Server
from neuralproofstate_withimports import NeuralProofState_withImports

def load_sorry(sketch, tactics, imports):
    server = Server(project_path="./", imports=imports)
    unit = server.load_sorry("\n".join(sketch+["sorry"]))[0]
    for tactic in tactics:
        print(f"Applying tactic: {tactic}")
        sketch.append(tactic)
        unit = server.load_sorry("\n".join(sketch+["sorry"]))[0]
        if unit.goal_state is not None:
            print(unit.goal_state)
        else:
            print("No goal state found, see message:")
            print(unit.messages)

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
    print(f"Proving theorem: {sketch[0]} \n")
    tactics = ["contrapose", "rw [not_or]", "intro ⟨hx, hy⟩", "exact mul_ne_zero hx hy"]
    load_sorry(sketch, tactics, ["Mathlib.Data.Real.Basic"])
    # TODO: Make this theorem work
    sketch = ["theorem Prime.dvd_iff_eq {p a : ℕ} (hp : p.Prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a := by"]
    print(f"Proving theorem: {sketch[0]} \n")
    tactics = ["refine ⟨?_, by rintro rfl; rfl⟩", "rintro ⟨j, rfl⟩", "rcases prime_mul_iff.mp hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)", "· exact mul_one _", "· exact (a1 rfl).elim"]
    load_sorry(sketch, tactics, ["Mathlib.Data.Nat.Prime.Defs"])

