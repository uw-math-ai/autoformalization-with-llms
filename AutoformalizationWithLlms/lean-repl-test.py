from lean_repl_py import LeanREPLHandler, LeanREPLPos, LeanREPLEnvironment, LeanREPLProofState, LeanREPLMessage
from pathlib import Path


# Create a new Lean REPL handler
lean_repl = LeanREPLHandler()

# Optionally, use the REPL from another project for dependencies
# This is needed e.g. if you want to use mathlib.
lean_repl = LeanREPLHandler(project_path=Path("path/to/your/leanproject"))

## Send a command to Lean
lean_repl.send_command("def f := 2")
response, env = lean_repl.receive_json()
# Env will be a LeanREPLEnvironment object, which contains the environment index
LeanREPLEnvironment(env_index=0)
# Response will be a dictionary with the Lean REPL response apart from the environment
{}

## Use an environment for subsequent commands
lean_repl.env = env.env_index
lean_repl.send_command("def g := f + 2") # Will use the previous environment
_ = lean_repl.receive_json()

## Use tactic mode
lean_repl.send_command("def h (x : Unit) : Nat := by sorry")
response, env = lean_repl.receive_json()
# Will return proof state objects LeanREPLProofState
LeanREPLProofState(goal="x : Unit\n⊢ Nat", proof_state=0, pos=LeanREPLPos(line=1, column=29), end_pos=LeanREPLPos(line=1, column=34))
# And messages
LeanREPLMessage(message="declaration uses 'sorry'", severity="warning", pos=LeanREPLPos(line=1, column=4), end_pos=LeanREPLPos(line=1, column=5))