
from pantograph.server import Server

project_path = "./"
lean_path = "/Users/siyuange/Documents/auto_formalization/autoformalization-with-llms/AutoformalizationWithLlms/example.lean"
imports = ["Mathlib.Data.Nat.Factorization.Basic", "Mathlib.Data.Nat.Prime.Basic", "Mathlib.Data.Real.Basic"]
print(f"$PWD: {project_path}")
print(f"$LEAN_PATH: {lean_path}")
server = Server(imports=imports, project_path=project_path)
units = server.tactic_invocations(lean_path)


with open(lean_path, 'rb') as f:
    content = f.read()
    for i, unit in enumerate(units):
        print(f"#{i}: [{unit.i_begin},{unit.i_end}]")
        unit_text = content[unit.i_begin:unit.i_end].decode('utf-8')
        print(unit_text)


for i, unit in enumerate(units):
    for j in unit.invocations:
        print(f"[Before]\n{j.before}")
        print(f"[Tactic]\n{j.tactic} (using {j.used_constants})")
        print(f"[After]\n{j.after}")