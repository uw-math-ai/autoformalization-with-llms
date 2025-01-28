# Setup

1. Make a new codespace of this repository (you can skip this if you are on Linux already).
2. Run `wget -q https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile` to install elan, lake and Lean.
3. Open the codespace in VSCode and run `git clone --recurse-submodules https://github.com/stanford-centaur/PyPantograph /workspaces/PyPantograph` to get `PyPantograph` in the workspace.
4. Run `pipx install poetry` to install poetry (needed for PyPantograph).
5. Navigate to the `PyPantograph` directory with `cd../PyPantograph` and run `poetry build` and `poetry install` to install PyPantograph.
6. Run `lake build` from the `examples/Example/` directory to build the Lean files there.
7. From the `PyPantograph/` directory run `poetry run examples/aesop.py` and `poetry run examples/sketch.py` to run the examples.
8. If you get a `permission denied` error, run `chmod -R 774 examples/` to fix it.
