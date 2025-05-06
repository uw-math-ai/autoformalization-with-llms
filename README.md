# Setup

1. Make a new codespace of this repository (you can skip this if you are on Linux already). Select "4 coures" instead of the default "2 cores" for smoother experience. Open the codespace in VSCode.
2. Run `wget -q https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile` to install elan, lake and Lean.
3. Add `lake` to your path with `echo "export PATH=\"$(dirname $(which lake)):\$PATH\"" >> ~/.bashrc`.
4. Download mathlib cache with `lake exe cache get`.
5. Run `poetry install --no-root` to install the dependencies (mainly PyPantograph).
6. Run `poetry run python scripts/pantograph_example.py` to test the installation.

# Eval on minif2f
- Run `poetry run python src/evaluate.py`
- If you get an error that server took too long to respond, you need to make sure minif2f imports are compiled. To do that run `lake exe cache get` and then open file `AutoformalizationWithLlms/minif2f_imports.lean` in VSCode and make sure it compiles.