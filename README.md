# STLTree 🌳

STLTree is a satisfiability checker for temporal logic formulas
in discrete-time Signal Temporal Logic (STL) and Mission-Time Linear Temporal Logic (MLTL),
including a solver based on a tree-shaped tableau, and one based on a bounded SMT encoding.

## 📦 Features

- Parses temporal logic formulas from file
- Supports both **tableau-based** and **SMT-based** solving
- Optional trace output and `.dot` graph generation
- Flexible control over solver optimizations


## 🚀 How to Run

### ✅ Requirements and Dependencies to Install

We recommend running STLTree in a Python [virtual environment](https://docs.python.org/3/tutorial/venv.html).
Create one (under Unix-like systems) with:
```sh
python -m venv .venv
source .venv/bin/activate
```

STLTree requires, among other packages:

- Python 3.11+
- pe>=0.5.0
- z3-solver>=4.13.0.0

Install them through:

```sh
pip install -r requirements.txt
```
If this doesn't work, try the [development instructions](#development-environment).


### ⌨️ Command-line options:

| Option                              | Description                                                                                     |
|-------------------------------------|-------------------------------------------------------------------------------------------------|
| `-s`, `--smt`                       | Use SMT-based satisfiability checker instead of the tableau-based method.                       |
| `-f`, `--fol`                       | Use FOL satisfiability checker instead of tree-based tableau.                                   |
| `-d`, `--max-depth <int>`           | Maximum depth for tableau construction (ignored if `--smt` is used). Default: `10000000`.       |
| `-p`, `--plot <file>`               | Output tableau as a `.dot` file for visualization (ignored if `--smt` is used).                 |
| `--print-trace`                     | Print an example trace that satisfies the formula.                                              |
| `-t`, `--strong-sat`                | Use strong satisfiability semantics (avoids vacuous truth). Experimental.                       |
| `--smtlib-result`                   | Output result in SMTLIB format: `sat`, `unsat`, or `unknown`.                                   |
| `--parallel`                        | Enable parallel tableau construction. Experimental.                                             |
| `--mltl`                            | Use MLTL semantics for `U` and `R` operators (not supported with SMT solver).                   |
| `--no-jump`                         | Disable the jump rule in the tableau.                                                           |
| `--no-formula-optimizations`        | Disable formula-level optimizations.                                                            |
| `--no-children-order-optimizations` | Disable child-node ordering optimizations.                                                      |
| `--no-early-local-consistency-check`| Only check local consistency for poised nodes.                                                  |
| `--no-memoization`                  | Disable memoization for tableau nodes.                                                          |
| `--no-simple-nodes`                 | Disable simple-node optimization.                                                               |
| `--no-g-f`                          | Disable special handling for `G` (Globally) and `F` (Eventually) operators.                     |
| `-v`, `--verbose`                   | Enable verbose output for debugging or analysis.                                                |
| `formula <file>`                    | Path to a file containing the temporal logic formula to be checked.                             |


### 🏁 Running STLTree

Run
```sh
python stltree.py [options] <formula-file>
```

Benchmarks (and [instructions for running them](benchmarks/README.md)) are located in the [benchmarks directory](benchmarks).


### Input Format

STLTree accepts input files that contain formulas in discrete, bounded-time STL or MLTL, with the following syntax:

| Operator  | Full Name         | Arity   |
|-----------|-------------------|---------|
| `G[a,b]`  | Globally          | Unary   |
| `F[a,b]`  | Eventually        | Unary   |
| `U[a,b]`  | Until             | Binary  |
| `R[a,b]`  | Release           | Binary  |
| `!`, `~`  | Not               | Unary   |
| `&`, `&&` | And               | Binary  |
| `\|`, `\|\|` | Or                | Binary  |
| `->`      | Implies           | Binary  |
| `<->`     | If and only if    | Binary  |

where `a` and `b` must be integers.

Atomic formulas can be Boolean variables, or comparisons of linear expressions of real variables.
Available comparison operators are `<=` `<` `>=` `>` `==` `!=`, and arithmetic operators are `+` and `-`.

Check the directory `benchmarks/formulas` or the tests in `tests` for some examples.

By default, STLTree checks satisfiability with a tree-shaped tableau.
Command line argument `--smt` causes STLTree to use a bounded-model-checking-style SMT encoding.


## 🧑‍💻 Development Environment

To setup the development environment, you'll need a working installation of `python`, `pip`, and [`pdm`](https://pdm-project.org/).

`cd` in the root of the repository, and activate a Python Virtual Environment.

Then run:
```sh
pdm lock --platform=YOUR_PLATFORM --python=YOUR_VERSION --append
pdm install -d
```
to install all required dependencies.
Replace `YOUR_PLATFORM` with your platform name (e.g., `manylinux_2_39_x86_64`)
and `YOUR_VERSION` with the Python version you have installed (e.g., `==3.12.3`).
