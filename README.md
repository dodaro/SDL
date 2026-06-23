# SDL to ASP/MiniZinc Compiler

This tool translates specifications written in **SDL (Specification and Description Language)** into executable code for:

- **Answer Set Programming (ASP)** via the **PySpEL** library and the **clingo** solver.
- **Constraint Programming (CP)** via **MiniZinc** and any supported solver (e.g., Gecode, Chuffed, CP‑SAT).

---

## Repository Contents

The tool consists of several Python files that must be kept together:

- `Validator.py` – main entry point, parser, and validator.
- `MiniZincTranslator.py` – generates MiniZinc code from the validated AST.
- `PyspelTranslator.py` – generates ASP (PySpEL) code.
- `error_messages.py` – user‑friendly error strings.
- `grammar.lark` – the Lark grammar definition (required for parsing).

---

## Requirements

- Python 3.7 or higher.
- [Lark](https://github.com/lark-parser/lark) – `pip install lark`
- (Optional) [PySpEL](https://github.com/potassco/pyspel) – required for the ASP target (`pip install pyspel`).
- (Optional) [MiniZinc](https://www.minizinc.org/) – required for the CP target, including a solver such as `cp‑sat`, `chuffed`, or `gecode`.

---

## Installation

1. Clone or download all source files into a folder.
2. Install the Python dependencies:

   ```bash
   pip install lark
   pip install pyspel   # if you plan to use ASP
   ```

3. Make sure the `minizinc` command is in your PATH if you target MiniZinc.
4. For ASP, ensure that the `clingo` binary is installed and note its full path.

---

## Usage

```bash
python Validator.py -t {pyspel|minizinc} [options] <input_file.sdl>
```

### Command-line Options

| Option | Description |
|--------|-------------|
| `-t TARGET` | **Required.** Target language: `pyspel` (ASP) or `minizinc` (CP). |
| `-e SOLVER` | **Execute** the generated code. For `pyspel`, `SOLVER` must be the **full path** to the `clingo` executable. For `minizinc`, `SOLVER` is the name of a MiniZinc solver (e.g., `cp-sat`, `chuffed`, `gecode`). |
| `-v` / `--verbose` | Print the generated code to the console before execution. |
| `-f FILE` | Write the generated code to `FILE` instead of the default (`o.py` for ASP, `outputMzn.mzn` for MiniZinc). |
| `-p` / `--print-program` | For ASP only: print the program without executing it. |
| `-r` / `--disable-recursive-check` | Disable the dependency‑cycle check. |

---

## Examples

### 1. Translate and Solve with ASP (clingo)

```bash
python Validator.py -t pyspel -e "C:/Users/yourname/miniconda3/envs/potassco/Library/bin/clingo.exe" examples/example1.txt
```

- Generates a Python script using PySpEL.
- Runs it with the provided `clingo` executable.
- Prints the answer sets (models) found.

### 2. Translate and Solve with MiniZinc (CP‑SAT)

```bash
python Validator.py -t minizinc -e cp-sat -v examples/example1.txt
```

- Translates the specification to MiniZinc.
- Executes it with the `cp‑sat` solver (requires Google OR‑Tools MiniZinc).
- The `-v` flag also displays the generated MiniZinc code.

### 3. Generate Code without Execution

```bash
python Validator.py -t minizinc -f mymodel.mzn examples/example1.txt
```

Produces a `.mzn` file that you can later run manually with `minizinc`.

### 4. Just Print the ASP Program

```bash
python Validator.py -t pyspel -p examples/example1.txt
```

Prints the generated PySpEL program without execution.

---

## Notes on Solvers

- **ASP (clingo):** Provide the full absolute path to the `clingo` binary. You can obtain it via `conda install -c potassco clingo` or from the [Potassco](https://potassco.org/clingo/) website.
- **MiniZinc:** Ensure that the `minizinc` command is available in your system PATH. Supported solvers depend on your MiniZinc installation. Popular choices: `cp-sat` (Google OR‑Tools), `chuffed`, `gecode`.