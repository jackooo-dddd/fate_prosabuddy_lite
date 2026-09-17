# FATE ProsaBuddy-Lite

An interpretable Lean 4 research prototype for comparing ordinary whole-proof
compiler repair with two general methods adapted from ProsaBuddy:

1. verified local Mathlib retrieval plus goal-driven `apply`/`refine`;
2. first-error discipline plus compiler-certified proof-prefix repair.

The project is independent of the sibling miniF2F prototype. Its proving core
uses a `BenchmarkAdapter`; the first adapter targets FATE-M.

## Layout

```text
benchmark/FATE-M/        official pinned benchmark checkout
agent/                   benchmark-independent proving implementation
tests/                   lightweight unit and Lean integration tests
results/                 JSONL traces, summaries, contrast report
scratch/                 every exact source compiled by Lean
```

`benchmark/prosabuddy-reference/` is a local, ignored read-only checkout used to
study the official methodology. No Coq syntax or benchmark solution is copied
into generated Lean proofs.

## FATE-M and Lean setup

```bash
git clone https://github.com/frenzymath/FATE-M benchmark/FATE-M
cd benchmark/FATE-M
lake exe cache get
lake build
cd ../..
```

The checked-out FATE-M configuration pins Lean and Mathlib `v4.28.0`. This
project does not replace its `lean-toolchain`, `lakefile.lean`, or manifest.

Create the Python environment:

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -r requirements.txt
```

## DeepSeek setup

```bash
cp .env.example .env
```

Set the following locally without committing it:

```text
DEEPSEEK_API_KEY=<your key>
```

The default model is `deepseek-flash`, the default temperature is `0`, and the
default proof-generation budget is five calls per theorem. The key is never
included in prompts, logs, summaries, or documentation.

## Experimental modes

### Baseline

```bash
python -m agent.run_experiment --mode baseline --problem 1
```

Uses only the unchanged theorem source, whole-proof generation, the first Lean
diagnostic, and whole-proof retry. It receives no retrieval, special skill, or
certified-prefix context.

### Retrieval and goal-driven apply

```bash
python -m agent.run_experiment --mode retrieval_apply --problem 1
```

Retrieval is triggered by structural theorem types or relevant failures. It
searches only the pinned local Mathlib source, verifies candidates with
`#check` in FATE-M's Lean environment, and sends a small verified set plus a
candidate audit and goal-driven application skill.

### Compiler-certified prefix repair

```bash
python -m agent.run_experiment --mode prefix_repair --problem 1
```

After a failed proof, the agent splits top-level tactic chunks and compiles
decreasing prefixes. A prefix is certified only when its sole remaining problem
is unfinished Lean goals. The next generation is asked for a suffix; an entirely
new proof is explicitly logged as `prefix_abandoned=true`.

### Full enhanced

```bash
python -m agent.run_experiment --mode full_enhanced --problem 1
```

Combines verified retrieval, goal-driven application, first-error/small-step
discipline, and certified prefix repair.

## Automatic contrast search

```bash
python -m agent.compare_modes \
  --benchmark fate-m \
  --max-problems 20 \
  --max-attempts 5
```

For each theorem in numeric order, this runs baseline first. Baseline successes
skip enhanced modes. A baseline failure triggers `full_enhanced`; an enhanced
success then triggers the two component ablations and writes
`results/contrast_case.md`.

Continue later stages with deterministic slices:

```bash
python -m agent.compare_modes --benchmark fate-m --start-index 20 --max-problems 5
python -m agent.compare_modes --benchmark fate-m --start-index 50 --max-problems 100
```

For a cost-bounded search stage, apply the same completion cap to every mode:

```bash
python -m agent.compare_modes --benchmark fate-m --start-index 20 \
  --max-problems 5 --max-attempts 5 --max-output-tokens 16384
```

## Reproduce the observed contrast case

The cost-bounded search found a strict same-code contrast at FATE-M problem 23,
`isMaximal_of_isPrime_of_fintype`: baseline failed all five generations while
`full_enhanced` succeeded on its first generation. The retrieval-only ablation
also succeeded, while prefix-only repair failed. Run the four conditions with
the same model, five-call budget, temperature, and completion cap:

```bash
python -m agent.run_experiment --mode baseline --problem 23 --max-attempts 5 --max-output-tokens 16384 --model deepseek-flash
python -m agent.run_experiment --mode retrieval_apply --problem 23 --max-attempts 5 --max-output-tokens 16384 --model deepseek-flash
python -m agent.run_experiment --mode prefix_repair --problem 23 --max-attempts 5 --max-output-tokens 16384 --model deepseek-flash
python -m agent.run_experiment --mode full_enhanced --problem 23 --max-attempts 5 --max-output-tokens 16384 --model deepseek-flash
```

The search stopped API experimentation after problem 25. No repeated stability
runs were made for problem 23 because of the explicit cost limit, so the report
is a verified single-run contrast rather than a statistical reliability claim.
See `results/contrast_case.md` and `results/final_experiment_summary.json`.

## Tests

```bash
python -m unittest discover -v
```

Tests cover FATE loading, exact proof-hole replacement, scratch generation,
proof-integrity checks, Lean success/failure, structured errors, failure
classification, verified retrieval and formatting, mode features, prefix
extraction/assembly, and logging.

## Evidence and outputs

Every proof-generation attempt is appended to `results/<run>.jsonl`, including:

- theorem, prompt, model output, exact scratch path, full Lean stdout/stderr;
- first Lean error and failure class;
- retrieval trigger/query/candidates/verified signatures/selected lemma;
- activated skill, certified prefix, remaining goals, suffix, abandonment flag;
- result, runtime, and token usage.

`results/<run>_summary.json` separately records API calls, retrieval/tool calls,
Lean calls, tokens, runtime, and per-problem status. All diagnostic and final
Lean sources remain under `scratch/<run>/<problem>/`.

No generated proof is compared with a reference solution. Final success requires
an unchanged theorem source, Lean return code zero, and rejection of `sorry`,
`admit`, suggestion tactics, new axioms/opaque declarations, and fake theorem or
parameter declarations.
