# Contrast case

## Problem

- Benchmark: FATE-M
- Problem ID: 23
- Theorem: `isMaximal_of_isPrime_of_fintype`

Let $R$ be a finite commutative ring with identity. Then every prime ideal $I$ of $R$ is maximal.

```lean
import Mathlib

/--
Let $R$ be a finite commutative ring with identity. Then every prime ideal $I$ of $R$ is maximal.
-/
theorem isMaximal_of_isPrime_of_fintype {R : Type*} [CommRing R] [Fintype R]
    (I : Ideal R) (hI : I.IsPrime) : I.IsMaximal :=
```

## Baseline

- Model: `deepseek-flash`
- Attempt limit: 5
- Maximum output tokens per generation: 16384
- Final status: FAILURE

### Attempt 1

```lean
<no parseable proof>
```

First Lean error:
```text
Model output does not contain a proof beginning with `by`
```

### Attempt 2

```lean
<no parseable proof>
```

First Lean error:
```text
Model output does not contain a proof beginning with `by`
```

### Attempt 3

```lean
by
  exact hI.isMaximal
```

First Lean error:
```text
failed to synthesize instance of type class
  Ring.DimensionLEOne R

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

### Attempt 4

```lean
<no parseable proof>
```

First Lean error:
```text
Model output does not contain a proof beginning with `by`
```

### Attempt 5

```lean
<no parseable proof>
```

First Lean error:
```text
Model output does not contain a proof beginning with `by`
```

## Enhanced

- Mode: `full_enhanced`
- Retrieval events: reason='structural theorem: Fintype, Ideal', query='I.IsMaximal I.IsPrime CommRing Fintype Ideal isMaximal isPrime fintype'
- Activated skills: goal_driven_apply
- Verified retrieved lemmas: Ideal.isMaximal_of_isPrime, Ideal.IsPrime.isMaximal', Ideal.isMaximal_iff_isPrime, Ideal.IsPrime.isMaximal, Ideal.isMaximal_of_primeHeight_eq_ringKrullDim
- Retrieved lemmas used in generated proof: Ideal.isMaximal_of_isPrime
- Certified prefix events: 0

## Final verified proof

```lean
by
  haveI : I.IsPrime := hI
  exact Ideal.isMaximal_of_isPrime I
```

## Verification

- Lean return code: `0`
- Independently recompiled source: `scratch/independent_final_verification/23/full_enhanced_final.lean`
- No `sorry`: verified by evaluator
- No `admit`: verified by evaluator
- No added axioms/opaque assumptions: verified by evaluator and exact-source insertion

## Resource comparison

| Mode | Success | API calls | Tokens | Lean calls | Runtime (s) |
|---|---:|---:|---:|---:|---:|
| baseline | False | 5 | 80204 | 1 | 413.61 |
| retrieval_apply | True | 2 | 32344 | 2 | 226.15 |
| prefix_repair | False | 5 | 77265 | 5 | 607.48 |
| full_enhanced | True | 1 | 10299 | 2 | 138.51 |

## Interpretation

The trace establishes a baseline failure and an enhanced Lean-verified success under the same model and generation budget. The logged retrieval, sele`cted skills, compiler diagnostics, and prefix events above show which mechanisms were actually exercised; they support association, not a causal claim beyond this case.

No repeated stability trials were run for this theorem because the search was
stopped at problem 25 to respect the API-cost limit.
