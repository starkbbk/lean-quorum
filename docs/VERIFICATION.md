# Verification record

Local verification completed on **2026-10-15**, using Lean 4.33.0-rc1 on
macOS ARM64 and Mathlib commit `9944fe2973b8dc0b86949101ed98232c07cd54a0`.

Command:

```bash
python3 scripts/verify.py
```

| Stage | Observed result |
| --- | --- |
| `lake build` | All eight formal modules, root library, and demo executable built successfully |
| Explicit theorem index | 61 source-declared theorems, each present in the audited environment |
| Transitive axiom audit | 173 project declarations checked, including 111 theorem declarations with generated helpers |
| Permitted foundational axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Guarded collector smoke test | Honest conflicting vote rejected, faulty equivocation retained |
| Executable regression sweep | All 240 configurations passed; each configuration enumerates every quorum pair |
| Audit negative test: incomplete theorem | Rejected as expected |
| Audit negative test: incomplete proof inside a definition | Rejected as expected |
| Audit negative test: project-defined axiom | Rejected as expected |

The sweep covers `n = 0..7`, `f = 0..n`, and `q = 0..n+1`, with the fixed
fault set `Finset.range f`. It checks the executable enumeration against
`n + f < 2q`. It is not an exhaustive enumeration of every fault set. The
parametric formal theorems quantify over arbitrary finite fault sets.

Automatic GitHub CI is not enabled in this initial publication. The workflow
template is provided at [`ci/lean-verification.yml`](../ci/lean-verification.yml).
This local record does not stand in for a remote CI result.
