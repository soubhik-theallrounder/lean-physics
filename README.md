# LeanPhysics

Small, self-contained Lean 4 formalizations of five physics ideas. Everything
is over `Int` / `Nat` using only Lean's core library (no Mathlib), so each
statement is exact and checks in under a second.

> **AI assistance disclosure:** these files were written with the help of
> Claude (Anthropic) in a session on 23 November 2026, and compiled with
> Lean 4.24.0. They are learning projects, not a contribution to Mathlib.

## Contents

| File | Physics idea | Main results |
|------|--------------|--------------|
| `LeanPhysics/SplitComplex.lean` | Special relativity in 1+1 dimensions. Events are split-complex numbers `t + x·j` (`j² = 1`); boosts are multiplication. | `interval_mul` (the interval is multiplicative), `boost_preserves_interval`, `lightcone_invariant`, `causal_invariant`, `unit_norm_trivial` |
| `LeanPhysics/Oscillator.lean` | A symplectic-Euler harmonic oscillator whose modified energy `x² + xp + p²` is conserved exactly. | `energy_iter`, `period_six`, area preservation |
| `LeanPhysics/Heisenberg.lean` | Quantum oscillator ladder operators on occupation-number states. | `commutator` (`[a, a†] = 1`), `number_basis` (`N eₖ = k eₖ`), `number_commutes` (`[N, a†] = a†`) |
| `LeanPhysics/Galilean.lean` | Galilean relativity: boosts compose by adding velocities, time is absolute, simultaneous distances are invariant. | `boost_add`, `boost_neg`, `simultaneous_distance` |
| `LeanPhysics/FreeFall.lean` | Constant acceleration with a discrete clock; exact kinematics and a work-energy identity. | `run_v`, `run_x`, `work_energy` |

## Build

```
lake build
```

`LeanPhysics.lean` ends with `#print axioms` checks. They report only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry`.

## Ideas for next steps

* Port `SplitComplex` to real numbers with Mathlib so genuine boosts
  (`cosh φ`, `sinh φ`) are available, and prove velocity addition.
* Show that the oscillator map is a rotation of order 6 in the Eisenstein lattice.
* Build the full Fock space and prove the uncertainty relation.
