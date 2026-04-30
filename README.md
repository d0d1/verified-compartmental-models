# Verified Compartmental Models

A reusable Isabelle/HOL framework for certified reasoning about compartmental ODE models, with the classical SIR epidemic model as the flagship instantiation.

## Overview

This project provides machine-checked formalizations of:
- Conservation laws for compartmental systems
- Positivity/nonnegativity of solutions
- Epidemic threshold conditions (R₀)
- Qualitative dynamics (monotonicity, peak theorems)

Built on Isabelle's mature ODE infrastructure (Picard-Lindelöf, flows, invariants).

## Structure

```
theories/          — Isabelle theory files
  Framework/       — Reusable compartmental ODE framework
  SIR/             — SIR model instantiation
document/          — LaTeX sources for AFP-style documentation
```

## Dependencies

Requires Isabelle 2024+ with HOL-Analysis and HOL-ODE sessions.

Shared Isabelle tooling is managed at the parent project level — see the isabelle-projects repository for common infrastructure.

## License

BSD-3-Clause
