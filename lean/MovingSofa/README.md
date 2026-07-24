# MovingSofa — Lean formalization track

Machine-verified lemmas for the moving-sofa program
(see `paper/PROGRAM.md`, Part VI). Lean 4.30, no external dependencies,
zero `sorry`.

## Verified (real proofs)

- **F1 — the superset principle (N1).** `famInter_antitone`,
  `superset_principle`, `area_bound`, `certified_upper_envelope`:
  subfamily reconstructions contain the true body, so any monotone area
  functional is bounded by the reconstruction area, uniformly along any
  deformation of the constraint family. This is the one-sidedness carrying
  every certified upper bound in the project.
- **F3a — the stationary-contact mechanism (N4 corollary).**
  On the coefficient module of trigonometric arcs `a·cos t + b·sin t + c`
  with formal derivative `D(a,b,c) = (b,−a,0)`: `stationary_contact`
  (`v + v'' = const c`), `lamA_const`, `lamD_const`, and the cap law
  `lamA_zero_iff` (`λ_A ≡ 0 ⟺ c = −1`, the SOL1 normal form — Gerver
  phase 1 and Σ's first arc). This is the exact algebraic source of every
  cap degeneracy in the program and of the Σ weight `w_μ`.

## Not yet formalized (tracked in PROGRAM.md)

- F1b: plane-topology inclusion for chord-closed reconstructions (Mathlib).
- F2: exact-degree reduction N2.
- F3: full rotating-frame identities N4 + analytic bridge for `D`.
- F5: arb-enclosure import interface.

## Build

```
lake build && .lake/build/bin/movingsofa
```
