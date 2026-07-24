# Road to the final global proof

## What "solving the moving sofa completely" means now

- **Gerver / one hallway, GLOBAL: already done** — Baek (2024, arXiv:2411.19826)
  proved Gerver's sofa is globally optimal. Our local machinery is a second,
  independent *method* there, not a new truth.
- **The genuinely open summit: Romik's ambidextrous problem.** Global AND
  local optimality of Σ (area ≈ 1.64495) are both open — the second half of
  Romik's 2018 Open Problem 1. No global result covers it; Baek's proof does
  not transfer (his majorant is built on the one-hallway contact structure).
- Therefore: **THE FINAL GLOBAL PROOF = global optimality of Σ**, with a
  by-product independent global proof for Gerver as validation.

## The novel instrument (assessment: partly invented already, here)

**Certified cell-wise quadratic programming over the contact-combinatorics
complex.** Three facts proved in this project make it possible:

1. **Exact quadraticity of frozen reconstructions** (proved; stated
   precisely): the TRUE area with solved junctions is analytic-but-not-
   quadratic within a cell; what is EXACTLY quadratic is any FROZEN
   reconstruction (fixed junction parameters + chords), and by the superset
   lemma it upper-bounds the true area pointwise. That is exactly what a
   certified global bound machine needs: quadratic UPPER ENVELOPES per
   region, with the superset slack shrinking as O(diam^2) under subdivision
   (junction refreezing at region centers).
2. **The superset principle** (proved): any constraint-arc reconstruction
   bounds the true area from above, pointwise along rays — certified upper
   bounds per cell come for free.
3. **The envelope identity** (proved): junction responses are exactly
   quadratic corrections — cell-to-cell transitions are controlled, and the
   true Hessian is the envelope of the per-cell forms.

Global optimization of a certified piecewise-quadratic functional =
branch-and-bound over cells with exact QP relaxations per cell + interval
arithmetic. This is the refinement, by exact quadratic structure, of
Kallus–Romik's coarse angle branch-and-bound; and where Baek needed one
global concave majorant (a stroke that may not exist ambidextrously),
cell-QP needs only local-in-cell convexity data, which we can compute.

The ambidextrous case doubles the contact structure (two hallway families,
one shared body): cells = pairs of contact structures; the per-cell area is
still exactly quadratic (both families' contact paths are affine — verified
symbolically in this project for the reflected family). The instrument
extends without new ideas; the cost is combinatorial size.

## Phases

- **G0 (done, this project):** local machinery — superset/reduction/envelope
  theorems; exact oracles (mpmath + Rust, cross-validated to machine
  precision); H¹ coercivity of the true Hessian at c_G assembled end to end
  (m ≥ 0.087–0.131 on gauged H²); certification protocol demonstrated
  (arb minors + interval quadrature of entries).
- **G1 — local Σ (the missing lemma):** the end-cap symbol of Σ degenerates
  like λ_min ≈ 4.95·θ^1.69 (measured, this project). Build the **weighted
  Gårding framework** (weight vanishing at the caps matching the degeneracy)
  and redo the ladder machinery for Σ. Novel-math content: a degenerate-
  elliptic coercivity theory for envelope functionals — the one place a new
  analytic object is genuinely required.
- **G2 — the global structure theorem:** formalize the cell complex
  (enumerate contact structures reachable from admissible trajectories),
  prove the piecewise-quadratic global decomposition from affineness, and
  the transition rules (the combinatorial moves met empirically here:
  crossings switching on/off, envelope arcs detaching). Testable now with
  the existing oracle at large ε.
- **G3 — the global bound machine:** per-cell certified QP upper bounds +
  branch-and-bound over the complex, in Rust with interval arithmetic.
  Validate by REPROVING Gerver globally (target: match Baek's answer by an
  independent method). This validation step de-risks everything.
- **G4 — Σ global:** run the machine on the doubled complex; combined with
  G1's local control at Σ, conclude global optimality of Σ. THE FINAL
  GLOBAL PROOF.

## G3 SEED: DEMONSTRATED (this session)

`algorithm/rigorous/ray_global.py` + the Rust `fray` mode implement the
machine in miniature along rays: on each subinterval, junctions are frozen at
the midpoint, three evaluations determine the EXACT upper-bound parabola
(frozen area is exactly quadratic in eps), and adaptive subdivision certifies
`sup < A*`. Results:

    ray  eta = e_x sin 2t:  CERTIFIED  area(c_G + eps eta) < A*
                            for all eps in [0.01, 0.60] -- ONE piece,
                            worst sup 2.219483 vs A* = 2.219532.
    ray  eta = e_y sin 2t:  CERTIFIED on [0.01, 0.60] -- 4 pieces.

Spliced with the local theorem (m > 0 on eps <= 0.01), this is a certified
GLOBAL statement along these slices. Caveats to discharge in G3 proper:
f64 -> interval arithmetic; Gamma-simplicity verification per piece; and the
real object is region-wise (not ray-wise) subdivision of trajectory space.

## Why this method vs Baek's (honest comparison)

Baek's proof is complete, global, and unconditional for the one-hallway
problem -- on achievement, it wins outright; nothing here matches a finished
119-page theorem. The claim of superiority is scoped and threefold:

1. **Transferability.** Baek's engine is a single globally concave majorant
   built on the one-hallway contact structure; no ambidextrous analogue is
   known, and the shared-body coupling of two motions is a genuine obstruction
   to constructing one. The cell-QP machine needs only per-region frozen
   quadratic bounds -- proved here for BOTH hallway families -- so it extends
   to Sigma without a new miracle.
2. **Quantitative output.** Concavity yields optimality but no modulus; this
   machinery produces explicit coercivity constants (m >= 0.087-0.131 on
   gauged H^2), explicit margins per region, and uniqueness radii.
3. **Mechanized certification.** Every object in the chain is a closed-form
   integral or a finite jet expression, already running under interval
   arithmetic (arb); the endgame is a machine-checkable certificate, where a
   long human proof is the harder artifact to audit.

Where Baek's method remains stronger: one idea covers all of trajectory space
at once (no combinatorial explosion), and it is DONE. The programs are
complementary: his result anchors Gerver; this machinery is the only current
path to Sigma and to certified, quantitative statements.

## First concrete steps (next sessions)

1. G1: derive the weighted symbol at Σ's caps; candidate weight
   w(θ) = θ^α(π/2−θ)^α with α matched to the measured 1.69 exponent;
   prove the weighted analogue of the multi-contact Gårding inequality.
2. G2: oracle experiment — large-ε ray sweeps counting combinatorial
   transitions and verifying exact per-cell quadratic fits (residual = 0
   within cells), mapping a first patch of the cell complex around c_G.
3. G3 seed: the per-cell QP certificate format (what must be stored per
   cell for a checkable proof), designed so the Gerver validation run and
   the Σ run share it.

Honest scale estimate: Baek's one-hallway global proof is 119 pages. This
program is of comparable magnitude, with two advantages he lacked: the
exact per-cell quadratic structure (his objects were merely concave) and a
validated compute stack. It is a program of months, not sessions — but
every step is named, and none requires an unexplained miracle.
