# THE PROGRAM — formal ledger toward the complete solution

Status legend: **[P]** proved (symbolic/pen-level, machine-verified where noted) ·
**[C]** certified (arb interval arithmetic, end to end) ·
**[K]** computed (float/high-precision, cross-validated) ·
**[M]** measured (numerical evidence, not load-bearing) ·
**[ ]** open.

Every box below is a precise mathematical statement or a finite computation.
Nothing on this list is open-ended.

---

## Part I — Novel mathematics inventory (results in their own right)

The instruments invented or first-derived in this project, stated formally.
These transfer beyond the sofa problem to envelope/intersection functionals
generally.

- **[P] N1. The superset principle.** For a family of closed constraint sets
  {H_t(c)} and any closed curve Γ assembled from subarcs of constraint
  boundaries and chords, ∩_t H_t(c) ⊆ R(Γ); hence the reconstruction area
  bounds the true area pointwise along any deformation. One-sided error,
  certified upper bounds for free. (3-line proof; used ~everywhere.)
- **[P] N2. Exact-degree reduction.** If every constraint boundary is affine
  in the trajectory jet, then any frozen-limit chord-closed reconstruction
  has area EXACTLY polynomial (degree 2; degree 3 with affine limit motion)
  in the deformation parameter. Combined with N1: local optimality reduces
  to sign questions about finitely many explicit polynomials — **no Taylor
  remainder exists anywhere in the argument**.
- **[P] N3. The envelope identity.** ∂A/∂b vanishes identically along
  zero-length-chord configurations, whence Q_β(η) = Q_true(η) +
  (β−β_IFT)ᵀH_bb(β−β_IFT) exactly: the true Hessian is the envelope of the
  frozen family, and the frozen form's defect is the explicit indefinite
  H_bb-correction.
- **[P] N4. Rotating-frame envelope-speed identities.** For contact paths of
  a rotation path x = R_t v + κ: A′ = λ_A ν, B′ = λ_B ν, C′ = λ_C μ,
  D′ = λ_D μ with λ_A = v₁+v₁″+1, λ_B = λ_A−1, λ_D = −(v₂+v₂″),
  λ_C = λ_D−1. Corollary (the **stationary-contact mechanism**):
  trigonometric arcs (v = a·cos t + b·sin t + const) make the corresponding
  contact a stationary POINT (λ ≡ 0) — the source of all cap degeneracies
  found in this project (Gerver phase 1/5; Σ phases 1/3).
- **[P] N5. Per-arc Wirtinger forms.** In the moving frame (p,q) =
  (⟨η,μ⟩,⟨η,ν⟩): δA∧δA′ = p(p+p″), δC∧δC′ = q(q+q″), corner path η∧η′ ≡ 0
  for fixed-direction η. The second variation of an envelope-area functional
  is a masked sum of 1-D Wirtinger forms — the structural reason for
  −‖η′‖²-type coercivity and for the sum rules.
- **[P] N6. Support-function splitting.** S = C \ N with C convex and its
  support function AFFINE in the trajectory ⟹ the convex part of the area
  is exactly quadratic with sharp Gårding constant; all breakpoints live in
  the notch. (Second, independent derivation of coercivity; kills the
  two-norm ghost at the leading order.)
- **[P] N7. Breakpoint reparameterization.** δ_cD ∥ D′ (both ∥ μ), so the
  junction's η′-dependence is absorbed by a parameter shift: moving
  breakpoints move no geometry at first order; junction displacement =
  ⟨η(b),ν⟩ν + O(ε²). Kills the classical two-norm obstruction at its root.
- **[P] N8. PSD-Gram/Schur-product far-tail bound.** For banded oscillatory
  couplings a(k,l) ≈ c·sin(2(l−k)θ_R)/(l−k): TT* = (c²/2)·C∘S with C the
  rank-2 cosine Toeplitz and S a PSD Gram; Schur's product theorem gives
  ‖T_far‖ ≤ c·√((N/2+σ)/(2(G−1))) with explicit σ — the first coupling
  bound in this problem landing at the measured scale.
- **[P] N9. The weighted cap framework (Σ) — mechanism PROVED.** Cap
  degeneracy = stationary contacts (N4): on the cap phases the only MOVING
  contacts of each family are its two ν-slot arcs (mask table computed:
  `sigma_masks.py`; both families' tables coincide by ρ-invariance). The
  two families' ν-frames at parameter θ point along ν_{±θ}, an angle 2θ
  apart, and the frame-pair Gram ν_θν_θᵀ + ν_{−θ}ν_{−θ}ᵀ has eigenvalues
  {2cos²θ, 2sin²θ} — the ambidextrous structure repairs its own cap
  degeneracy at exactly rate sin²θ. Hence the weight
  w_μ = min(1, sin²θ/sin²β, cos²θ/sin²β), w_ν = 1, with the anomalous
  stationary-contact responses one-signed favourable (N1). Core identity
  machine-verified (Lean: `frame_pair_identity`, `frame_pair_coercive`).
- **[P-mech/K] N11. The fan-bite 3/2-law.** At a stationary wall fan, the
  cutting-side response of the TRUE area is super-quadratic:
  F(−ε) − F₀ ≈ −c·ε^{3/2} (bite depth ε, width √ε from the envelope
  geometry; measured c ≈ 20 at Gerver's phase-1 fan, constant across
  ε = 5e-4..2e-3). Consequences: the true functional is only C^{1,1/2}
  at stationary-fan candidates; the kink is one-signed FAVOURABLE; and
  every smooth oracle (jet/structure-following, or fan-released) is a
  superset upper form dominating both one-sided branches — the uniform
  justification of the certified objects at both c_G and Σ.
- **[K→ ] N10. Certified cell-wise QP (the global machine).** Trajectory
  space carves into combinatorial cells (junction-branch charts); frozen
  reconstructions give exact quadratic upper envelopes per region (N1+N2)
  with slack O(diam²) under refreezing; adaptive subdivision + interval
  arithmetic = certified global bounds. Demonstrated on rays (arb-certified
  slice theorem); region-wise version = Part IV.

---

## Part II — Local theorem at Gerver's c_G (the 46-page manuscript)

- **[P]** Superset lemma; reduction theorem (quadratic & cubic forms);
  envelope identity; per-arc forms; tangency identities; reparameterization;
  interior Gårding (Q ≤ −½‖η′‖² + C₀‖η‖², C₀ ≤ 50); support-function
  theorem; λ_A ≡ 0 phase-1 degeneracy.
- **[C]** K=16 frozen-block negative definiteness — **unconditional**
  (all 528 entries by interval quadrature, radius ≤ 2.3e-20; minor test on
  the ball matrix at 256 bits). K=32 frozen indefiniteness (rigorous
  Rayleigh). Local–global splice input on [0, 0.01].
- **[K]** True-Hessian ladder to 124 modes: m₁(K) = .805/.797/.790/.781/.775,
  fit m∞ ≈ 0.765 (two independent pipelines agreeing to machine precision;
  every anomaly traced: basin jumps, chord artifact, kink Newton,
  transition-straddling stencils, H²-scale stencils).
- **[K]** Tail weld: τ(65..192) = 0.4689, τ(65..280) = 0.4764, far section
  0.1068 vs lemma bound 0.35 [P]; proved c_T = 0.497 [P];
  **m ≥ 0.139** (slope-free), **m ≥ 0.087–0.131** on gauged H² (three-block
  weld, τ_s = 0.063 computed).
- **[ ] L1.** Certified sweep of the remaining computed matrices (true-Hessian
  blocks, cross blocks) — identical mechanical repetition of the done K=16
  sweep. *(compute-hours)*
- **[!] L2-CORRECTION.** The wrap chord of the standard frozen layout
  GENUINELY CROSSES the swung A-arc at ε ≈ 0.45 (verified: one true
  sign-crossing within the segment span) — the frozen curve is
  non-simple on ≈ [0.393, 0.60], so the ORIGINAL arb ray claim's
  float-simplicity check was inadequate there and that portion is
  WITHDRAWN. The certified x-ray statement is exactly the sweep result
  below. Fix in progress: head-collapse layout (absorb A-head + pocket
  into the wrap chord, ending at the tail arc's own endpoint).
- **[C/ ] L2.** Γ-simplicity certification of the x-ray certificate
  (`ray_graph_cert.py`), full sweep run: **CERTIFIED on
  [0.01, 0.2578] ∪ [0.2727, 0.3926]** (30 pieces; area + simplicity +
  winding in ball arithmetic — includes the local-splice region, so the
  spliced local+slice statement is now unconditional on ε ≤ 0.2578).
  FINAL x-ray RESULT: **CERTIFIED on [0.01, 0.59352] ∪ [0.59838, 0.60]**
  (both gap windows closed by the head-collapse layout; the remaining
  4.9·10⁻³ sliver at 0.594–0.598 straddles the ε≈0.58 combinatorial
  cell transition, where the midpoint-frozen reconstruction is maximally
  awkward — chaseable later with transition-anchored b0 if wanted).
  y-ray sweep in progress. Found en route:
  reversal pockets RETRACE the envelope (chord cuts must span positive
  net displacement — implemented), and the winding form of the superset
  lemma (wind ≥ 1 on S, ≥ 0 off) is the right side condition for
  non-simple frozen curves.
- **[ ] L3.** Final assembly write-up pass: one theorem statement
  "c_G is a strict local maximum on the explicit H²-ball, computer-assisted,
  modulo [the shrinking list]", with the dependency graph printed.
- **[P/K] L4 (audit, RESOLVED).** The true Gerver functional IS kinked at
  c_G along phase-1 cap directions (polygon oracle, cap-wide bump:
  releasing side quadratic ≈ −4·L², cutting side a 3/2-POWER LAW
  F(−ε)−F₀ ≈ −20·ε^{3/2} — the fan bite has depth ε, width √ε:
  super-quadratic, strictly favourable). The Part-II jet oracle is the
  smooth STRUCTURE-FOLLOWING superset form (fwd/bwd symmetry verified
  after removing an endpoint-leak linear term): by N1 it dominates both
  one-sided true forms, so the manuscript's ladder-negativity chain is
  VALID and strengthened — same architecture as the Σ fan release.
  Manuscript needs the interpretive remark (terminology: "structure-
  following Hessian"), queued with L3.

## Part III — Local theorem at Σ (G1) — the genuinely new result

- **[P] S1.** Cap law: λ_A ≡ 0 on (0,β), mirrored on (π/2−β,π/2); full
  first-phase speed table (0,−1,−½,+½) exact (N4 + Romik's closed forms).
- **[P] S2.** Exact weight w_μ, w_ν (N9).
- **[K] S3.** Ladder for Q_Σ at K = 10/16/24 (stencil-validated), with
  the DISCOVERY SEQUENCE recorded in SIGMA_LOCAL.md §7: weighted-H¹
  margins decay (0.377/0.160/0.056 — floor hypotheses tested and
  refuted); smooth cap bumps are hyper-coercive (Q/L² to −272); the
  functional is KINKED at c_R (one-sided branch ratio 0.12, the
  stationary-contact ignition); both branches strictly negative along
  the worst mode (−9 / −43 per unit L²); and the K-STABLE invariant is
  **L²-coercivity: m_L² = 3.98 / 3.68 / 3.58**, limit ≈ 3.5.
- **[ ] S3b.** Branch-resolved ladder. Measurement design: since Q is
  piecewise-quadratic, each branch form Q_cell is the EXACT Hessian at
  any base point strictly inside its cone — so shift the base
  c_R → c_R + δ·η_cell (η_cell deep in the cone, δ tiny) and run the
  UNCHANGED central-difference ladder there: it captures Q_cell with no
  one-sided stencils at all. Identify the ignition functionals ℓᵢ(η)
  (cap-wall normal displacements) from the mask/N4 data to enumerate
  cones; ~4 shifted ladders. Extend the L² ladder to K=32 for the
  average-form limit.
- **[ ] S4.** Σ analytic oracle (both families; the Rust port pattern) — for
  precision beyond Shapely and for certification.
- **[P°] S5.** Σ weighted interior Gårding (Theorem 4, SIGMA_LOCAL §5):
  proof route complete and the statement stands — but S3's data shows it
  is VACUOUS on cap-oscillatory modes (the unweighted C₀‖η‖² slack
  dominates the weighted coverage there): true, not delivering. Kept as
  a bulk instrument; the delivering frame for the caps is the cell-wise
  L² statement (S7′).
- **[P/K→] S7″ (supersedes S7′ — the delivering route).** FAN RELEASE:
  replace each cap's stationary wall fan by its two extreme walls. By N1,
  F_rel ≥ F with EQUALITY at c_R (half-planes through a common point are
  determined by their extreme normals — verified 2·10⁻¹⁰), and F_rel is
  C² near c_R (fan kink gone: fwd/bwd = 1.0000 at three stencil sizes vs
  0.12 for the full functional). Hence Q_rel ≥ Q one-sidedly, and
  **Q_rel ≤ −m‖η‖²_{L²} ⟹ Σ strict local max, modulus m** — no branch
  enumeration, no kink in the certified object. First datum:
  Q_rel(cap bump) = −16.62 stencil-stable. Released ladder K=10/16/24
  chained and running (`sigma_hessian_released.py`,
  `sigma_rel_K{K}.npy`). The wedge-bite terms discarded on the
  favourable side are the corner-fan support functional — N11 candidate
  if needed quantitatively later.
- **[~] S7′ (superseded by S7″).** Cell-wise branch enumeration — kept
  as the fallback/refinement frame (branch data: −9/−43 per unit L²
  along the worst mode; FD-average m_L² ≈ 3.5).
- **[ ] S6.** Σ tail weld (weighted analogues of the Part-II items).
- **[ ] S7.** Statement: "Σ is a strict local maximum of the ambidextrous
  functional" (computer-assisted, same standard as Part II) — **the first
  new-truth theorem of the program** (no prior result implies it).

## Part IV — The global machine (G2–G3)

- **[K] G2a.** First cell map: ~4 cells along a full ray; transitions at
  ε ≈ .02/.04/.16/.58; chart boundary visible.
- **[C] G3a.** Ray-global slice theorem: area(c_G+ε·eₓsin2t) < A* for all
  ε ∈ [.01,.60], **certified in arb** (5 pieces; simplicity float-checked).
- **[ ] G2b.** Transition rules formalized (junction-branch folds, crossing
  ignition/extinction) + cell enumeration bound near c_G.
- **[ ] G3b.** Region-wise machine: finite-dimensional charts (truncated
  trajectory space) with the LOCAL theorem supplying the tail: the key
  lemma "certified bound on a chart + coercive tail ⟹ bound on the full
  ball of trajectory space". *(the main remaining architecture item)*
- **[ ] G3c.** Compactness/normalization reduction (à la Kallus–Romik/Baek:
  monotone normalized sofas) so the global search space is a compact
  finite-parameter family. *(known technology, must be redone certified)*
- **[ ] G3d.** GERVER GLOBAL VALIDATION RUN: reprove Baek's theorem by the
  cell machine. De-risks everything before Σ.

## Part V — Σ global (G4): THE FINAL GLOBAL PROOF

- **[ ] G4a.** Doubled-complex cell machine for the ambidextrous functional
  (both families; the per-cell structure already proved for the reflected
  family). NOTE the unification dividend: S7″'s released functional IS a
  cell-machine object (a structure-following superset form), and N11 shows
  every smooth certified object at a stationary-fan candidate is of this
  kind — the local splice and the global cells now share one formal
  framework and one certification pipeline.
- **[ ] G4b.** Global run for Σ + splice with S7″. **Result: global
  optimality of Σ — the completion of the moving-sofa problem** (Romik's
  Open Problem 1, both halves; Gerver's half being Baek's).

## Part VI — Formalization track (machine-checked proofs)

Ordered by dependency; each item is Lean-ready in the sense that its
informal proof is short and self-contained.

- **[P] F1.** N1 (superset lemma) — **DONE, machine-verified** (Lean 4.30,
  `lean/MovingSofa`, zero sorry): `famInter_antitone`, `superset_principle`,
  `area_bound`, `certified_upper_envelope`. Remaining sub-item F1b: the
  plane-topology chord-closure inclusion (Mathlib).
- **[P] F2a.** N2-core (exact-degree) — **DONE, machine-verified**:
  `exact_degree` (bilinear ∘ affine = exact quadratic with explicit
  coefficients). F2b (bridge: Green form bilinearity over arc integrals)
  open — Mathlib integration calculus.
- **[P] F3a.** N4-corollary (stationary-contact mechanism) — **DONE,
  machine-verified**: on the trig coefficient module, `v + v'' = const c`,
  `lamA_const`, `lamD_const`, cap law `lamA_zero_iff` (λ_A ≡ 0 ⟺ SOL1 form
  c = −1). Full N4/N5 (F3) still open: needs Fourier-product API or
  Mathlib `deriv` + the analytic bridge for the formal derivative.
- **[P] F3b.** N9-core (ambidextrous frame-pair mechanism) — **DONE,
  machine-verified**: `frame_pair_identity` ((cu+sv)²+(cu−sv)² = 2c²u²+2s²v²)
  and `frame_pair_coercive` (2m(u²+v²) ≤ 2c²u²+2s²v² for m ≤ c², m ≤ s²).
- **[P] F4a.** N10 chain-soundness core — **DONE, machine-verified**:
  `psum_strict_mono`, `chain_injective` (positive steps ⟹ injective path),
  the discrete skeleton behind the monotone-chain simplicity certificate.
- **[P] F4b.** S7″ fan-combination identity — **DONE, machine-verified**:
  `fan_combination_x`, `fan_combination_y` (interior fan normals are
  combinations of the extremes; the algebraic heart of the fan release).
- **[P] F4c.** Lemma 7a ν-slot collapse — **DONE, machine-verified**:
  `nu_slot_collapse` (the exact identity closing the Σ cap tail sector).
- **[ ] F4.** N7, N3, N6 — short symbolic proofs.
- **[ ] F5.** The certified-numerics interface: import arb enclosures as
  Lean facts (the established `interval_cases`-style bridge or trust-tagged
  constants), so Part II's [C] items become machine-checked end-to-end.

---

## Standing discipline

- Every new claim enters this ledger with a status tag before it enters the
  manuscript.
- No status upgrades without the artifact (proof text, arb log, or
  cross-validated computation) committed to the repository.
- Negative results and dead instruments stay recorded (naive-chord failure,
  frozen-form indefiniteness, mask-extension pitfall, C³-not-C⁴, the
  basin/stencil taxonomy) — they are part of the mathematics.
