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
- **[P/K] N11. The stationary-fan kink (CORRECTED by N12).** At a
  stationary wall fan the true area is not twice differentiable: the two
  one-sided second variations differ (measured branch ratio 0.12 at Σ,
  0.005 at Gerver's phase-1 fan). ORIGINAL READING — a "3/2-law"
  F(−ε)−F₀ ≈ −c·ε^{3/2} — was inferred from a log-slope of ≈1.6 on a
  short ε-range and is **superseded by N12**: the exact scaling is
  QUADRATIC, F_rel − F = ε²N(φ), with the non-quadratic-form coefficient
  N accounting for the apparent fractional exponent (a pre-asymptotic
  mix, not a fractional law). What survives unchanged and is load-bearing:
  the kink is one-signed FAVOURABLE, and every smooth oracle
  (jet/structure-following or fan-released) is a superset upper form
  dominating both one-sided branches — the uniform justification of the
  certified objects at both c_G and Σ.
- **[P/K] N12. THE FAN-BITE FUNCTIONAL — the object that closes the cap
  sector.** At a stationary wall fan (λ ≡ 0 on an interval of half-width
  β) every constraint line passes through ONE point P. In u = x − P the
  perturbed constraints are ⟨u, μ_s⟩ ≤ ε·φ(s) with **no constant term**,
  so the local body is EXACTLY K_ε = ε·K₁ (homogeneity; Lean:
  `fan_homogeneity`). Hence the area lost to the interior lines relative
  to the fan-released set is exactly
  **F_rel − F = ε²·N(φ), N(φ) := |W₁ \ K₁| ≥ 0**,
  positively homogeneous of degree 2 and one-signed but **not a quadratic
  form** — N(φ) ≠ N(−φ) is the exact source of the kink. Properties:
  * **(a) vanishing criterion** — N(φ) = 0 ⟺ d(s) := φ(β)cos s/cos β −
    φ(s) ≤ 0 for all s, i.e. no interior line cuts inside the wedge apex.
    So the released form is EXACT on one-signed cap perturbations
    (verified: bumps give bite 0 to machine precision).
  * **(b) elementary rigorous lower bound** (one interior cut is contained
    in the bite): N(φ) ≥ max_s [d(s)]₊²·sin2β / (2 sin(β−s) sin(β+s)).
  * **(c) all-active closed form** (when φ + φ″ ≥ 0):
    N(φ) = φ(β)² tan β + ∫₀^β (φ′² − φ²) ds — the Wirtinger form again;
    the constant case gives φ²(tan β − β), the exact area between a
    circular arc and its two tangent lines.
  * **(d) the reconciliation** Q_true = Q_rel − [N(φ) + N(−φ)].
  * **(e) at Σ**: BOTH families' fans are frozen at the SAME point
    (P_A = (1,½) for cap 1), so the fan is symmetric of half-width β with
    φ(s) = ⟨η(|s|), μ_{|s|}⟩ even; and Σ's two caps bite on OPPOSITE
    branches with equal magnitude.
  * **VALIDATED**: on the released form's worst K=24 direction,
    Q_rel = −0.201, bites 0/26.238 (cap 1) and 26.238/0 (cap 2), total
    52.476, predicted Q_true = −52.68 vs **measured −52.39 (0.55%)**.
    (`sigma_fanbite.py`.) This supersedes the empirical "3/2-law" reading
    of N11: the true scaling is exactly quadratic with a
    non-quadratic-form coefficient.
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
- **[C] S4/S7‴-e. Σ CERTIFICATION — the first rigorous interval statement
  about Σ.** (`certify_sigma_struct.py`.) Q_struct is **NEGATIVE DEFINITE
  on the K-mode span, certified in arb** (Sylvester's criterion applied to
  the ball matrix at 256 bits; **K=10 (20 modes, all 210 entries, max
  radius 2.1e-12) certified**, minors positive through order 20; definiteness is
  metric-independent so no eigenvalue enclosure is needed). Certifiable
  precisely because of the three earlier structural results: integrands
  trajectory-independent, arc ranges exactly {0, β, π/2−β, π/2}, junction
  response null. No oracle, no junction solve, no floating point in the
  chain. **By N1 this certifies that the TRUE ambidextrous functional
  strictly decreases to second order in every direction of the span.**
  **CAVEAT DISCHARGED**: β has a CLOSED FORM,
  β = arctan(((√2+1)^{1/3} − (√2−1)^{1/3})/2), so it is enclosed directly
  in ball arithmetic (radius 5.8e-90 at 300 bits) with no root-finding.
  Re-run with the exact enclosure: entry radii 1.7e-85, minors positive
  through order 20 — **the certification is UNCONDITIONAL**. The Σ analytic/Rust oracle originally
  planned here is no longer needed for certification — the closed form
  superseded it.
- **[P°] S5.** Σ weighted interior Gårding (Theorem 4, SIGMA_LOCAL §5):
  proof route complete and the statement stands — but S3's data shows it
  is VACUOUS on cap-oscillatory modes (the unweighted C₀‖η‖² slack
  dominates the weighted coverage there): true, not delivering. Kept as
  a bulk instrument; the delivering frame for the caps is the cell-wise
  L² statement (S7′).
- **[K] S4/S7‴-a. Σ's structure map and CLOSED-FORM form — BUILT AND
  VALIDATED.** (`sigma_struct_map.py`, `sigma_struct_junctions.py`,
  `sigma_qstruct_assemble.py`.) Results:
  * **Traversal**: ∂Σ is exactly 10 arcs,
    dA[π/2→b] rA[b→π/2] dB[π/2→β] dX[β→B] dD[B→0] rC[0→B] dC[B→0]
    rD[0→B] rX[B→β] rB[β→π/2] (B = π/2−β), ρ-symmetric, the doubled
    Gerver structure.
  * **Junctions**: EVERY junction sits exactly at β, π/2−β, 0 or π/2
    (Newton residuals ~1e-10). Σ has no free junction parameters at c_R
    — strictly simpler than Gerver's four.
  * **Cap law, arc-level**: the A-contact is frozen at exactly (1, ½) —
    on the mirror axis, arc speed 0 to machine precision on (0,β).
    λ_A ≡ 0 verified directly on the geometry.
  * **Validation**: Green area over the table = −1.6449552 (A_R* to
    2.6e-9); `Q[const_x, ·] ≡ 0` to 1.4e-12 (horizontal translation is
    an exact symmetry of Σ — end-to-end check of the whole assembly);
    every diagonal entry matches a direct struct-following FD oracle to
    5 digits.
  * **Key structural fact**: the per-arc integrands and chord jets are
    TRAJECTORY-INDEPENDENT; the trajectory enters only through the arc
    ranges, which are exactly {0, β, π/2−β, π/2}. So Q_struct is a
    finite sum of elementary trigonometric integrals — closed form, no
    oracle, no junction solve, directly interval-certifiable.
  * **Ladder** (d²F/dε² convention): negative definite at every K, but
    the margin decays on CAP-CONCENTRATED modes (L²: 1.21 / 0.62 / 0.035
    at K = 6/16/24; quadrature-converged to 6 digits, so real).
- **[P/K] S7‴-b. ENVELOPE IDENTITY APPLIED TO Σ — a NULL RESULT, and the
  null result is a theorem** (`sigma_envelope.py`). The hypothesis was
  that Σ's decaying cap margin is the frozen-junction defect (as at
  Gerver K=32) and that letting the 10 junction parameters respond would
  restore it. Measured and derived:
  * **The zero-chord derivative identity holds**: max |∂G/∂β| = 2.9e-7
    at c_R (the identity that makes any envelope argument possible).
  * **H_ββ has identically zero diagonal** — measured |H_jj| ≤ 3e-4
    (noise), and derived: with one junction parameter moving, the
    reconstruction area is O(δ³), because
    ∂G/∂δ = ½[P(b+δ)−P(b)]∧P′(b+δ) = ¼δ²·P′∧P″ + O(δ³).
    So the affine-junction family's β-quadratic is DEGENERATE and the
    naive "min over β" Schur complement does not even apply.
  * **Exactly ONE junction carries a cross term**: H[rC·t₁, dC·t₀] =
    −0.048, all others zero. Reason: the cross term is ½P′∧Q′, and at
    every junction joining arcs of the SAME family both velocities are
    ∥ μ (λ_C μ, λ_D μ) so the wedge vanishes — the breakpoint mechanism
    N7. It survives only at the mirror-axis junction where a ν-slot arc
    meets its own ρ-image, whose velocities are μ_t and μ_{−t}: an angle
    2t apart. **The same 2θ frame-angle that drives N9.**
  * **Net correction is negligible, CONFIRMED AT BOTH K**: relative
    ‖Q_true−Q_frz‖_F/‖Q_frz‖_F = 3.8e-6 at K=16 (4e-6 at K=6), with the
    margins unchanged to four digits — H¹ 0.006868 → 0.006868,
    L² 0.621862 → 0.621865. K=16 is precisely where the cap decay bites,
    so the test is decisive: junction response does not touch Σ's second
    variation. (The H_ββ structure is K-independent: diagonal ≤ 3e-4,
    the single mirror-axis cross term −0.0482 at every K.)
  **Conclusion: Σ's closed-form frozen structure-following form already
  IS the true second variation.** The certifiable object is the right
  object — but the decaying cap margin is therefore GENUINE, not an
  artifact, and cannot be repaired by junction response.
- **[P/K] S7‴-c. CAP SECTOR RESOLVED by the fan-bite functional N12.**
  The released form's flat directions are NOT flat for the true
  functional: the discarded interior cap walls remove exactly
  ε²·[N(φ)+N(−φ)], and on the worst K=24 released direction that is
  52.48 against a released margin of 0.20 — predicting the true value to
  0.55%. This reconciles, quantitatively, the two ladders measured
  earlier: released margins 4.58/0.91/0.20 (decaying) vs the TRUE
  Σ Hessian's L² margins 3.98/3.68/3.58 (K-STABLE) at K = 10/16/24. The
  bite is exactly the difference, and the true form's K-stability is
  therefore explained rather than merely observed.
  **S7‴-d. THE DICHOTOMY — PROVED (analytic ingredients) AND COMPUTED
  (K-uniform).** (`sigma_dichotomy.py`.) The chain, each step elementary:
  * G(s) = sin2β/(2 sin(β−s)sin(β+s)) is MINIMIZED at s = 0, because
    sin(β−s)sin(β+s) = sin²β − sin²s (Lean: `fan_cut_gain`), so
    G ≥ G(0) = cot β uniformly on the fan. **[P]**
  * The two branches cover the two signs of d, so
    N(φ) + N(−φ) ≥ max_s d(s)²G(s) ≥ cot β·‖d‖²_∞. **[P]**
    (Verified against exact N: bound/exact = 89%, 58%, 75% on test data.)
  * **d is translation-invariant**: replacing φ by φ + c·cos s leaves d
    identically unchanged, since cos s spans ker(h ↦ h+h″) — exactly the
    rigid-translation data of a fan. So the bite measures the distance of
    the cap data from the unique true null direction, and the bound
    descends to the quotient. **[P]**
  * Hence **wherever the released form degenerates the bite must pay**,
    and the total is what matters. Computed infimum of
    −Q_true = −Q_rel + Σ_caps bites over the p least-negative released
    directions (search restriction certified safe by the spectral gap:
    λ_{p+1} = 457 / 285 / 146 ≫ the minimum ≈ 10):

    | K  | released margin alone | **TOTAL (dichotomy)** | bite share |
    |----|----------------------|-----------------------|------------|
    | 10 | 8.116                | **11.06**             | 20.7%      |
    | 16 | 1.295                | **10.47**             | 26.6%      |
    | 24 | 0.239                | **10.00**             | 32.1%      |

    The released margin collapses by a factor 34 while the TOTAL is
    K-STABLE at ≈ 10 (decrements 0.59, 0.47 — extrapolating to ≈ 9),
    and the bite's share grows monotonically 21% → 27% → 32%: the
    dichotomy operating exactly as designed. Stable in p (p = 6 and
    p = 10 agree to 0.5%).
  * **Note on the earlier "true ladder margin 3.5"**: that was the min
    eigenvalue of a matrix built by POLARIZING a non-quadratic functional,
    hence not the functional's infimum. The honest object is the
    directional infimum computed here.
- **[✗→P] S7‴ (supersedes S7″ — the corrected object).** The fan release
  FAILED as sole certified object: released-ladder margins collapse
  (L²: 4.58/0.91/0.20; weighted E_w: 0.136/0.0062/0.0013 at K=10/16/24;
  direct-probe-verified −0.77 → −0.039 on the worst spans). Mechanism:
  releasing the cap fans deletes ALL μ-slot constraints there, leaving
  t→0-concentrating x-bumps coupled only through cancelable terms —
  the flat-direction family is genuine. THE CORRECTION: the certified
  object is the **STRUCTURE-FOLLOWING form Q_struct** — keep every fan
  wall as an envelope-following contact arc (the Gerver jet-oracle
  pattern, verified smooth & symmetric there): its Wirtinger sum
  includes the stationary A-arc's p-form over the cap interval =
  full-strength μ-coverage, NO sin² suppression ⟹ uniform H¹ Gårding,
  plain-H¹ ladder + Part-II weld verbatim. Q_struct is superset-valid
  (arcs are constraint-boundary arcs; equality at c_R), smooth (envelope
  formulas analytic in the jets), and assembles in CLOSED FORM (the
  qfrz Σ-port — no junction solving, directly certifiable). The release
  detour's yield stands: N11 (fan-bite 3/2-law), the flat-direction
  discovery (proving the A-arc terms are load-bearing), Lemma 7a
  (ν-slot bookkeeping), criticality/domination checks.
- **[archived] S7″ (fan release).** Valid inequalities (F ≤ F_rel with
  equality at c_R verified 2·10⁻¹⁰; C², fwd/bwd = 1.0000; Lean core
  `fan_combination` stands; ladders in `sigma_rel_K{K}.npy`) but NOT
  uniformly coercive — kept as a lemma family, not the theorem vehicle.
- **[~] S7′ (superseded by S7″).** Cell-wise branch enumeration — kept
  as the fallback/refinement frame (branch data: −9/−43 per unit L²
  along the worst mode; FD-average m_L² ≈ 3.5).
- **[ ] S6.** Σ tail weld (weighted analogues of the Part-II items).
- **[ ] S7. Σ-LOCAL — STILL OPEN, gap now named.** Theorem 9 is assembled
  in SIGMA_LOCAL.md §9 with a 12-row input ledger. Items 1–11 are done
  (two independent routes: the CERTIFIED Q_struct < 0, and the dichotomy
  with K-stable constant ≈ 10). **Item 12 — the tail/weld from the K-mode
  span to all of L² — is NOT done.** Until it is, what exists is a
  statement about finite-dimensional subspaces, not a local-maximality
  theorem. The remaining gap is one named, standard-shaped estimate (the
  Σ analogue of Part II's weld: far-tail Schur bound N8 + block coupling),
  not a structural unknown.

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

## BUG FOUND AND FIXED (2026-07-29): corner-term polarization

The corner-path contribution to the second variation is the wedge
η_u ∧ η_v′, whose symmetric polarization is ¼·E_ij·(W_ij − W_ji) with
W_ij = ∫s_i s_j′ and E antisymmetric. **All three implementations used the
SUM (W_ij + W_ji) instead of the difference.** Effects:
* the Python assembler's corner term came out ANTISYMMETRIC and silently
  vanished under symmetrization;
* the Rust port made it symmetric and wrongly kept it;
* the arb certification inherited the same wrong integrand.
Only the xy (cross-component) block is affected — E vanishes on the
diagonal and within each component block, which is exactly why the
5-digit FD-oracle validation (diagonal entries only) passed it.
**Found by cross-checking the Rust port against Python** — the two
disagreed by 1.8 in the xy block while agreeing to 2e-12 elsewhere.
Fixed in `sigma_qstruct_assemble.py`, `sigma_struct.rs`,
`certify_sigma_struct.py`; Rust and Python now agree to 3.8e-12.
CORRECTED margins are STRONGER: L² 2.336 / 1.173 / 0.0357 at K = 6/16/24
(was 1.211 / 0.622 / 0.0354). All definiteness verdicts stand; the
certification was re-run with the corrected integrand.

**Lesson recorded**: the validation that passed this bug tested only
diagonal entries. Cross-component terms need their own check — an
independent reimplementation caught what the oracle comparison could not.

## Rust port (compute discipline, honoring the standing instruction)

`sigma_struct.rs` (pure std, no crates): the closed-form assembler in
Rust — **0.5 s for K = 32/48/64**, versus a Python geometry probe that
needed ~90 minutes and was killed. The one O(n³) step (eigenvalues) goes
to LAPACK via a thin front-end (`sigma_spec.py`), which is Fortran/C, not
Python. What remains Python: the shapely TRUE-area oracle (the actual
bottleneck all session, and the cause of the OOM) — porting it needs
polygon booleans and is scoped, not yet done.

## HIGH-K TAIL FINDING (`sigma_struct.rs` scan)

| K  | Q_struct L² margin | H¹ margin |
|----|--------------------|-----------|
| 16 | 1.17               | 6.9e-3    |
| 24 | 3.6e-2             | 2.0e-4    |
| 32 | 8.1e-4             | 4.0e-6    |
| 48 | < 1e-6 (f64 floor) | < 1e-6    |
| 64 | < 1e-6 (f64 floor) | < 1e-6    |

**Q_struct's margin collapses below f64 resolution by K ≈ 48.** Two
consequences, both load-bearing: (i) the certified Sylvester route on
Q_struct cannot be pushed much past K ≈ 32 without extended precision,
and (ii) more importantly it can NEVER supply a uniform constant — so
**item 12 must go through the dichotomy (Q_rel + fan bite), not through
Q_struct.** That settles the architecture question for the tail.

## Compute discipline (post-OOM, 2026-07-29)

A machine OOM killed all running computations (three concurrent Python
geometry processes + system load on 24 GB). Losses: the y-ray sweep's
in-progress results (log-only; needs rerun) and /tmp logs. Survived: all
checkpoints (sigma_rel_K24.npy at 20/48 rows — resumed). NEW RULES:
one heavy computation at a time, nice'd, with an RSS guard (3 GB) and a
system-memory floor (1.5 GB reclaimable) enforced by the monitor; heavy
runs must checkpoint (all current ones do). Queue: K=24 released
(running) → y-ray sweep rerun → K=32 released if wanted.

## Standing discipline

- Every new claim enters this ledger with a status tag before it enters the
  manuscript.
- No status upgrades without the artifact (proof text, arb log, or
  cross-validated computation) committed to the repository.
- Negative results and dead instruments stay recorded (naive-chord failure,
  frozen-form indefiniteness, mask-extension pitfall, C³-not-C⁴, the
  basin/stencil taxonomy) — they are part of the mathematics.
