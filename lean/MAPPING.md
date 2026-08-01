# Paper ↔ Lean mapping

Required by Rule 5.  Every declaration below is in `MovingSofa/Basic.lean`.
`lake build` is clean, there is no `sorry` anywhere in the file, and
`#print axioms` reports nothing beyond `propext` and `Quot.sound`, except for exactly two
declarations, `strip_covers_iff` and `cone_nu_iff`, which also use `Classical.choice`.
That list was checked by running `#print axioms` over every theorem in the file, not by
inspection.  Two earlier versions of this note were wrong about it: one claimed no
`Classical.choice` anywhere, the next named only `strip_covers_iff`.

Toolchain: Lean 4.30, no Mathlib.  Trigonometric quantities are carried as
formal symbols under Pythagorean side conditions, and arithmetic is over `Int`
so that the identities stay decidable; the instantiation of the symbols at actual
sines and cosines is a separate Mathlib-track item and is NOT claimed here.

(The `Line` column is indicative only and rots as the file grows; `grep` the declaration
name for the current position.)

| Lean declaration | Line | Paper / PROGRAM item | Statement | Axioms |
|---|---|---|---|---|
| `famInter_antitone` | 90 | N1a | keeping fewer constraints enlarges the intersection | none |
| `superset_principle` | 97 | N1b, F1 | the full intersection sits inside every subfamily intersection | none |
| `area_bound` | 104 | N1c | monotone-area corollary of `superset_principle` | none |
| `safe_closure` | 124 | N1e, G2 | body inside every assembled piece ⟹ body inside their intersection; the hypothesis `lem:superset` needs and omitted | none |
| `certified_upper_envelope` | 133 | N1d | per-ε subfamily choice bounds the true area at every ε simultaneously | none |
| `stationary_contact` | 177 | F3a, N4 | the speed operator `v ↦ v + v''` collapses to the constant term on trigonometric phases | — |
| `lamA_const` | 187 | F3a | λ_A is constant on trigonometric arcs | — |
| `lamA_zero_iff` | 194 | F3a | λ_A ≡ 0 exactly on SOL1-form arcs (the cap degeneracy) | — |
| `lamD_const` | 209 | F3a | λ_D is constant on trigonometric arcs | — |
| `psum_strict_mono` | 231 | F4a | positive steps give strictly increasing partial sums | — |
| `chain_injective` | 248 | F4a | monotone chains are injective (ray simplicity) | — |
| `fan_combination_x` | 268 | F4b | the interior-fan combination identity, x component | — |
| `fan_combination_y` | 285 | F4b | same, y component | — |
| `nu_slot_collapse` | 315 | F4c | the ν-slot tail-closing identity | — |
| `fan_homogeneity` | 355 | F4d, N12 | the fan-bite functional is exactly ε²-homogeneous | — |
| `fan_cut_gain` | 379 | F4e | the single-cut gain factor is bounded by its value at the fan centre | — |
| `exact_degree` | 432 | F2a, N2 | exact-degree reduction | — |
| `frame_pair_identity` | 450 | F3b, N9 | the ambidextrous frame-pair Gram identity | — |
| `frame_pair_coercive` | 465 | F3b, N9 | frame-pair coercivity with modulus 2·min(sin²θ, cos²θ) | — |
| `chord_sliver` | 524 | F6a, G1 | the sliver between the wall line and a departing chord has twice-area `l·h`: the `-(l/2)h` term of the rank-one defect | propext |
| `bowtie_signed_zero` | 531 | F6b, S6 | a self-intersecting closed quadrilateral has signed shoelace 0 | none |
| `square_signed` | 539 | F6c, S6 | the same vertices traversed simply give twice-area 2 — signed area ≠ region area | none |
| `selection_rule` | 550 | F6d, M1 | a `T`-invariant form vanishes between opposite-sign eigenvectors of an involution | propext, Quot.sound |
| `ueig_opposite` | 564 | F6e, M1 | modes in different grading classes have opposite `U`-eigenvalue | propext |
| `grading_selection` | 575 | F6f, M1 | hence a `U`-invariant form vanishes between them (the Z2 block-diagonalisation) | propext, Quot.sound |
| `intersection_chain` | 592 | F7a, S8 | dominance + margin + slack ⟹ `atrue ≤ astar + s - m` | propext, Quot.sound |
| `slack_squeeze` | 601 | F7b, S8 | `x ≤ y + s_n` for all n with some `s_n ≤ 0` ⟹ `x ≤ y` | propext, Quot.sound |
| `sq_nonneg_int` | 618 | F8 | `0 ≤ x*x` | propext |
| `weighted_sq_nonneg` | 626 | F8 | `0 ≤ d*x²` for `d > 0` | propext |
| `weighted_sq_pos` | 630 | F8 | `0 < d*x²` for `d > 0`, `x ≠ 0` | propext |
| `sum_nonneg` | 640 | F8 | non-negative entries ⟹ non-negative sum | propext, Quot.sound |
| `niche_below_apex` | 690 | F9a, A1 | a wedge point lies at or below its apex (ambidextrous transfer) | propext, Quot.sound |
| `niche_disjoint` | 700 | F9b, A2 | `y ≤ M` and `H−M ≤ y` with `2M < H` is contradictory: the two niches are disjoint | propext, Quot.sound |
| `union_area_of_disjoint` | 707 | F9c, A4 | disjointness collapses inclusion–exclusion | propext, Quot.sound |
| `sol6_bracket` | 726 | F11, B6 | `D(Dv) = -(v+1)` for half-angle arcs of constant term `-1`: the identity behind ODE6 | none |
| `sol6_ode` | 740 | F11 | same, with the constant term as a hypothesis | none |
| `wedge_gap` | 770 | F12 | the two angular spans at a ρ-fixed apex miss by `2t` | propext, Quot.sound |
| `wedge_gap_width` | 776 | F12 | the gap width is exactly `2t` | propext, Quot.sound |
| `strip_covers_iff` | 800 | F13, S1b | the cones cover the line iff `E ≤ PY - 1`, i.e. iff `ε ≤ (2p_y-1)/(2 tan t₀)` | propext, **Classical.choice**, Quot.sound |
| `no_cover_below_half` | 810 | F13b | `p_y ≤ 1/2` ⟹ a gap at every distance: the threshold is exactly `1/2` | propext, Quot.sound |
| `connectedness_ceiling` | 820 | F13c, S1b | no omitted strip ⟹ `p_y ≤ 1/2` | propext, Quot.sound |
| `sum_pos_of_one_pos` | 656 | F8 | non-negative entries with one positive ⟹ positive sum: certificate ⟹ strict definiteness | propext, Quot.sound |

## What is NOT formalized, and why

Recorded so the VERIFIED label is not read as covering more than it does.

* **`lem:superset` as used in the paper.**  `superset_principle` proves only the
  constraint-dropping statement.  The chorded version the paper consumed is
  FALSE without the supporting-line hypothesis; `safe_closure` is the corrected
  form.  See `rem:chord-gap` and `rem:chord-hypothesis`.
* **The rank-one law G1 itself.**  `chord_sliver` formalizes the area identity
  behind it; the full statement `δA_rec = -(ℓ/2)(η_x'(0)+η_x'(π/2))` needs
  Green's theorem for piecewise-C¹ curves and the first variation of an area
  functional, neither available without Mathlib.  Label stays PROVED.
* **Mode 2 in general.**  `bowtie_signed_zero` / `square_signed` exhibit
  signed ≠ region on the minimal instance.  The general statement (signed area
  equals region area iff the curve is simple) needs the Jordan curve theorem and
  is not attempted.
* **The corner criterion G8.**  The reduction
  `q ∈ Q_t ⟺ arg(q-c(t)) - t ∈ (π, 3π/2)` is elementary but needs `arg` and the
  rotation identity over `ℝ`; with trig carried as formal symbols the useful
  content would be the norm-preservation of the frame map, which requires ring
  normalisation of a degree-4 identity and is not available in core Lean.
  Label stays PROVED for the reduction, HEURISTIC for the coverage margin.
* **Every numerical margin.**  Ladder eigenvalues, containment margins and symbol
  minima are HEURISTIC by Rule 7.  `sum_pos_of_one_pos` supplies the LAST step of a
  definiteness argument (certificate ⟹ strict definiteness); what is missing is the
  CERTIFICATE, in exact arithmetic.  The entries are currently central differences
  of a floating-point polygon area, so there is no rigorous enclosure for a Lean
  proof to consume: the FD truncation error is `O(ε²·M₄)` with `M₄` unknown, and the
  polygon vertices involve `cos`/`sin` of grid angles so exact rationals are not
  available either.  The route with precedent in this project is
  `certify_sigma_struct.py` (closed-form assembly, arb at 300 bits, Sylvester
  minors); for `|R_n|` it is available via N10, since on each combinatorial cell the
  polygon area is a polynomial.  Until that certificate exists these stay HEURISTIC.

## F14, F15, F16 — blocks that had no table row

| Statement | Lean declaration | Status |
|---|---|---|
| SOL1's `μ`-speed is `2a₁ sin t + ½cos t − ½`, constant-free, and vanishes at `t=0` | `Trig.sol1_speed_mu`, `sol1_speed_const`, `sol1_speed_vanishes` | VERIFIED |
| `u² = x` and `u(x+3) = 2` give `x(x+3)² = 4` (step 2 of the T3 proof) | `u_sq_cubic` | VERIFIED |
| the Cardano substitution as a polynomial identity, and its vanishing on the cubic | `cardano_substitution`, `cardano_vanishes` | VERIFIED |
| the `ν`-half of cone membership is `y·C < p_y·C − ε·S`, and the `μ`-half is then automatic | `cone_nu_iff`, `cone_mu_of_nu` | VERIFIED |
| a concave function with a nonpositive derivative attains its max; a subtracted square is concave; the far endpoint of a segment | `concave_critical_global`, `concavity_of_subtracted_square`, `segment_far_endpoint` | VERIFIED |

`cone_nu_iff` is one of the two declarations using `Classical.choice`.

## F23 — the boundary term of the first variation (note §9, Theorem "δQ(Σ)=0")

| Statement (note) | Lean declaration | Status |
|---|---|---|
| in doubled units the reflection is `y ↦ 2−y`, so a `ρ`-fixed height is `1`, i.e. `½` | `rho_fixed_height` | VERIFIED |
| the leftmost boundary point has height `−H'(π)`; `ρ`-fixedness forces `H'(π) = −½`, so the coefficient `2H'(π)+1` of `η(π)` vanishes | `boundary_term_vanishes` | VERIFIED |
| the same at `θ=0` gives `H'(0) = ½` | `right_extreme_height` | VERIFIED |
| both extreme points of the cap sit at the same height | `extremes_same_height` | VERIFIED |

Axioms `[propext, Quot.sound]`.  NOT formalized: that the boundary point with outer normal
`μ_θ` is `H(θ)μ_θ + H'(θ)ν_θ`, and that the extreme point is unique — both are geometry.

## F32 — the extremal cross-section (note, Prop "The extremal configuration")

| Statement (note) | Lean declaration | Status |
|---|---|---|
| the extremal profile `4−4\|s−√2/2\|` integrates to `4√2−2` over the band | `extremal_integral` | VERIFIED |
| half of it is `2√2−1` | `half_is_bound` | VERIFIED |
| the crude bound `ℓ ≤ 4` gives Hammersley's `2√2`, a gap of exactly 1 | `crude_is_hammersley` | VERIFIED |

Axioms `[propext, Quot.sound]`.  NOT formalized: the coordinate reduction of Lemma "uv",
the piecewise-linear structure of the cross-section, and the conjecture that no placement
exceeds the extremal value.

## F31 — the cap constant (note, Lemma "Cap lemma")

| Statement (note) | Lean declaration | Status |
|---|---|---|
| the strip retains `sqrt2 - 1/2` of the rotated unit square (cleared by 4) | `cap_area` | VERIFIED |
| twice the cap is `2 sqrt2 - 1` | `two_caps` | VERIFIED |
| the second handedness removes exactly 1 from Hammersley's `2 sqrt2` | `hammersley_gap` | VERIFIED |

Axioms `[propext, Quot.sound]`.  NOT formalized: the integration giving the cap area, the
identification of the perpendicular arm pairs with rotated unit squares, and the
conjecture that the two parallel pairs cannot add.

## F30 — the arm sandwich and the disc counterexample (note, Lemma "arm sandwich", Remark "disc")

| Statement (note) | Lean declaration | Status |
|---|---|---|
| `α₂ ≤ α₁' ≤ α₂+1` from the two-sided curvature bound | `arm1_sandwich` | VERIFIED |
| `−α₁−1 ≤ α₂' ≤ −α₁` | `arm2_sandwich` | VERIFIED |
| the disc `1−c+c(sin+cos)` has curvature density `1−c` identically | `disc_curvature` | VERIFIED |

Axioms `[propext, Quot.sound]`.  The sandwich supplies the proved Lipschitz constant of
the explicit-ball proposition and both transversality statements.  NOT formalized: the
a.c./atom bookkeeping and the grid evaluations.

## F29 — the anchored-cell reduction and the corner constants (note, Thm "Diagonal concavity")

| Statement (note) | Lean declaration | Status |
|---|---|---|
| Lemma M: `B − w² ≤ B` — dropping the `(q−p')²` term dominates every ordered cell by a diagonal cell | `cell_mono` | VERIFIED |
| small-τ collection: `(−3+2+1)E + (3t²−1)R ≤ 0` for `3t² ≤ 1`, `E,R ≥ 0` | `small_tau_collect` | VERIFIED |
| corner `P²`-coefficient `−174+125+36 < 0` (scaled by 100) | `corner_P_coeff` | VERIFIED |
| corner `D`-coefficient `98−21π ≥ 32` given `7π ≤ 22` | `corner_D_coeff` | VERIFIED |
| corner `r`-coupling, cleared form `550 ≤ 576` | `corner_r_coupling` | VERIFIED |

Axioms `[propext, Quot.sound]`.  NOT formalized: the Poincaré inequalities, the
Dirichlet–Neumann eigenbasis expansion, the transfer-matrix representation, and the
interval covering (305 + 249 boxes, `ambi_anchored.py`).

## F28 — the coupling is a total derivative (note, Thm "The sharp constant")

| Statement (note) | Lean declaration | Status |
|---|---|---|
| `2p²−2P²+q²−R²−(p+R)²+(q−P)² = p²−P²+2q²−2R²−2pR−2qP` — the integrand on `E₁∩E₂` | `overlap_integrand` | VERIFIED |
| given the product rule `Dpq = pR+qP`, the two cross terms equal `−2·Dpq`: a total derivative | `cross_is_total_derivative` | VERIFIED |
| with `p(0)=0` the telescoped integral is the single value `2p(β)q(β)` | `telescope_gauge` | VERIFIED |

Axioms `[propext, Quot.sound]`.  This is why the sharp constant is reachable: on the
overlap of `E₁` and `E₂`, where the obstruction lives, the coupling contributes only a
boundary value, so it is not a pointwise cost and no pointwise splitting is needed.  NOT
formalized: the product rule itself (core Lean has no derivative), the Euler-Lagrange
system, the `4×4` matrix exponential, and the interval covering of `[2/3, 73/100]`.

## F27 — the two Cauchy-Schwarz steps of the sharp constant (note, Thm "Concavity, sharp order")

| Statement (note) | Lean declaration | Status |
|---|---|---|
| `M·(P a² + 2K ab + M b²) = (Ka + Mb)²` when `MP = K²` — the `E₂` completion behind `−(a+b)² ≤ −λb² + (λ/(1−λ))a²` | `e2_completion` | VERIFIED |
| `n(m+n)x² + m(m+n)y² − mn(x−y)² = (nx + my)²` — the `E₁` split `(x−y)² ≤ (1+1/κ)x² + (1+κ)y²` at `κ = m/n`, with no side condition | `e1_split` | VERIFIED |
| `M > 0` and `M·F = S²` ⟹ `F ≥ 0`: dividing the weight back out | `form_nonneg_of_completion` | VERIFIED |

Axioms `[propext, Quot.sound]`; `form_nonneg_of_completion` needs only `propext`.  These
are the two steps that decouple the halves of `[0,π]`, reducing the second variation to
two Sturm-Liouville eigenvalue problems and lifting the certified constant from `0.1532`
to `2/3` against a sharp `0.7323`.  NOT formalized: the Sturm oscillation theorem, the
transfer-matrix representation, and the sign evaluations `Φ_L(2/3), Φ_R(2/3) > 0`.

## F26 — the sigma term has no singularity (note, Prop "$H^1$ stability")

| Statement (note) | Lean declaration | Status |
|---|---|---|
| `sec² − tan² = 1`, cleared of denominators against `C²+S²=1` | `sec_sq_sub_tan_sq` | VERIFIED |
| the two unbounded pieces of the σ integrand cancel, leaving `η²−η′²` | `sigma_term_bounded` | VERIFIED |

The integration by parts `−2∫ηη′tan t = ∫η²sec²t` is analysis and is not formalized.

## F25 — the segment argument (note, Proposition "Beyond Sigma's own cell")

| Statement (note) | Lean declaration | Status |
|---|---|---|
| non-positive second difference ⟹ slopes non-increasing | `second_diff_nonpos_mono` | VERIFIED |
| + first slope `≤ 0` ⟹ the function never exceeds its starting value | `concave_along_segment` | VERIFIED |
| the case used: first slope `= 0`, from `δQ(Σ) = 0` | `concave_from_critical` | VERIFIED |

## F24 — the support-point coordinates (note §9)

| Statement (note) | Lean declaration | Status |
|---|---|---|
| at `θ=π`, `(C,S)=(-1,0)`, the boundary point is `(-H,-D)`, height `-H'(π)` | `support_point_at_pi` | VERIFIED |
| at `θ=0` it is `(H,D)`, height `H'(0)` | `support_point_at_zero` | VERIFIED |
| the whole chain: height at `π` is `-D`, `ρ`-fixedness gives `D=-1`, so `2H'(π)+1` vanishes | `boundary_chain` | VERIFIED |

NOT formalizable in core Lean: the parametrisation `p(θ) = H(θ)μ_θ + H'(θ)ν_θ` of the
boundary point, and the uniqueness of the extreme point.  Both are geometry rather than
`Int` arithmetic, and both are used by the note without proof.

## F17 — the niche functional in convex-linear data (note §8, P3c)

| Statement (note) | Lean declaration | Status |
|---|---|---|
| Prop "Niche area in convex-linear data", the arm integral `∫_{α⁺}^{σ}(s-α)ds = ½(σ-α)² - ½(α⁻)²`, negative branch | `arm_integral_neg` | VERIFIED |
| same, non-negative branch (clamp kills the subtracted term) | `arm_integral_pos` | VERIFIED |
| Lemma "Normal velocities": each face advances on one side of its OWN envelope point | `face_advance_sign` | VERIFIED |
| the face-1 sweep is nonempty under a condition on `σ, α₁` alone — the repair of the reported injectivity failure | `face1_nonempty` | VERIFIED |
| `2(p²+q²) ≥ (p+q)²` | `two_sq_add_sq` | VERIFIED |
| `(a+b)⁺ ≤ a⁺ + b⁺` | `pp_add_le` | VERIFIED |
| midpoint convexity of `x ↦ (x⁺)²`, the property making the first two terms convex quadratics | `posPart_sq_midpoint_convex` | VERIFIED |

`#print axioms` on all seven: `[propext, Quot.sound]` only.  What is NOT formalized,
and is the substance of the proposition: that the two sweeps are disjoint, injective,
and cover the niche.  Those are measured, not proved — see the note's Remark "What is
measured, and what it gives".  Nor is the convex-linearity of `α₁, α₂, σ` in `h`
formalized; it is an affine-algebra statement about \(h\mapsto c(t)\) that needs real
analysis, not `Int`.

## F18 — cap form, principal symbol, outer-arm monotonicity (note §9)

| Statement (note) | Lean declaration | Status |
|---|---|---|
| the two-branch expansion behind `\|C2\| = ∫(H²−H′²) − H(0) − H(π)` | `cap_branch_sum` | VERIFIED |
| the principal symbol is `≤ −1` for every admissible indicator choice, given `E₁ ⊆ [0,π/2]` | `principal_symbol_neg` | VERIFIED |
| `4a₁ sin β = 1` with `a₁ > ½` forces `sin β < ½`, i.e. `β < π/6` (scaled to `Int` by a common denominator) | `beta_below_pi_over_six` | VERIFIED |
| `cos²t·x′ = ½ − sin t > 0` on the first phase | `phase1_increasing` | VERIFIED |
| `cos²t·x′ = ½(1 − sin t) ≥ 0` on the last phase | `phase3_increasing` | VERIFIED |
| the sweep endpoint equals the right end of the floor facet | `facet_tangency` | VERIFIED |

`#print axioms` on all six: `[propext, Quot.sound]`.  NOT formalized: the analysis behind
the cap identity (that `⟨h″,h⟩ = −∫h′²` with no boundary terms, the circle having none);
the middle-phase positivity `W > 0`, which core Lean cannot express; and
Proposition "V over-estimates the niche", whose proof is Reynolds' transport theorem.

## F19 — the curvature condition (RC) (note §10)

| Statement (note) | Lean declaration | Status |
|---|---|---|
| `n'' = -n + 1 - (G+G'')` from `⟨c(t),ν_t'⟩ = n + G - 1` | `curvature_substitution` | VERIFIED |
| the `α₂` cancellation giving `Φ'' + Φ = R` | `phi_ode` | VERIFIED |
| a sum of products of nonnegative kernel and forcing is nonnegative (Riemann-sum shadow of `Φ = ∫ sin(τ-u)R du ≥ 0`) | `kernel_sum_nonneg` | VERIFIED |
| (RC) cuts out a convex set: `a·X + b·Y ≤ (a+b)·D` for `a,b ≥ 0` | `rc_convex` | VERIFIED |

Axioms: `[propext, Quot.sound]`; `kernel_sum_nonneg` needs only `propext`.  NOT formalized:
that the integral representation solves the oscillator, and that the facet atom at
`θ = π/2` contributes nothing because it sits where the kernel vanishes.  Both are
analysis, not `Int` arithmetic.

## F20 — the cross condition and the completion identity (note §11)

| Statement (note) | Lean declaration | Status |
|---|---|---|
| interior to the face-2 segment forces `s1 ≤ 0`, below the face-1 segment | `cross_excl_face2` | VERIFIED |
| interior to the face-1 segment forces `s2 ≤ 0`, outside `[0,α₂]` | `cross_excl_face1` | VERIFIED |
| `-p²-(qT+p)²+(r-p)² = -(p+qT+r)²+2r²+2qTr` | `completion_identity` | VERIFIED |

Axioms: `[propext, Quot.sound]`.  NOT formalized: the two geometric identities for `s1`,
`s2` (they need plane geometry), and the Poincaré inequalities of the Gårding step.

## F21 — the oscillator positivity, discretely (note §12)

| Statement (note) | Lean declaration | Status |
|---|---|---|
| non-negative second difference + equal first two terms ⟹ non-decreasing | `second_diff_mono` | VERIFIED |
| `Φ₀ = Φ₁ = 0` and second difference `≥ 0` ⟹ `Φₙ ≥ 0` — the discrete shadow of `Φ = ∫ sin(τ-u)R du ≥ 0` | `discrete_osc_nonneg` | VERIFIED |
| a sum of (non-positive coefficient) × (non-negative quantity) is `≤ 0`, the Gårding assembly | `garding_sum_nonpos` | VERIFIED |

Axioms `[propext, Quot.sound]`; `garding_sum_nonpos` needs only `propext`.  `discrete_osc_nonneg`
is the honest formal content of the step F19 left to analysis: core Lean has no integration,
but the discrete implication is the same statement on a grid.  Still NOT formalized: the
Poincaré inequalities, and that the continuum ODE has the stated integral representation.

## F22 — (RC) on the half-angle blocks (note §13)

| Statement (note) | Lean declaration | Status |
|---|---|---|
| `(x±y)²` expansions with `x, y` as atoms | `sq_add_int`, `sq_sub_int` | VERIFIED |
| Lagrange: `(a²+b²)(c²+s²) − (ac+bs)² = (as−bc)²` | `lagrange_identity` | VERIFIED |
| `c²+s² = 1` and `9(a²+b²) ≤ 16` ⟹ `9(ac+bs)² ≤ 16` — (RC) on the half-angle block, from the coefficients alone | `rc_block` | VERIFIED |

Axioms `[propext, Quot.sound]`.  This is why (RC) for `Σ` reduces to `f₁²(4−2√2) ≤ 16/9`
with no information about `t`.

## Declarations with no table row

`SetP`, `famInter`, `fullInter`, `psum`, `pp`, `D`, `L`, `const`, `lamA`, `lamD`, `ueig`,
`shoe3`, `shoe4`, `neg_add_one`, `pp_nonneg` are definitions or one-line helpers used
inside the proofs above; they carry no independent mathematical content and are
deliberately not mapped.  Every *theorem* in `Basic.lean` is either in a table above or is
such a helper.

## F33 / F34 — the unconditional upper bound (now over the reals, in `Bound.lean`)

These were first written over `Int` and in a hand-built `Z[sqrt 2]`, because `Basic.lean`
is Mathlib-free and those were the only faithful models available. The project now depends
on Mathlib, so they are stated over the reals in `MovingSofa/Bound.lean`, where they are
the mathematics rather than models of it; the `Int` spellings were deleted rather than kept
alongside. Declaration names below are the real ones.

| Paper | Lean declaration | Note |
|---|---|---|
| Lemma "four pieces" (`lem:fourpiece`) | `four_piece` (ℝ) | the decomposition, over a linear order; `Int` is a faithful and non-vacuous model |
| same, sign-restricted case | `four_piece_no_cross` | both cross pieces empty |
| Lemma "both offsets positive" (`lem:bothpos`) | `both_positive_absorbed` | the containment `B ⊆ A ∪ D` that makes the case need no new estimate |
| length of `A ∩ I` | `low_end_le` | `2 − \|p−r\|` |
| length of `D ∩ I` | `high_end_le` | `2 − \|q−w\|` |
| Proposition "profile" (`prop:gfun`), maximum | `profile_ge_one`, `gMid_le` | `x²+(√2−x)² ≥ 1` over ℝ, via `(2x−√2)² ≥ 0` |
| non-vacuity of the ring (rule I6) | `gMid_at_half` | the maximum is attained, so the bound is sharp |
| the maximiser | `gMid_eq_max_iff` | the maximiser is exactly `x = √2/2`, uniquely |
| `g(1/√2) = 2√2 − 1` | `wide_case_le`, `sqrt_two_lt_bound` | case 1 of the unconditional theorem |
| the two profiles halved | `romik_lt_bound`, `bound_lt_gerver` | the bracket `1.6449552 < 2√2−1 < 2.2195316` |

Historical note (rule I6): before Mathlib, the profile identity was carried in a
hand-built ℤ[√2] rather than as an `Int` hypothesis `S*S = 2`, because that hypothesis has
no integer witness and every theorem under it would be vacuously true. Over ℝ the issue
does not arise.

What is NOT formalised: the integrals, the second variation, and the ball-arithmetic
certificates. Those need real analysis and are out of reach without Mathlib; their label
stays PROVED, never VERIFIED.

## Tooling note

Core Lean 4.30 (no Mathlib) has no `ring` and no `positivity`, but it does have `grind`,
which closes the degree-2 `Z[sqrt 2]` component identities that `simp`+`omega` cannot.
Unfolding must go through the raw operations (`add`, `mul`, `sub`) rather than typeclass
instances: routing through `HMul.hMul`/`Mul.mul` makes `simp` loop on `mul.eq_1`.

Core Lean (no Mathlib) has no `ring` and no `positivity`.  Degree-2 identities go
through with `simp [Int.add_mul, Int.mul_add, Int.mul_comm]` followed by `omega`;
degree-4 identities (such as the 2×2 Sylvester identity) do not, which is why F8
formalizes the logic of a certificate rather than the algebra that produces one.

## The profile integral (`Integral.lean`) — VERIFIED

| Paper | Lean declaration | Note |
|---|---|---|
| `prop:gfun`, the bound | `integral_tent_le` | `∫₀^√2 (2−2\|s−x\|)⁺ ds ≤ 2√2−1` for every `x` |
| `prop:extremal`, attainment | `integral_tent_at_mid` | equality at `x = √2/2`, so the constant is the supremum |
| the reduction | `half_le_integral_cap` | `∫₀^√2 min(\|s−x\|,1) ds ≥ 1/2` — the whole content |
| the truncation identity | `tent_eq`, `tent_eq_cap` | `(2−2\|s−x\|)⁺ = 2 − 2·min(\|s−x\|,1)` |
| the pairing | `cap_pair` | `min(\|s−x\|,1) + min(\|s+√2/2−x\|,1) ≥ √2/2` |
| subadditivity | `min_add_le` | `min(a+b,1) ≤ min(a,1)+min(b,1)` |

The Lean proof is shorter than the note's, and deliberately so. The note computes `g` in
closed form on four ranges of `x`; Lean avoids all four by using `max 0 y = y + max 0 (−y)`
to turn the truncation into a correction term, after which the statement is a single
pairing inequality with no case analysis anywhere. This is worth carrying back into the
note, and has been.

Still PROVED and not VERIFIED: the second variation (`thm:system`) and the ball-arithmetic
covering for region (iv) of `lem:profineq`. Those need certified numerics inside Lean, not
just Mathlib.

## Verified interval arithmetic (`Interval.lean`) — the layer, not yet the covering

| Purpose | Lean declaration |
|---|---|
| interval with rational endpoints | `Iv`, `Iv.Mem` |
| exact point, add, neg, sub | `pt_sound`, `add_sound`, `neg_sound`, `sub_sound` |
| scaling by a nonnegative rational | `smulNonneg_sound` |
| min, max, abs | `min_sound`, `max_sound`, `abs_sound` |
| the decidable positivity test | `posBelow_sound` |
| enclosure of √2 | `sqrt2I_sound`, checked against `√2² = 2` |

Rational endpoints, so no rounding argument is needed anywhere; irrational constants enter
only through provably-sound enclosures. Every operation carries a one-directional
containment theorem, so an empty interval is harmless.

**What this does NOT yet do.** It is the arithmetic layer only. Region (iv) of
`lem:profineq` still needs (a) the reduction of the region to a finite set of boxes and
(b) a verified evaluation of the integrand enclosure on each. Neither is written. The label
on region (iv), and on the second variation, remains PROVED and not VERIFIED, and the note
says so.

## Lemma E without a covering (`LemmaE.lean`)

| Paper | Lean declaration | Status |
|---|---|---|
| the assembly of `lem:profineq` | `lemmaE_of` | VERIFIED, with L1/L3/L4 as hypotheses |
| `C ≥ 1/2`, restated | `half_le_Cfun` | VERIFIED (from `Integral.lean`) |
| `e ≥ 0` | `efun_nonneg` | VERIFIED |
| `(u₂−u₁)² ≤ 2(u₁²+u₂²)` | `sq_sub_le_two_mul_add_sq` | VERIFIED |
| `D − 1 ≤ D²/4` | `trapezoid_le_triangle` | VERIFIED |
| L1, L3, L4 | `L1_triangle`/`L1_F`, `L3_full`, `L4_full` | VERIFIED (`ProfileClosed.lean`) |
| **Lemma E, no hypotheses** | `lemmaE_verified`, `profile_bound_verified` | **VERIFIED** |

The 28512-box ball covering is gone from the mathematics, not merely from Lean, and as of
`ProfileClosed.lean` nothing remains: the ramp integrals, the zone analysis of the clipping
loss, the closed forms of `C` beyond the band, and the reflection are all machine-checked.
`lemmaE_verified` has no hypotheses. The only certificate still outside Lean anywhere in
the project is the second variation (`thm:system`).

## The second variation: elementary constant (`SecondVar.lean`)

| Paper | Lean declaration | Status |
|---|---|---|
| decoupling on E₂: `(a+b)² ≥ λb² − ra²` | `decouple_E2` | VERIFIED (exact square `(a+(1−λ)b)²/(1−λ)`) |
| decoupling on E₁: `(x−y)² ≤ (1+1/κ)x² + (1+κ)y²` | `decouple_E1` | VERIFIED (exact square `(x+κy)²/κ`) |
| `prop:elem` assembly to `1/12` | `secondvar_assembly`, `secondvar_combined` | VERIFIED, with the five analytic inputs as hypotheses |
| half-Poincaré (`habs`) | `habs_verified` (`Poincare.lean`) | VERIFIED |
| subset monotonicity (`hsub`) | `hsub_verified` | VERIFIED |
| the tail cut (`hcut`) | `hcut_verified` | VERIFIED |
| the engine `(f b − f a)² ≤ (b−a)∫f'²` | `sq_sub_le` | VERIFIED — G-monotonicity, no Cauchy–Schwarz |
| DD/DN Wirtinger | `wirtinger_DD`, `wirtinger_DN` (`Wirtinger.lean`) | VERIFIED — shifted Riccati `v = k·cot(kt+c)`, no singularity anywhere |
| the master block | `riccati_block` | VERIFIED — regular FTC, no limits |
| the pointwise square | `pointwise_riccati` | VERIFIED — `(a·s − k·co·b)² ≥ 0` |
| `tan c ≤ 2c` | `tan_ratio_le` | VERIFIED via `sin c ≤ c`, `cos c ≥ 7/8` |
| assembly with shift losses | `secondvar_assembly'` | VERIFIED — `1/1200` (DD), `1/2500` (DN) fit in the `1/1886` slack |
| **the capstone, no hypotheses** | `elementary_constant_verified` | **VERIFIED** |

`prop:elem` of the note is the new mathematics here: `(1/2)δ²Q ≤ −(1/12)‖η‖²` on the cell
with NO transfer matrices and NO ball arithmetic — Rule 3 record: all seven chain steps
hold on 600 random C¹ test functions; the decoupled eigenvalues at `(9/20, 1/4)` are
`(2.689, 0.388)`, strictly above the chain's `(2/11, 369/4400)`, and a claim of `0.75 > c*`
fails against the coupled form, as it must. The sharp `73/100` stays an arb certificate;
what the elementary constant removes is any computer from the QUALITATIVE concavity.

## The geometric reduction (`Reduction.lean`)

| Piece | Lean declaration | Status |
|---|---|---|
| the placed region in rotated coordinates | `placedRegion` | defined |
| fibres lie in the four-piece union | `fibre_subset_four_piece` | VERIFIED (lift of `four_piece`) |
| `S ⊆ X ⟹ vol S ≤ vol X` | `area_mono` | VERIFIED |
| the assembly to `vol S ≤ 2√2−1` | `reduction_assembly` | VERIFIED, given the two named obligations |
| measurability of the region | `placedRegion_measurable` | VERIFIED |
| Fubini restricted to the band | `placedRegion_volume_eq` | VERIFIED |
| fibre ⊆ the two ends (sign-restricted) | `fibre_subset_ends` | VERIFIED |
| fibre measure ≤ two tents | `fibre_volume_le` | VERIFIED |
| lintegral ↔ Bochner bridge | `lintegral_tent_le` | VERIFIED |
| **the slicing identity** | `placedRegion_volume_le` | **VERIFIED** (sign-restricted case) |
| sofa ⊆ placed region (two-motions argument) | hypothesis `hplace` | to discharge — needs the moving body formalised |

## Corrections recorded

`reduction_assembly` originally asked for `volume ≤ 2√2−1` in the fibre coordinates
`(s,t)`, where the plane's area element is `½ ds dt`; the fibre-coordinate volume of the
extremal region is exactly `2(2√2−1)`, so the hypothesis was unsatisfiable and the
assembly vacuous. Caught by the rule-I6 check (can the hypothesis hold at all?) one
commit after it shipped; the bound is now `2(2√2−1)` with the change of variables
recorded in the docstring.
