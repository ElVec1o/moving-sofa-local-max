# Paper ↔ Lean mapping

Required by Rule 5.  Every declaration below is in `MovingSofa/Basic.lean`.
`lake build` is clean, there is no `sorry` anywhere in the file, and
`#print axioms` reports nothing beyond `propext`, `Quot.sound` and, for
`strip_covers_iff` alone, `Classical.choice`.  An earlier version of this file claimed
no `Classical.choice` anywhere; that claim was correct until F13 was added and is now
corrected.

Toolchain: Lean 4.30, no Mathlib.  Trigonometric quantities are carried as
formal symbols under Pythagorean side conditions, and arithmetic is over `Int`
so that the identities stay decidable; the instantiation of the symbols at actual
sines and cosines is a separate Mathlib-track item and is NOT claimed here.

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

## Tooling note

Core Lean (no Mathlib) has no `ring` and no `positivity`.  Degree-2 identities go
through with `simp [Int.add_mul, Int.mul_add, Int.mul_comm]` followed by `omega`;
degree-4 identities (such as the 2×2 Sylvester identity) do not, which is why F8
formalizes the logic of a certificate rather than the algebra that produces one.
