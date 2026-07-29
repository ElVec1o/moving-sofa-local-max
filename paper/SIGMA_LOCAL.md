# The weighted second-variation framework at Romik's Σ (Program Part III)

Formal note for items S1–S5 of `PROGRAM.md`. Everything here is stated at
proof-level precision; status tags mark what is symbolic, machine-verified,
or computed. This note is the seed of the Σ-local paper section.

Throughout: β = 0.289653820817320941 (Romik's transition angle), ρ = the
reflection across y = ½ fixing Σ, ρ₀ = its linear part (y-flip), and
(μ_t, ν_t) = (cos t, sin t), (−sin t, cos t) the rotating frame.

## 1. Setup and the reflected-family calculus

The ambidextrous functional is F(c) = |Σ(c)|, Σ(c) = S(c) ∩ ρS(c),
S(c) = L_horiz ∩ ⋂_{t∈[0,π/2]} H_t(c), H_t(c) = R_t H + c(t).

**Lemma 1 (ρ-conjugation).** [P — one line] A trajectory perturbation η
translates the direct-family wall at parameter t by η(t) and the
reflected-family wall by ρ₀η(t). The reflected family's wall normals at
parameter t are ρ₀-images of the direct ones:
ρ₀μ_t = μ_{−t}, ρ₀ν_t = −ν_{−t}. Consequently the reflected family's
per-arc Wirtinger forms (N5) are the direct-family forms with
p̃(t) = ⟨η, μ_{−t}⟩, q̃(t) = ⟨η, ν_{−t}⟩ (the sign of ν is killed by the
quadratic forms).

*Proof.* ρ(R_tH + c) = ρ₀R_tH + ρ₀c(t) and ρ₀R_t = R_{−t}ρ₀; apply ρ₀ to
each normal. ∎

So at parameter t the second variation sees FOUR slot directions:
μ_t, ν_t (direct) and μ_{−t}, ν_{−t} (reflected) — the reflected frame is
the direct frame at the OPPOSITE angle. The two ν-directions are an angle
2t apart. This misalignment is the whole mechanism of §4.

## 2. The mask table (computed; `algorithm/rigorous/sigma_masks.py`)

Activity of each hallway boundary element on ∂Σ at c_R, probe grid n=181,
distances saved in `sigma_masks.npz`. In units of π/2 (β ≙ 0.1844):

| element              | direct family    | reflected family |
|----------------------|------------------|------------------|
| corner (notch tip)   | [0.184, 0.816]   | identical        |
| inner wall iy        | [0, 0.816]       | identical        |
| inner wall ix        | [0.184, 1]       | identical        |
| outer wall oy        | [0, 1]           | identical        |
| outer wall ox        | [0, 1]           | identical        |

Three structural facts, all load-bearing:

1. **The corner path is confined to [β, π/2−β] exactly** — the notch is
   carved only in the middle phase; caps are notch-free.
2. **Each cap has exactly one active inner wall** and both outer walls.
3. **The two families' tables coincide** (forced by ρΣ = Σ: the ρ-image of
   a direct contact is a reflected contact). In particular NO cross-family
   rescue by masks alone: both families degenerate at the caps
   simultaneously, and the repair must come from frame geometry (§4), not
   from coverage counting.

(The corner activity shows brief flickers near 0.37–0.42 and mirrored.
Resolved by a fine probe at n=2401: the "detachments" are EVENLY-SPACED
blips of uniform amplitude ~1·10⁻⁴ — polygonal-discretization beating
(chord sagitta of the sampled intersection polygon), not geometry. The
corner path is continuously active on [β, π/2−β]; definitive analytic
confirmation lands with the S4 oracle. Not load-bearing either way: the
corner form provides no coverage in §5.)

## 3. Cap speed law (S1) [P]

On the cap t ∈ (0, β), the active direct contacts have envelope speeds
(rotating-frame identities N4, evaluated on Romik's closed-form first arc,
which is in SOL1 normal form):

λ_A ≡ 0 (outer μ-contact STATIONARY — wall active, point frozen),
λ_C = −½, λ_D = +½ (ν-slot arcs moving), λ_B: wall inactive (mask 0).

At t = β the A-contact ignites (λ_A jumps to ≈ 0.77) and the corner path
and second inner wall switch on. Mirror statements on (π/2−β, π/2). The
algebraic core (v + v″ collapses to the constant term; λ_A ≡ 0 iff SOL1
form) is machine-verified: `lean/MovingSofa` `stationary_contact`,
`lamA_zero_iff`.

**Consequence for slots.** On a cap, the direct family's MOVING arcs are
exactly its two ν-slot arcs (C and D types: outer wall ox + inner wall iy,
both q-form); the μ-slot arc A is present but stationary (contributes the
anomalous response, §6) and B is masked off. By table-equality the
reflected family contributes exactly its two ν_{−t}-slot arcs.

## 4. The frame-pair mechanism (N9 core) [P, machine-verified]

**Lemma 2 (frame-pair coercivity).** For unit vectors ν_{±t} an angle 2t
apart and any u ∈ ℝ²:

  ⟨u, ν_t⟩² + ⟨u, ν_{−t}⟩² ≥ 2·min(sin²t, cos²t)·|u|².

*Proof.* In the bisector frame, ⟨u,ν_{±t}⟩ = cos(t)u₁ ± sin(t)u₂; the
identity (cu₁+su₂)² + (cu₁−su₂)² = 2c²u₁² + 2s²u₂² and c², s² ≥ m :=
min(c², s²) give the bound. Both steps machine-verified
(`frame_pair_identity`, `frame_pair_coercive`). Sharp: equality at
u along the anti-bisector (resp. bisector). ∎

The Gram matrix ν_tν_tᵀ + ν_{−t}ν_{−t}ᵀ has eigenvalues
{2cos²t, 2sin²t}: **the ambidextrous structure repairs its own cap
degeneracy at exactly rate sin²t** — the exponent-2 law measured in the
symbol experiments, now with its exact mechanism.

## 5. The weighted interior Gårding inequality (S5)

Define the **coverage matrix** at parameter t as the mask-weighted sum of
slot projectors over all moving arcs of both families:

  M(t) = Σ_{arcs a active, λ_a ≠ 0} n_a(t) n_a(t)ᵀ,
  n_a ∈ {μ_t, ν_t, μ_{−t}, ν_{−t}}.

**Proposition 3 (coverage bound).** [P given §2–§4] With w(t) =
min(1, sin²t/sin²β, cos²t/sin²β):

  M(t) ⪰ 2 sin²β · w(t) · I  on (0, π/2).

*Proof.* Caps: the four moving arcs are the two ν_t-forms (direct C, D)
and two ν_{−t}-forms (reflected), so M = 2(ν_tν_tᵀ + ν_{−t}ν_{−t}ᵀ) ⪰
4min(sin²t, cos²t)I ≥ 2sin²β·(sin²t/sin²β)I on (0,β) [Lemma 2 doubled].
Middle phase: the direct family alone has both slots moving (A ignited,
λ_A ≈ 0.77; C, D active) giving M ⪰ μμᵀ + ννᵀ = I ⪰ 2sin²β·I since
2sin²β = 0.163 < 1. Mirror cap symmetric. ∎

**Theorem 4 (weighted Gårding for Σ).** [P-route complete; explicit C₀ in
the assembly pass] There is an explicit C₀ such that for all endpoint-
vanishing η ∈ H¹([0,π/2]; ℝ²):

  Q_Σ(η) ≤ −sin²β ∫₀^{π/2} w(t)|η′(t)|² dt + C₀ ∫₀^{π/2} |η(t)|² dt.

*Proof route (each step proved in the Gerver chain, N5–N7, and carrying
over verbatim with Lemma 1's substitutions):*
1. Per-arc Wirtinger forms: each moving arc contributes
   ∫χ (P² − P′²) with P = ⟨η, n_a⟩-type components (N5), junction motion
   absorbed by reparameterization (N7) at cost O(‖η‖²)-terms.
2. Rotating-frame derivative: P′ = ⟨η′, n_a⟩ ± ⟨η, n_a^⊥⟩; the zeroth-order
   terms go to C₀‖η‖² by the ε-split
   −(P′)² ≤ −(1−ε)⟨η′,n_a⟩² + C(ε)⟨η,n_a^⊥⟩².
3. Sum over arcs and families with masks: the derivative terms assemble to
   −(1−ε)∫⟨M(t)η′, η′⟩ ≤ −(1−ε)·2sin²β∫w|η′|² [Prop. 3].
4. The stationary A-contacts and the corner form are one-signed favourable
   / lower-order (§6) and are DISCARDED on the upper-bound side (N1
   one-sidedness): dropping them only weakens the negative term by zero.
5. Collect: coefficient sin²β after fixing ε = ½. ∎

**Empirical confirmation (S3, running).** The finite ladder in the
weighted metric G_w[u,v] = ∫ w⟨u′,μ⟩⟨v′,μ⟩ + ⟨u′,ν⟩⟨v′,ν⟩ + ⟨u,v⟩:
K=10 (20 modes): max generalized eigenvalue −0.377 (weighted), −0.370
(unweighted contrast). K=16 in progress; the prediction of Theorem 4 is a
K-uniform negative weighted margin while the unweighted margin decays to 0
along cap-concentrating sequences.

## 6. The anomalous cap terms [P mechanism, K magnitude]

The stationary A-contact still responds at second order: the perturbed
contact sweeps an O(‖η‖)-arc. By the superset principle (N1) its
contribution to any frozen upper reconstruction is one-signed
(area-decreasing), so it may be dropped in upper bounds — this is why the
measured cap symbol exponents (1.37–1.69 by window) sit BELOW the clean
sin²t law: the anomalous response only helps. The endpoint blow-up probe
(G ~ −3.95/w^{1.5}) confirms the favourable sign.

## 7. The ladder data (S3): the discovery of the piecewise-quadratic
##    structure and the L² invariant

Weighted-metric generalized eigenvalues of the FD ambidextrous Hessian
(basis sin(2kθ) per component):

| K  | modes | m_w (weighted H¹) | m_L² (pure L² metric) |
|----|-------|-------------------|------------------------|
| 10 | 20    | 0.377             | **3.979**              |
| 16 | 32    | 0.1606 (validated ε=1e-4/1e-5) | **3.679**  |
| 24 | 48    | 0.0560            | **3.582**              |

**The weighted-H¹ margin decays; the floor hypothesis (0.127 and then
sin²β) was tested and REFUTED** — K=24's worst mode has weighted-energy
ratio E/L² = 586 (correction term negligible) yet Q/E = −0.056 < sin²β.
Theorem 4 is not contradicted (its C₀‖η‖² slack absorbs the data for
C₀ ≳ 15) but it is VACUOUS on cap-oscillatory modes: the unweighted
zeroth-order term dominates the weighted coverage exactly on
self-similar cap concentrations. The weighted-H¹ frame does not deliver
S7.

**What is actually happening (three experiments):**

1. *Smooth self-similar cap bumps are hyper-coercive*
   (`sigma_cap_symbol.py`): L²-normalized bumps at scales δ =
   0.9β..0.15β give Q/L² = −90 → −272, with Q/E_w growing to −2.07 as
   δ → 0. No symbol degeneracy on smooth profiles.
2. *The functional is KINKED at c_R*: the one-sided responses along
   cap directions differ by a factor ≈ 8 (fwd/bwd = 0.12) — the
   stationary A-contact ignites for one sign of the perturbation and
   stays frozen for the other, exactly as the stationary-contact
   mechanism (N4/S1) predicts. Q_Σ is PIECEWISE-QUADRATIC at c_R, not
   twice differentiable.
3. *Both branches are strictly negative along the worst mode*: the
   K=24 worst eigenvector's profile is a two-branch parabola with
   one-sided curvatures ≈ −9 and ≈ −43 per unit L² — strict decrease
   in both directions. The small weighted-H¹ margin was a big negative
   L²-response (−33·L²) divided by an enormous metric energy.

**The K-stable invariant.** In the pure L² metric the ladder margin is
stable: m_L² = 3.98 / 3.68 / 3.58 with shrinking decrements — the
FD-average form satisfies Q ≤ −m‖η‖²_{L²}, m ≈ 3.5, uniformly in K so
far. (High modes have −k²-type responses, min eigenvalues −1589/−4063/
−9155: the bulk is H¹-coercive; the caps saturate at L² scale.)

**Reframed target (S7′).** Σ-local maximality is a CELL-WISE statement:
at c_R the second variation splits into finitely many combinatorial
branches (cap-ignition sign patterns — the same cell structure as the
global machine N10, evaluated AT the candidate); the theorem to prove
is per-branch L²-coercivity

  Q_cell(η) ≤ −m_cell ‖η‖²_{L²},   min over cells m_cell > 0,

whose FD-average is what the ladder measures (average of branch forms).
The branch-resolved ladder (one-sided stencils per ignition pattern) is
the next computation (S3b). This unifies Part III with the cell-QP
instrument: the local Σ theorem and the global program now run on the
SAME piecewise-quadratic machinery.

## 8. The weighted tail weld (S6) — transfer inventory

The Part-II (Gerver) weld machinery in the weighted metric. Status of
each ingredient:

1. **Far-tail coupling bound (N8): carries over VERBATIM.** [P] The
   Schur/PSD-Gram argument uses only the banded envelope
   |a(k,l)| ≤ c/(l−k) of per-arc integrals of sine products; the weight
   multiplies the μ-slot integrand and w_μ ≤ 1, so the same envelope
   constant holds. No recomputation needed for the BOUND (the measured
   coupling will differ; the bound stands).
2. **Weld algebra: carries over VERBATIM.** [P] The Schur-complement
   inequality m ≥ m_V − τ²/g_T is metric-independent linear algebra.
3. **Tail-diagonal negativity: needs Σ computation.** [K target] The
   Gerver tail section (0.107, with proved envelope c_T = 0.497) must be
   recomputed with Σ's masks and the weight. The proof pattern is
   unchanged: on the middle phase w ≡ 1 and the full Wirtinger coverage
   applies; on the caps the frame-pair modulus (§4) supplies the weighted
   coverage. Requires the Σ analytic oracle (S4) for precision beyond
   Shapely.
4. **Slope carriers.** Σ's basis needs the endpoint-slope-free
   modification (v_k with the sin2t/sin4t corrections) only if the
   junction-gauge analysis (N7 for Σ's junction set) shows the same
   H²-gauge subtlety; the mask table (§2) shows Σ has FOUR interior
   junctions (β, transitions at ~0.37–0.42·π/2 flickers, π/2−β) — the
   gauge audit is part of S6.

## 8b. The fan-release theorem (S7″) — the delivering route

**Lemma 5 (fan redundancy).** [P; algebraic core Lean-verified] Let
P ∈ ℝ² and 0 < b − a < π. Then
⋂_{t∈[a,b]} {x : ⟨x−P, μ_t⟩ ≤ 0} = {⟨x−P, μ_a⟩ ≤ 0} ∩ {⟨x−P, μ_b⟩ ≤ 0}.

*Proof.* ⊆ is trivial. For ⊇: the positive-combination identity
sin(b−a)·μ_t = sin(b−t)·μ_a + sin(t−a)·μ_b (a polynomial identity in the
six sine/cosine symbols — `fan_combination` in `lean/MovingSofa`), with
both coefficients ≥ 0 for t ∈ [a,b] and sin(b−a) > 0, exhibits every
interior normal as a nonnegative combination of the extremes. ∎

**Theorem 6 (fan release).** [P + computational verification] Let F_rel
be the ambidextrous functional with the cap-interior stationary-wall
constraints removed (first cap: the outer μ-wall for t ∈ (0,β); last
cap: the outer ν-wall for t ∈ (π/2−β, π/2); both families inherit the
release through ρ). Then:

1. F_rel ≥ F everywhere (superset principle N1: fewer constraints);
2. F_rel(c_R) = F(c_R) (Lemma 5: at c_R the released walls all pass
   through the frozen contact point, so the extremes already cut the
   same wedge — verified numerically to 2·10⁻¹⁰);
3. F_rel is C² near c_R along cap directions (the stationary-fan kink
   is the ONLY source of one-sidedness there; with two transversal
   walls the corner responds smoothly — verified: fwd/bwd = 1.0000 at
   stencil sizes 2e-4/1e-4/5e-5, where F itself has ratio 0.12);
4. hence the one-sided second variations satisfy Q ≤ Q_rel along every
   ray, and

   **Q_rel ≤ −m‖η‖²_{L²}  ⟹  Σ is a strict local maximum of the
   ambidextrous functional, with L² modulus m.**

No branch enumeration, no kink in the certified object; the discarded
wedge-bite terms are one-signed favourable and never need to be
computed. Two supplementary facts:

*Criticality transfers.* c_R is critical for F_rel: F_rel − F ≥ 0 is
minimized at c_R and F is critical there, so both one-sided directional
derivatives of F_rel vanish. (Measured residual linear responses
~2·10⁻⁴ are polygonal-grid noise — they halve as ε doubles and cancel
exactly in central stencils; the quadratic sum is ε-stable.)

*Domination verified directionally.* Along the full form's worst K=24
eigenvector: released branches (−1.6, −4.1) vs true branches
(−5.2, −43) — released ≥ true on each side, as N1 requires, and
Q_rel(η*) = −6.79, stencil-stable.

First data: Q_rel(cap bump) = −16.62; **released ladder K=10:
NEG DEF, m_rel_L² = 4.576** (bulk spectrum matching the full form's —
min −1587 vs −1589 — confirming the release touches only cap behavior).

**K=16: m_rel_L² = 0.911; K=24: 0.201 — and the honest post-mortem
(§8e) shows the released-margin collapse is GENUINE.** The K=16 datum's
agreement with the Hardy-floor prediction was coincidental: the §8d
Hardy step was wrong (Hardy's ¼ needs a boundary condition the cap
profiles don't satisfy), and direct probes verified the collapse
(−0.77 → −0.039 on the worst spans; in the weighted metric
0.136/0.0062/0.0013). See §8e for the mechanism and the corrected
architecture.

### 8e. Why the release fails, and the corrected object (S7‴)

Releasing the cap fans deletes every μ-slot constraint on the cap
interior. A t→0-concentrating x-polarized bump then couples to F_rel
only through the ν-slot arcs (Lemma 7a coverage, scale-invariant) and
the corner terms — and tuned shapes cancel these against each other:
the flat-direction family is genuine, and inf Q_rel → 0 in every
metric. The release overshot.

**The corrected certified object is the STRUCTURE-FOLLOWING form
Q_struct**: keep every fan wall as an envelope-following contact arc
(exactly the Gerver jet-oracle pattern, there verified smooth and
symmetric). Its per-arc Wirtinger sum then includes the stationary
A-arc's p-form over the whole cap interval — full-strength μ-slot
derivative coverage with NO sin² suppression — restoring the uniform
H¹ Gårding inequality and the entire Part-II ladder/weld architecture
in the plain H¹ metric. Q_struct is superset-valid (its arcs are
constraint-boundary arcs; equality at c_R since the fan arc degenerates
to the frozen point), smooth (envelope formulas are analytic in the
jets), and assembles in CLOSED FORM (the qfrz Σ-port: per-arc
integrals + junction chords, no junction solving) — directly
arb-certifiable. The release detour's permanent yield: N11, the proof
that the A-arc terms are load-bearing, Lemma 7a, and the
criticality/domination checks.

## 8c. Tail control for the released functional (S6-released)

The S7″ conclusion needs Q_rel ≤ −m‖η‖²_{L²} for ALL η, not just the
computed span. Route (each step a Part-II pattern with the released
structure):

**Lemma 7a (exact ν-slot collapse — no Gårding slack).** [P] For any arc
carrying the q-form with q = ⟨η, ν_t⟩ and η = η_x·e_x (the cap-critical
polarization): with s = sin t, c = cos t,

  q² − q′² = −s²(η_x′)² − sc·(η_x²)′ − cos2t·η_x²,

and since (sc)′ = cos 2t the last two terms integrate to a pure boundary
term. Hence over any mask interval [a,b]:

  ∫_a^b (q² − q′²) dt = −∫_a^b sin²t·(η_x′)² dt − [sin t cos t·η_x²]_a^b.

The identity is EXACT — the ν-slot arcs deliver sin²-weighted μ-slot
derivative coverage with no ε-splitting loss; all zeroth-order bulk
terms cancel identically. (Mirror identity for the y-polarization with
cos²t via the μ-slot arcs; mixed polarizations by polarization of the
same algebra.)

**Proposition 7 (released cap-sector coercivity).** [P-route, constants
being fixed] Summing Lemma 7a over the four ν-slot arcs active near the
first cap (direct C, D + reflected C̃, D̃; masks from §2), the released
form obeys, on x-polarized η supported in the cap,

  Q_rel(η) ≤ −4∫ sin²t·(η_x′)² dt + (junction/corner boundary terms),

and Hardy's inequality inf ∫t²φ′²/∫φ² = 1/4 gives

  Q_rel(η) ≤ −(1 − o(1))‖η‖²_{L²} + C_corner·(endpoint values²).

So the cap sector is L²-coercive with structural constant ≥ 1 (before
corner corrections), for ALL frequencies — the tail sector that
defeated the weighted-H¹ frame is closed by an exact identity plus
Hardy. The remaining constant-tracking: the corner/junction boundary
terms (finitely many point evaluations, absorbed as in N7 with explicit
C_corner) and the middle-phase assembly (full coverage, Part-II
pattern).

**Corollary 8 (L² weld).** Bulk frequencies are H¹-coercive
(middle-phase full coverage); cap-concentrated directions are covered
by Proposition 7 uniformly in frequency; the finite ladder block
supplies the mixed/low span; the coupling is bounded by the same
structure constants (Part-II weld algebra in L² normalization).

### 8d. The corner-constant budget (Prop 7 constants)

For x-polarized η supported in the first cap [0, β]:

1. *Mask-edge boundary terms vanish.* C's mask edges are 0 and π/2,
   where sin t·cos t = 0; D's mask edge is π/2−β, where η = 0. Same for
   the reflected arcs. So Lemma 7a contributes pure coverage:
   −4∫₀^β sin²t·(η′ₓ)², no edge terms.
2. *Hardy with the sin²-weight.* On [0, β]: sin t ≥ (sin β/β)·t =
   0.9861·t, so sin²t ≥ 0.9724·t² and each arc's coverage is ≥
   0.9724·(1/4)‖η‖²_{L²} on cap-supported directions (Hardy constant
   1/4, sharp). Four arcs: structural constant ≥ 0.9724 ≈ 0.97.
3. *What remains: the released-corner vertex quadratic.* The two-wall
   corner at the cap responds through the extreme wall displacements
   (g(0), g(β)) = (⟨η(0),μ₀⟩, ⟨η(β),μ_β⟩); for sine-basis directions
   η(0) = 0, leaving a rank-one quadratic in η(β): |corner| ≤
   C_V·|η(β)|². Agmon on [β/2, β] with the weighted derivative:
   |η(β)|² ≤ δ·∫sin²t(η′ₓ)² + (sin(β/2))⁻²·δ⁻¹·‖η‖²_{L²} — absorb the
   first part into item 2's coverage (4 → 4 − C_Vδ), the second into
   the L² constant.
4. *Junction-chord terms at β* (C/D arcs meeting the corner complex):
   same |η(β)|²-type bounds via N7, added to C_V.

Net cap-sector constant: m_cap ≥ 0.97 − (corner budget), with the
measured K=16 margin 0.911 sitting exactly in this window — the
empirical corner budget is ≈ 0.06, comfortably within item 3–4's
head-room. The full explicit C_V enumeration is the remaining
pen-and-paper item of Proposition 7.

So S7″ closes as: released ladder (computed, K-stable) + Lemma 7a/
Proposition 7 (exact identity + Hardy; constants to finish) + the weld.
The prediction for the ladder trend: m_rel(K) may relax from 4.58
toward the cap-sector structural constant ≈ 1 + corner corrections as
cap-self-similar directions enter — remaining strictly positive.

## 9. THE Σ-LOCAL THEOREM — assembled statement and honest ledger

### Theorem 9 (Σ is a strict local maximum — current status)

*Let F be Romik's ambidextrous area functional and c_R his trajectory.
For every perturbation η in the span of {e_comp sin(2kθ)}_{k≤K}, η ≠ 0
modulo horizontal translation,*

  F[c_R + εη] − F[c_R] ≤ −(m/2)·ε²‖η‖²_{L²} + o(ε²),  m ≈ 10 (K-uniform).

**Proof architecture, with the status of every input.**

| # | Input | Status |
|---|-------|--------|
| 1 | **Superset principle** F_recon ≥ F, equality at c_R | **[P]** Lean `superset_principle` |
| 2 | **Exact-degree**: frozen reconstructions are exactly quadratic | **[P]** Lean `exact_degree` |
| 3 | **Cap law** λ_A ≡ 0; fan frozen at (1,½) | **[P]** Lean `lamA_zero_iff`; geometric check to 1e-10 |
| 4 | **Structure map**: ∂Σ is 10 arcs, junctions exactly at {0,β,π/2−β,π/2} | **[K]** residuals 1e-10; Green area = A_R* to 2.6e-9 |
| 5 | **Envelope null result**: junction response contributes nothing | **[P/K]** derived (H_ββ diagonal ≡ 0) + measured 3.8e-6 at K=16 |
| 6 | **Q_struct closed form** = the true structure-following 2nd variation | **[K]** matches direct FD oracle to 5 digits |
| 7 | **Q_struct NEGATIVE DEFINITE** on the K-span | **[C] CERTIFIED in arb** at K=10 (20 modes, 210 entries, max radius 2.1e-12; Sylvester minors positive through order 20, 256 bits) |
| 8 | **Fan release**: F ≤ F_rel, equality at c_R, F_rel is C² | **[P]** Lean `fan_combination`; verified 2e-10, fwd/bwd = 1.0000 |
| 9 | **Fan-bite identity** F_rel − F = ε²N(φ), N ≥ 0 homogeneous deg 2 | **[P]** Lean `fan_homogeneity`; validated to 0.55% |
| 10 | **Bite lower bound** N(φ)+N(−φ) ≥ cot β‖d‖²_∞, translation-invariant | **[P]** Lean `fan_cut_gain` |
| 11 | **Dichotomy**: −Q_rel + bites ≥ ≈10, K-stable (10.00 at K=24) | **[K]** search certified safe by spectral gap |
| 12a | **Interpolation**: −Q_true ≥ M, M a genuine quadratic form (bite minorant is quadratic since d is linear in η) | **[P/K] DONE** — holds on all directions, verified against the exact oracle |
| 12b | **Weld**: extension from the K-span to all of L², now applied to the quadratic M | **[ ] OPEN** (mechanical: needs Q_rel at K>24, then c_T and τ) |

**What is therefore established.** Items 1–11 give, for each computed K, a
K-uniform margin on the K-mode span, and item 7 upgrades the definiteness
statement on that span to a fully certified one (interval arithmetic, no
floating point in the chain, modulo the β-enclosure noted below). Two
INDEPENDENT routes reach the conclusion on the span: the certified
Q_struct < 0 (items 1–7), and the dichotomy with its K-stable constant
(items 8–11). The first is rigorous but its margin decays with K; the
second has a K-stable margin but its Q_rel input is float.

**What is NOT established (item 12).** The passage from "every direction of
the K-mode span" to "every direction of L²" is not done for Σ. The Gerver
analogue of this step (Part II's weld: far-tail Schur bound N8 + block
coupling τ) took substantial work, and its Σ version has not been carried
out. Until it is, Theorem 9 is a statement about finite-dimensional
subspaces, not a local-maximality theorem. **Σ-local remains open**, with
the remaining gap now a single named, standard-shaped estimate rather than
a structural unknown.

**β-enclosure: discharged.** Romik's β has a closed form,
β = arctan(((√2+1)^{1/3} − (√2−1)^{1/3})/2), so it is enclosed directly in
ball arithmetic — radius 5.8·10⁻⁹⁰ at 300 bits, no root-finding, no
Newton–Kantorovich step needed. Re-running the certification with the exact
enclosure gives entry radii 1.7·10⁻⁸⁵ and the same verdict: **item 7 is
UNCONDITIONAL** (modulo the arb library itself).

### Why the two routes are worth keeping separate

Route A (certified Q_struct) is the one that will scale to a machine-checked
proof: every entry is an elementary trigonometric integral over ranges
{0, β, π/2−β, π/2}, with trajectory-independent integrands — so the whole
matrix is interval-izable with no oracle, no junction solve, and no
floating point. Route B (the dichotomy) is the one that explains WHY the
constant does not degenerate: the fan bite exactly compensates the released
form's collapse, with its share growing 21% → 27% → 32% across K = 10, 16,
24. A complete proof wants both: A for rigour, B for the uniform constant.
