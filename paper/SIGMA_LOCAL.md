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

(The corner activity shows brief flickers near 0.37–0.42 and mirrored —
distances hovering at the 2·10⁻⁴ threshold near Romik's interior phase
transitions. Not load-bearing: the corner form provides no coverage in §5.)

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

## 7. The ladder data (S3) and the floor hypothesis

Weighted-metric generalized eigenvalues of the FD ambidextrous Hessian
(basis sin(2kθ) per component; metric G_w = ∫ w_μ⟨u′,μ⟩⟨v′,μ⟩ +
⟨u′,ν⟩⟨v′,ν⟩ + ⟨u,v⟩):

| K  | modes | m_w (weighted) | unweighted | stencil check |
|----|-------|----------------|------------|---------------|
| 10 | 20    | 0.377          | 0.370      | —             |
| 16 | 32    | 0.1606         | 0.157      | ε=1e-4 vs 1e-5: 0.16057 vs 0.16035 ✓ |

All eigenvalues strictly negative at both K. The margin fell ≈ 1/K²
between the two data points — but the top eigenvector diagnosis refutes
the decay-to-zero reading: the offending mode is x-polarized,
cap-concentrated (62% of L² mass in the caps), with weighted-derivative
Rayleigh quotient ∫(w_μ⟨η′,μ⟩² + ⟨η′,ν⟩²)/‖η‖² = 101, and

  Q(η*) = −0.127 × (weighted derivative energy).

So Q tracks the weighted energy PROPORTIONALLY on the worst mode — the
generalized eigenvalue is heading to a **floor ≈ 0.127** (the true
weighted coercivity constant; compare the Theorem-4 structural constant
sin²β = 0.084), while G_w grows with K. Discriminating experiment: K=24
(running). Floor hypothesis predicts m_w(24) ≈ 0.13–0.14; genuine decay
predicts ≈ 0.07.

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

## 9. What remains for the Σ-local theorem (S7)

- S3: K=24 discriminating run (in progress); then K=32 if needed.
- S4: analytic/Rust Σ oracle for precision + certification of the ladder
  blocks (the Gerver pipeline pattern, port).
- S5: assembly write-up with explicit C₀ (route complete, §5).
- S6: items 3–4 above.
- Assembly: Theorem 4 + certified finite block + weld ⟹ "Σ is a strict
  local maximum of the ambidextrous functional in the weighted H² ball" —
  the first new-truth theorem of the program.
