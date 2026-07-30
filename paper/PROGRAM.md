## B1 ANSWERED: Baek's balancing argument does NOT transfer as-is  💧💧

Read Baek Ch. 3-4 in full.  His balancing engine is a COINCIDENCE between two
things, and the coincidence is what breaks for two corners.

### What makes his argument work

Working with polygon caps and the functional A_Theta(K) = |C_Theta(K)| - |N_Theta(K)|:

  * Lemma 3.4.6 (the identity).  Following the polyline p_K from right to left,
    C_K^+(omega) - A_K^-(0) = sum_{t} tau_K(t) v_t.  Following the upper boundary
    dK from right to left gives the SAME endpoints, so also
    C_K^+(omega) - A_K^-(0) = sum_t sigma_K(t) v_t.  Subtracting,
        sum_t (tau_K(t) - sigma_K(t)) (v_t . u_0) = 0,   with v_t . u_0 < 0.
  * Lemma 3.4.7 (the derivative).  Pushing the edge e_K(t) outward by epsilon
    changes the functional by (sigma_K(t) - tau_K(t)) epsilon + O(eps^2).

The SAME quantity sigma - tau appears in both.  Hence if K is not balanced there is
a t with sigma > tau, pushing there strictly increases the area, and a maximum must
satisfy sigma = tau exactly (Theorem 3.4.9).  That EQUALITY is then consumed by
Theorem 3.4.10 (a maximum polygon cap contains its niche), which is precisely the
step that repairs the connectedness gap in Gerver's original argument.

### Why it breaks for two corners

The ambidextrous functional is A_ambi = |C2| - |U| - |rho U|.  On rho-symmetric
caps the admissible perturbation must push e(t) and e(rho t) together, and

    delta A_ambi = 2 [ sigma(t) - tau_U(t) - tau_U(rho t) ] epsilon,

so the balance condition would have to be sigma(t) = tau_U(t) + tau_U(rho t).  But
the geometric identity does NOT change correspondingly: dC2 and the polyline of U
connect one pair of endpoints, while the polyline of rho U connects a DIFFERENT
pair, because the two niches sit on opposite sides of the separating band.  There
is no single identity forcing sum (sigma - tau_U - tau_{rho U}) v_t = 0, so the
contradiction step does not close.

Concretely: Baek's derivative and his identity are both expressions in sigma - tau.
Ours is an expression in sigma - tau_U - tau_{rho U}, and the available identity is
still in sigma - tau.  The mismatch is exactly one factor of the second niche.

### The irony worth recording

What creates the obstruction is our own Theorem (A1-A6): the niches are DISJOINT,
separated by a band of width 0.2243 about y = 1/2.  That disjointness is what makes
|U u rho U| = |U| + |rho U| (good, it killed the inclusion-exclusion term) and ALSO
what puts the two niche polylines on opposite sides of the cap so that no common
identity is available (bad, it kills the balancing step).  The same geometric fact
helps Ch. 7-8 and hurts Ch. 3-4.

### Status

B1 = NO as stated.  Not proved impossible -- what is established is that Baek's
specific mechanism does not carry over, and where.  Options, in order of appeal:

  (i)  find a modified identity for the rho-symmetric setting: perhaps follow a
       path that traverses both niche polylines and the cap boundary once each, so
       that a single closed circuit yields the needed relation;
  (ii) balance in the rho-QUOTIENT: work on the half-strip 0 <= y <= 1/2 with one
       niche, where Baek's argument may apply verbatim, and lift;
  (iii) replace the balancing existence argument entirely, since its only purpose
       is to produce a maximum monotone sofa of rotation angle pi/2 satisfying the
       injectivity condition; any other existence proof would do.

Option (ii) is the most promising and is directly enabled by the separation
theorem: below the band there is exactly one niche, which is Baek's situation.

## B6 COMPLETE: SOL6 transcribed and ODE6 DERIVED

ROMIK_FORMULAS.md carried ODE1-ODE6 by name and SOL1-SOL5 explicitly, but SOL6 was
missing -- and Sigma's middle phase IS SOL6.  Both are now recorded.

    SOL6:  x_6(t) = R_t ( f1 cos(t/2) + f2 sin(t/2) - 1,
                         -f2 cos(t/2) + f1 sin(t/2) - 1 )^T + kappa_6,
           kappa_6 = ( 1 - (4/3) a_1 , 1/2 ),   f2 = (1 - sqrt2) f1,
           f1 = (4/3) a_1 cos(beta) / ( cos(beta/2) + (1-sqrt2) sin(beta/2) ).

    ODE6:  x'' = 2 J x' + (3/4)(x - kappa_6) - (1/4) R_t (1,1)^T,
           J = [[0,-1],[1,0]].

DERIVATION.  Writing v for the bracket, v'' = -(1/4)(v + (1,1)) directly.  With
x = R_t v + kappa and R' = JR = RJ one gets x' = R(Jv + v') and
x'' = R(-v + 2Jv' + v''); substituting v'' and eliminating v' = R^{-1}x' - Jv gives
the stated form.

VERIFIED: residuals 5.6e-15 at five values of t, against a finite-difference floor
of ~1e-9; and v'' = -(1/4)(v + (1,1)) holds to 1e-16.

STRUCTURAL POINT.  ODE6 is NOT of the form of ODE1-ODE5.  Those are
x'' = R_t b + M(t) x' with no x term; a least-squares fit of SOL6 to that pattern
fails with residual 0.154.  ODE6 carries a restoring term in x.  In complex form
(J <-> i) its homogeneous part is z'' - 2i z' - (3/4) z = 0, with characteristic
roots lambda = i/2 and 3i/2 -- which is exactly why SOL6 contains cos(t/2) and why
the closed form for c_y - 1/2 contains sin(3t/2).  The two half-integer angles in
this project's Sigma formulas are the two characteristic exponents of ODE6.

## A3' PROVED: max_t c_y(t) in closed form, and F1 derived rather than tabulated

The separation lemma needs M := max_t c_y(t) < 1/2.  This is now closed form.

### The reduction

On Romik's middle piece [beta, pi/2-beta], x_6(t) = R(t) v(t) + kappa with
v(t) = (F1 cos(t/2) + F2 sin(t/2) - 1, -F2 cos(t/2) + F1 sin(t/2) - 1), and

    kappa_{6,2} = 1/2  EXACTLY,        F2 = (1 - sqrt2) F1.

So c_y(t) - 1/2 = sin(t) v_x + cos(t) v_y, and using
S(3C^2 - S^2) = sin(3t/2), C(3S^2 - C^2) = -cos(3t/2) with S = sin(t/2),
C = cos(t/2), this collapses to

    c_y(t) - 1/2 = F1 sin(3t/2) - F2 cos(3t/2) - (sin t + cos t)
                 = F1 sqrt(4 - 2 sqrt2) sin(3t/2 + pi/8) - sqrt2 sin(t + pi/4),

using tan(pi/8) = sqrt2 - 1.  Both sinusoids peak at t = pi/4, and the expression
is symmetric about pi/4 (verified: c_y(beta) = c_y(pi/2-beta) = 0.214380179711375),
so the maximum is attained at t = pi/4 and

    M = 1/2 - ( sqrt2 - F1 sqrt(4 - 2 sqrt2) ),
    M < 1/2   <=>   F1^2 < (2 + sqrt2)/2.

### F1, derived from the junction rather than taken from Table 2

The reference implementation carried F1 as the decimal 1.202938908156911389 from
Romik's Table 2, with a comment admitting the closed form was not resolved.  Two
attempts to recover it from the decimal FAILED and are logged as dead ends:
`findpoly` returns spurious degree-3 polynomials with 5-digit coefficients (19
digits of input cannot support that), and `pslq` finds no relation in Q(sqrt2).

It is not needed.  F1 is DETERMINED by the junction condition x_1(beta) = x_6(beta).
Both x_1 and x_6 have the form R(t) v + kappa with kappa_y = 1/2, and the two
kappa_x differ by exactly a_1/3, so R(beta)(v_1 - v_6) = (-a_1/3, 0), whence
v_{1,x} - v_{6,x} = -(a_1/3) cos beta.  With A2 = 0 this gives

    F1 = (4/3) a_1 cos(beta) / ( cos(beta/2) + (1 - sqrt2) sin(beta/2) ),

and a_1, beta are already closed form:

    a_1  = (1/4) sqrt( 4 + cbrt(71 + 8 sqrt2) + cbrt(71 - 8 sqrt2) )
    beta = arctan( (1/2)( cbrt(sqrt2+1) - cbrt(sqrt2-1) ) ).

VERIFICATION at 50 digits: the derived value is
1.202938908156911389070223, agreeing with Table 2's 19-digit decimal to 7.0e-20 --
i.e. the table value is exactly its rounding.  And the SECOND junction component,
which the derivation did not use, is satisfied to 1.67e-51.  That independent
check is what makes this a derivation and not a curve fit.

### The numbers

    F1^2        = 1.44706201675774209406641508553
    (2+sqrt2)/2 = 1.70710678118654752440084436210
    gap         = 0.26004476442880543033          -> M < 1/2 HOLDS

    M               = 0.3878381292441942963983578
    1/2 - M         = 0.1121618707558057036        (separation margin)
    1 - 2M          = 0.2243237415116114072        (gap between the niches)

All explicit algebraic numbers.  A3 moves HEURISTIC -> PROVED: the inequality is a
finite comparison of closed-form algebraic numbers with a 15% margin, not a
numerical measurement.

## B3, at the design level: the rho-symmetry HALVES the construction

rho is an isometry, so |rho U| = |U| exactly (measured: identical cell counts,
43775 each).  Combined with disjointness (A4),

    |Sigma| = |C2| - |U u rho U| = |C2| - 2|U|.

So the ambidextrous Q needs only ONE niche handled, with one core and two tails --
exactly Baek's shape, not two cores and four tails.  The rho-symmetry halves the
construction instead of doubling it.  This is the answer to the scoping question
that opened the new program.

## F10 formalized: Baek's concavity criterion (all VERIFIED)

    concave_critical_global          B <= 0 and C <= 0  =>  A + B + C <= A
    segment_far_endpoint             the coefficient bookkeeping identifying
                                     A + B + C with h(K',K')
    concavity_of_subtracted_square   a subtracted square has C <= 0 -- the
                                     mechanism of Baek's Thm 7.4.2

38 theorems, zero sorry, axioms only propext and Quot.sound.  Recorded honestly:
these formalize the ARITHMETIC CORE of Thm 7.1.5, not the convex-domain theory
itself (which needs Minkowski sums and support functions over the reals, i.e.
Mathlib).  The point of formalizing the core is that it is the step which makes the
second variation unnecessary, and it is now machine-checked.

# NEW PROGRAM (2026-07-30): the AMBIDEXTROUS problem via Baek's architecture

GOAL: prove that Romik's ambidextrous sofa Σ, area A_R* = 1.6449552184, is the
maximum-area ambidextrous moving sofa, by transferring Baek's concavity
architecture (arXiv:2411.19826) from the one-corner problem.

The second-variation program is retired.  Baek settles the one-corner problem
globally and never computes a second variation; the ambidextrous problem is open
and his method is the one to use on it.  Retired ladder jobs were killed; their
checkpoints are kept but certify a bound no longer in use.

## Baek's engine, extracted (his Chapter 7)

  * Thm 7.1.1  the planar convex bodies 𝒦 form a CONVEX DOMAIN under Minkowski sum
  * Thm 7.1.2  h_K, the vertices v_K^±, and the surface measure σ_K are
               CONVEX-LINEAR in K
  * Thm 7.1.3  |K| = ½∫ h_K σ_K is QUADRATIC in K
  * Thm 7.1.5  for a CONCAVE quadratic f on a convex domain, K maximises f iff
               Df(K;·) ≤ 0 -- only the FIRST derivative is needed
  * Thm 7.3.2  the convex-curve segment has 𝒥(u_K^{a,b}) = ½∫_{(a,b)} h_K σ_K,
               quadratic in K
  * Thm 7.4.1  MAMIKON, generalised: the Mamikon region has area ½∫_a^b α(t)² dt
               with α(t) = (z(t) − v_K^+(t))·v_t
  * Thm 7.4.2  THE CONCAVITY ENGINE: if z_K is convex-linear in K and lies on the
               tangent line l_K(t), then ℳ_K(a,b;z_K) is quadratic and CONVEX in K

So Q = (linear and quadratic terms) − (Mamikon regions) is CONCAVE, because a
square of a convex-linear quantity is a convex quadratic.  That single observation
replaces every Hessian ladder in the retired program.

## The transfer, and the one thing that had to be checked

Baek: S = K \ N(K), convex cap minus ONE niche.
Ambidextrous, in the decomposition this project already uses in sigma_area.rs:

    Σ = C₂ \ (U ∪ ρU),     C₂ = C ∩ ρC convex,     ρ(x,y) = (x, 1−y).

A convex cap minus the union of TWO niches.  Inclusion–exclusion,

    |U ∪ ρU| = |U| + |ρU| − |U ∩ ρU|,

puts the overlap term into Q with a PLUS sign, which is exactly the wrong sign for
a mechanism built on SUBTRACTING convex quadratics.  So the whole transfer hinged
on whether the niches overlap.

### They do not.  [PROVED]

Measured first: on a 500×500 grid over [−2.6,1.6]×[−0.2,1.2] with n_t = 12001,

    |U| ≈ |ρU| ≈ 1.033719   (43775 cells each),   |U ∩ ρU| = 0   (0 cells)

and refinement bands of ±0.02, ±0.005, ±0.001 about y = ½ contain no point of
either niche.  Then the reason, which is elementary:

LEMMA (niche ceiling).  For t ∈ [0, π/2], Q_t ⊆ {y ≤ c_y(t)}.
Proof.  q ∈ Q_t means q − c(t) = −a μ_t − b ν_t with a, b > 0.  On [0, π/2] both
μ_t = (cos t, sin t) and ν_t = (−sin t, cos t) have non-negative y-component, so
q_y − c_y(t) = −a sin t − b cos t ≤ 0. ∎

LEMMA (separation).  Hence U ⊆ {y ≤ M} with M := max_t c_y(t), and ρU ⊆ {y ≥ 1−M}.
If M < ½ the two are disjoint. ∎

For Romik's trajectory M = 0.387838, measured, against the threshold ½ — a margin
of 0.112, and a gap of 0.224 between the niches.  Since Romik's Σ is piecewise
ALGEBRAIC and c is in closed form, M < ½ is a finite closed-form check, not a
numerical one.

CONSEQUENCE: |U ∪ ρU| = |U| + |ρU| exactly, so each niche is handled by precisely
the machinery Baek applies to his single niche, and the architecture transfers with
no new mathematics at this step.

## Formalized (F9, all VERIFIED)

    niche_below_apex        F9a  a wedge point lies at or below its apex
    niche_disjoint          F9b  M ≤ y and H−M ≤ y with 2M < H is contradictory
    union_area_of_disjoint  F9c  the inclusion–exclusion term drops out

`lake build` clean, zero sorry, axioms only propext and Quot.sound.  35 theorems.

## What remains, in order

  B1  monotone reduction for ambidextrous sofas: does a maximum-area ambidextrous
      sofa admit BOTH movements with rotation angle exactly π/2?  (Baek Ch. 3–4
      redone; his balancing repair may or may not survive two corners.)
  B2  the ambidextrous injectivity condition, by a differential inequality in
      Baek's style (his Ch. 6, the eleven-fold bootstrap).
  B3  the overestimating region: two cores and four tails, or one core and two in a
      ρ-quotient.  This is where the ρ-symmetry should pay.
  B4  Q on a convex domain of convex-body tuples, quadratic by support functions.
  B5  concavity by Mamikon, using F9 so that the two niches contribute additively.
  B6  criticality of Σ from Romik's ambidextrous ODEs (Rom18) — the analogue of
      Baek §1.8.3, and the step where Romik's existing work is the input.
  B7  formalize B4/B5 in Lean.  These are closed-form convex geometry with NO
      numerics, so unlike every margin in the retired program they can reach
      VERIFIED.

## 🌊🌊🌊 RULE 4 NOVELTY AUDIT AGAINST BAEK 2024 — PART II IS SUBSUMED AND WAS ALREADY KNOWN

Read: Jineon Baek, "Optimality of Gerver's Sofa", arXiv:2411.19826v1, 29 Nov 2024,
119 pages.  This audit should have been run at the start of the program; running it
now invalidates a large part of it.

### What Baek proves

Definition 1.1.1: the hallway is L = H_L ∪ V_L with H_L = (−∞,1]×[0,1] and
V_L = [0,1]×(−∞,1] — ONE right-angled corner, the CLASSICAL problem.  Theorem 1.1.1:
Gerver's sofa attains the maximum area 2.2195…  So global optimality for the
classical problem is settled (peer review still pending as of this audit).

### Baek's method, and why it is structurally better than ours

  1. Reduce to MONOTONE sofas with rotation angle exactly π/2 (Ch. 3–4), repairing
     a genuine logical gap in Gerver's own balancing argument (§1.3.2: balancing can
     BREAK connectedness of the polygon intersection — Figure 1.6).
  2. Prove an INJECTIVITY CONDITION on the rotation path via a differential
     inequality, solved by bootstrapping f₀ → f₁ → … → f₁₁ ≥ 1 (Figure 1.10).
     Three iterations suffice numerically; he does eleven "to minimize computer
     assistance".
  3. Build an OVERESTIMATING REGION R ⊇ S shaped like Gerver's niche (one core, two
     tails), cutting the cap at a specific angle φ ∈ [0.039, 0.040].
  4. Define Q(K,B,D) := |K| − 𝒥(γ) on a CONVEX DOMAIN ℒ of triples of convex bodies
     with linear constraints, where 𝒥 is the curve area functional.
  5. Prove Q is QUADRATIC on ℒ (support functions / Brunn–Minkowski) and GLOBALLY
     CONCAVE (via MAMIKON'S THEOREM: the Mamikon regions have area linear in K, so
     Q is a linear functional minus convex quadratics).
  6. Show Gerver's G is a critical point of Q using ROMIK'S local-optimality ODEs.
  7. Concave + local ⟹ global: Q(K,B,D) ≥ Q(K*,B*,D*) ≥ |S*|, so |G| ≥ |S*|.

THE DECISIVE STRUCTURAL POINT.  Our entire program is SECOND-VARIATION: assemble
Hessians, prove negative definiteness, weld a tail.  Baek never computes a second
variation.  He constructs an upper bound that is quadratic and globally concave, so
only the FIRST derivative is needed, and concavity does globally what our Hessian
ladders were trying to do locally.  Our method is strictly weaker than the available
one.

### Part II (Gerver local maximality) is dead twice over

  (a) SUBSUMED: Baek proves GLOBAL optimality, strictly stronger than local.
  (b) ALREADY KNOWN: Baek states plainly that the derivation S_max = G "is
      essentially done in the existing works establishing the local optimality of G
      [Ger92; Rom18; Den24]".  So local optimality of Gerver's sofa was in the
      literature BEFORE Baek, in three separate places.

The one distinction worth recording, and it does not rescue the result: Gerver's and
Romik's "local optimality" is a FIRST-ORDER derivation assuming the contact
structure, whereas Part II attempted a genuine SECOND-ORDER statement over all
perturbations without assuming the structure.  Stronger in kind, but of a claim that
is now a corollary of Baek.  Part II should be retired, not repaired.

### The φ coincidence is not a coincidence

Baek cuts the cap at φ ∈ [0.039, 0.040].  Our measured φ = 0.039177 is the same
angle, and it is exactly where we independently found that Gerver's contact arc A is
CONSTANT on [0,φ] (verified to 3e-31).  Baek builds his core/tails decomposition
precisely around that degeneracy.  So our hardest-won structural discovery is a
known feature of the problem that the successful proof is organised around.

### What survives the audit

  * ROMIK'S AMBIDEXTROUS SOFA Σ IS STILL OPEN.  Baek's hallway has one corner; the
    ambidextrous problem requires turning both ways and is not addressed anywhere in
    his 119 pages.  A_R* = 1.6449552184 is still only a conjectured optimum, derived
    by Romik from local optimality exactly as Gerver derived his.  This is a real
    open problem and it is where the remaining value is.
  * FORMALIZATION.  Baek's proof is 119 pages and peer review is pending.  Nothing
    of it is machine-checked.  Our Lean development (32 theorems, zero sorry, axioms
    only propext/Quot.sound) is a genuine asset and the natural target is Baek's
    argument, or the ambidextrous analogue of it.
  * The Mode-2 lemma (signed area ≠ region area, `bowtie_signed_zero` /
    `square_signed`) is a real cautionary result for anyone computing area bounds
    from Green sums, and is machine-checked.

### What does NOT survive

N1 (superset principle) is Baek's overestimating region R — the same idea, and ours
is a rediscovery.  The Toeplitz/symbol machinery (M1–M4), the chord-free
reconstruction, the lens analysis, and every ladder margin are all internal to the
second-variation route, which the concavity route makes unnecessary.  They are
salvage, not results.

### Consequence for the plan

The correct move is NOT to turn the remaining yellow/white atoms green.  Most of
them certify a second-variation program for a theorem that is either already proved
(Gerver) or better attacked another way (Σ).  Finishing them would be the last-mile
failure mode of Rule 16 applied to a target that has moved.

The re-aimed program:
  A. Transfer Baek's architecture to the ambidextrous problem: monotone reduction,
     injectivity by differential inequality, an overestimating region respecting the
     ρ-symmetry (two cores / four tails, or a ρ-quotient with one core and two),
     Q quadratic on a convex domain of convex-body tuples, concavity by Mamikon,
     criticality from Romik's ambidextrous ODEs.
  B. Formalize in Lean: the concavity engine (Mamikon, quadraticity of Q via support
     functions) is far more formalizable than any Hessian ladder, because it is
     closed-form convex geometry with no numerics.

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

## Shapely-oracle Rust port — DELIVERED, with a measured limitation

`sigma_area.rs`. The port is made tractable by an algebraic restructuring
rather than by implementing polygon booleans: each hallway is
H_t = C_t \ Q_t (two half-planes minus the reflex quadrant), so the whole
intersection reorders as

    S = ⋂_t H_t = (⋂_t C_t) \ (⋃_t Q_t) = C \ U,
    Σ = C2 \ (U ∪ ρU),   C2 = C ∩ ρC convex.

C2 is exact Sutherland–Hodgman half-plane clipping; and on any vertical
line each quadrant cuts exactly ONE y-interval, so the notch is a 1-D
interval union per slice (sort and merge). No polygon booleans anywhere.

**Validated**: area at c_R agrees with shapely to 4.8e-6 at NXQ=4000 and
1.2e-8 at NXQ=30000 (both sit 1.2e-4 from Romik's exact value — that is
the shared t-discretization, not a port error). Speed: 3x faster than
shapely at equal accuracy.

**MEASURED LIMITATION (the honest part).** The slice quadrature is NOT
adequate for finite-difference Hessians at high mode frequency:

| test direction | Rust FD | shapely FD | error |
|---|---|---|---|
| smooth cap bump | −80.27 | −81.38 | 1.4% |
| K=24 worst eigenvector (freq ~24) | −44.36 | −52.39 | 15% |

with the high-frequency value converging only slowly in NXQ
(+812 / +81 / −44 at NXQ = 4k / 12k / 30k). **Mechanism**: shapely
computes the polygon exactly, so its O(1e-4) discretization error is
common-mode and cancels in the ε² division; the slice quadrature's error
sits at KINKS THAT MOVE WITH ε, so it does not cancel, and the 1/ε² = 1e8
amplification exposes it. This is a real property of the method, not a
tuning issue.

**`subtract_wedge` — DONE, and the oracle is now EXACT.** The routine
walks ∂P, classifies against the quadrant, computes crossings, and
re-routes each inside-run along ∂Q through the apex.

*The bug that took the debugging*: with a single enter/exit pair the walk
begins AT the exit, so the Enter that cyclically precedes it is still
pending when the loop ends and never receives its ∂Q routing — the
boundary then short-circuits along a chord and removes only a thin sliver
instead of the whole wedge region. It was invisible from the outside
because the apex-fallback counter never tripped (the code never reached an
Exit with a pending Enter). Diagnosed by instrumenting one wedge: it
showed `inside=1, crossedges=2` while shapely put 0.150 of area in that
same quadrant — proving the walk ran but removed nothing. Fixed by giving
the wrap-around pair its own closure.

**Validation — exact agreement with shapely:**

| quantity | Rust | shapely | difference |
|---|---|---|---|
| area at c_R | 1.645080257887 | 1.645080257887 | 8.4e-15 |
| FD, smooth cap bump | −81.38334 | −81.38334 | 0.0000% |
| FD, K=24 eigenvector | −52.38710 | −52.38710 | 0.0000% |

1199 wedges fire. Both finite differences now match to all printed digits —
the exactness property the slice quadrature lacked is restored, because the
polygon arithmetic is exact and its error is common-mode across an FD
stencil.

**What is now Rust/C end to end**: the closed-form assembler
(`sigma_struct.rs`, 0.5 s for K=64), the interval certification
(FLINT/arb), the eigensolves (LAPACK), Lean. The remaining Python is the
shapely oracle, still needed for high-frequency FD until `subtract_wedge`
lands.

## TAIL (Theorem 9, item 12) — high-K evidence with the exact oracle

With `sigma_area.rs` exact and fast, the tail was attacked directly against
the TRUE functional rather than through proxies.

**(a) Tail probe** (`sigma_tail.py`, driver over the Rust oracle). The
covering argument predicts which mechanism carries each component; measured
−Q_true on L²-normalized families at frequencies far past the K≤24 ladders:

| family | k=4 | 16 | 32 | 64 | 128 | reading |
|---|---|---|---|---|---|---|
| cap, x-polarized | 411 | 2374 | 3289 | 3595 | 3645 | **saturates ≈3600** |
| cap, y-polarized | 8617 | 22821 | 24322 | 24441 | — | k² then saturates |
| plain modes | 190 | 2710 | 10413 | — | — | k² growth |
| middle-supported | 861 | 12550 | 51024 | — | — | k² growth |

The critical row is the first: the cap x-component is the one the ν-slot
arcs cover only with weight sin²t (degenerate at the cap), so the FAN BITE
must carry it — and the bite is amplitude², i.e. frequency-INDEPENDENT.
Measured: it saturates at ≈3600 and does NOT decay, confirmed at n_theta =
1201 and 2401. **That is the one claim whose failure would have broken the
weld, and it holds.**

**(b) K-uniform bound** (`sigma_tail_min.py`). Cleaner than the Q_rel+bite
dichotomy: since Q_true ≤ Q_struct (superset), −Q_true ≥ −Q_struct, so the
minimum of −Q_true can only sit where −Q_struct is least coercive. Searching
those p=8 directions with the EXACT oracle (no polarization of the kinked
functional, no matrices):

| K | −λ₁(Q_struct) | inf over the p least-coercive dirs | gap λ_{p+1} |
|---|---|---|---|
| 16 | 1.742 | **9.19** | 302 |
| 24 | 0.351 | **8.76** | 218 |
| 32 | 0.044 | **8.85** | 139 |
| 48 | 0.00002 | **8.77** | 54 |
| 64 | ~0 | (search 59.4) | 8.8 |

**−Q_true ≈ 8.8·‖η‖²_{L²}, K-STABLE across K = 16…64**, while Q_struct's own
margin collapses by five orders of magnitude over the same range. The true
functional does not degenerate; only the smooth majorant does.

**What is still missing for a proof.** The bound above is min(search, gap),
which is rigorous for η lying wholly in the p-span or wholly in its
complement. MIXED directions need an interpolation step (a Lipschitz/
continuity estimate for −Q_true, or a search over the full span). Until
that is supplied, item 12 has strong high-K evidence with a clean structure
but is **not closed**. At K=64 the reported figure is the gap, not the
search, so p=8 is too small there — that is a computation to redo, not an
obstruction.

## THE INTERPOLATION ESTIMATE — item 12's obstruction REMOVED

The blocker was that the fan bite N is homogeneous of degree 2 but **not a
quadratic form**, so a bound proved on a low-dimensional search space could
not be transported to mixed directions. Resolution: the PROVED bite bound is
quadratic once unwound.

    N(φ)+N(−φ) ≥ max_s d(s)²G(s)              [one interior cut, N12b]
               ≥ cot β · ‖d‖²_∞                [G ≥ G(0), Lean `fan_cut_gain`]
               ≥ (cot β/β) · ‖d‖²_{L²(0,β)}    [max ≥ mean]

and **d is LINEAR in η** (d(s) = φ(β)cos s/cos β − φ(s)). So ‖d‖²_{L²} is a
quadratic form D, and with Q_true = Q_rel − [N(φ)+N(−φ)],

    **−Q_true(η) ≥ M(η) := −Q_rel(η) + (cot β/β)·(D₁+D₂)(η),  M QUADRATIC.**

Coercivity of M is an ordinary eigenvalue problem, valid on **every direction
simultaneously — mixed included**. No search, no interpolation gap.
(cot β/β = 11.5838; d vanishes on translations, so the statement is modulo
the exact symmetry, as it must be.)

| K | −Q_rel alone | **m(M) = closed bound** | bite's share |
|---|---|---|---|
| 10 | 8.116 | **8.531** | 4.9% |
| 16 | 1.295 | **6.842** | 81.1% |
| 24 | 0.239 | **6.556** | 96.4% |

The released form alone collapses by 34×; M stays ≈ 6.6 with the bite
carrying 96% of it by K=24. Decrements 1.69 then 0.29 — settling near 6.5.

**Verified end to end**: on random directions in the K=24 span, M(η) ≤
−Q_true(η) held in every case, tight to 1–3% (e.g. 1974.7 ≤ 2021.5,
3487.0 ≤ 3537.4), with −Q_true evaluated by the exact Rust oracle.

**What this changes.** Item 12 is no longer blocked by a structural
obstruction (a non-quadratic functional resisting decomposition); it is
reduced to the STANDARD WELD applied to the quadratic form M — the same
block/tail/coupling argument already carried out for Gerver in Part II.
Remaining for that weld: Q_rel at K > 24 (needs a released mode in
`sigma_area.rs` — a flag skipping the cap outer walls), then the tail
constant c_T and coupling τ. Mechanical, not conceptual.

## THE WELD (item 12b) — FAILED as set up. Honest report.

The 2x2 block weld on M was run at four cutoffs. It fails at all of them:

| K | K0 | m_N | c_T | tau | tau^2 vs m_N c_T | verdict |
|---|----|-----|-----|-----|------------------|---------|
| 24 | 8 | 9.39 | 22.03 | 402 | 1.6e5 vs 207 | FAILS |
| 24 | 12 | 7.56 | 56.47 | 1077 | 1.2e6 vs 427 | FAILS |
| 24 | 16 | 6.84 | 509.7 | 1809 | 3.3e6 vs 3487 | FAILS |
| 16 | 8 | 9.39 | 121.4 | 389 | 1.5e5 vs 1140 | FAILS |

**Diagnosis (structural, not a cutoff choice).** In L² normalization the form
is UNBOUNDED — the Wirtinger terms scale like k² — so the tail block's
minimum (22, attained on cap-concentrated tail combinations) and the coupling
maximum (402, attained on entirely different directions) are reached in
different places. A 2x2 bound multiplies those two worst cases together and
is hopelessly lossy. It is lossy, not wrong: the FULL K=24 form has margin
6.56 > 0, so the failure is in the estimate, not in the mathematics.

**Why the Gerver weld does not transfer.** Part II's weld runs in H¹, where
k² is absorbed into the norm and the form is bounded. Σ has L² coercivity but
NOT H¹ coercivity (Q_struct's H¹ margins decay: 0.128 / 0.0069 / 0.0002),
because the bite is a frequency-INDEPENDENT mechanism. So the Σ tail needs an
estimate adapted to an unbounded form — a graded/multi-block weld, or a
direct proof that the K-limit of m(M) is positive — not the Part-II template.
That is a genuine setback for item 12b and is logged as one.

**Status of the M-ladder** (the quantity whose limit must be shown positive):
8.531 (K=10), 6.842 (K=16), 6.556 (K=24); decrements 1.69 then 0.29. K=32
running (`sigma_rel_hess.py`, released Rust oracle, ETA ~33m) to extend it.

## GRADED WELD — also FAILS.  Decomposition is the wrong tool.

Dyadic bands with optimized weights (`sigma_graded.py`), K=24, K0=6:

| band | k-range | lam_min | couplings |
|------|---------|---------|-----------|
| B0 | (0,6] | 9.81 | 287, 249 |
| B1 | (6,12] | 246.60 | 287, 1055 |
| B2 | (12,24] | 56.47 | 249, 1055 |

Optimized graded bound: **-1044.8**, against the true full-form margin
**+6.5555**.

**This is the informative failure.** The couplings (~1000) dwarf the band
minima (10-250), and lam is not even monotone in the band index. The form is
NOT approximately block-diagonal in frequency: its coercivity comes from a
cancellation spread across ALL modes at once. Therefore **no decomposition
weld can work** -- not 2x2, not dyadic, not any refinement. The Part-II
template is unavailable for Sigma at a structural level, not for want of
tuning.

## THE REMAINING MATHEMATICS, sharply posed

With decomposition excluded, item 12b reduces to ONE analytic statement. All
its ingredients are already proved or computed:

M(eta) >= int_0^{pi/2} W(t)|eta'(t)|^2 dt - C_0 ||eta||^2_{L2}
              + (cot b / b) ||d_eta||^2_{L2(caps)}

where W is the coverage weight (W ~ 1 on the middle phase, W ~ sin^2 t on the
caps -- N9), C_0 the interior-Garding constant (N5/N6 pattern), and d_eta the
cap deviation (linear in eta, vanishing exactly on translations -- N12).

**Lemma T (the target).** There is m > 0 such that for every eta orthogonal
to the translation direction,

    int W(t)|eta'|^2 dt  +  (cot b / b) ||d_eta||^2_{L2(caps)}
        >=  (m + C_0) ||eta||^2_{L2}.

This is a DEGENERATE-WEIGHT POINCARE INEQUALITY WITH BOUNDARY COMPENSATION:
the weight W vanishes at the two cap points, so the Poincare step fails there
on its own, and the d-functional must supply exactly the missing control.
That is precisely the division of labour the fan-bite mechanism was found to
implement, so the statement is the right one -- but it is a genuine piece of
analysis, not a computation, and it is NOT yet proved.

Status: CONJECTURE, supported by the M-ladder (8.531 / 6.842 / 6.556 at
K = 10/16/24, decrements 1.69 then 0.29) and by the tail probe (cap-x
saturating at ~3600 rather than decaying).

## LEMMA T — PROVED (compactness).  Item 12b reduced to one standard write-up.

**Lemma T.** There is m > 0 such that for every η ⊥ translations,
∫W|η′|² + (cot β/β)‖d_η‖²_{L²(caps)} ≥ (m + C₀)‖η‖²_{L²}.

*Proof.* Suppose not; take ‖η_n‖=1, η_n ⊥ translations, both terms → 0.
* On the middle W ≥ w_mid > 0, so η_n′ → 0 and η_n → a constant v there.
* On each cap the y-component has FULL coverage (weight cos²t ≈ 1 at the
  tip), so η_{n,y} → const with no degeneracy.
* The x-component is where W degenerates — exactly what the bite covers.
  Since d = φ − λ·cos for the specific λ = φ(β)/cos β,
  **‖d‖_{L²} ≥ inf_λ‖φ − λcos‖ = dist(φ, span{cos})** for free. So
  ‖d_n‖ → 0 forces φ_n → its cos-component in L² on the whole cap,
  tip included. No concentration escapes.
* Hence η_n → v constant. On a constant, φ(s) = v_x cos s + v_y sin s gives
  **d(s) = v_y(tan β·cos s − sin s)**, and on cap 2 (ψ(σ) = −v_x cos σ +
  v_y sin σ) the identical expression. Both vanish **iff v_y = 0**, i.e. iff
  v is a HORIZONTAL translation — precisely Σ's true symmetry. Orthogonality
  gives v = 0, contradicting ‖η_n‖ = 1. ∎

The constant-direction computation is verified to 1e-16: v=(1,0) gives
d ≡ 0 exactly, v=(0,1) gives ‖d‖ = 0.0931.

**Why this works where welds cannot.** Decomposition tries to certify each
frequency band separately; the form's coercivity is a cancellation across all
bands at once, so that is hopeless. Compactness never decomposes — it only
needs the degenerate directions to be identified, and the fan bite identifies
them exactly (it vanishes precisely on the true symmetry).

**Status, stated exactly.** Lemma T is PROVED *conditional on* the Gårding
structure ∃C₀ : M ≥ ∫W|η′|² − C₀‖η‖² + c‖d‖². That structure follows by the
standard argument from the proved per-arc Wirtinger forms (N5), the computed
mask table, and an ε-split — **but it has NOT been written out**, so it is
labelled *route*, not PROVED, and the effective label of item 12b is that of
its weakest link. Also: compactness gives a NON-EXPLICIT m, so the
quantitative modulus (≈6.5) still comes only from computation.

**12b-iii IS NOW WRITTEN** (Proposition 7', SIGMA_LOCAL.md §10): the Gårding
structure follows from N5 (per-arc forms) with the ε-split, N9 (frame-pair
Gram, giving W ≍ sin²t on the released caps), and N7 (breakpoint
reparameterization, which removes the pointwise-η′ junction terms — the
classical two-norm obstruction); junction values at β, π/2−β are absorbed by
Agmon localized to the middle phase, where W is non-degenerate.

**Therefore item 12b is PROVED (qualitatively): −Q_true ≥ m‖η‖²_{L²} for some
m > 0.** The constant is non-explicit; the computed value is ≈6.5.

**What Theorem 9 now is.** Every analytic link is PROVED. The remaining
dependency is COMPUTATIONAL: the released contact structure (which arcs are
active where), established by the mask table and the traversal (junction
residuals ~1e-10, Green area = A_R* to 2.6e-9). So Σ-local is a
**computer-assisted theorem**, with the contact structure as its computational
core — the same standard as Part II for Gerver, and as Baek's global result.
It is NOT a fully symbolic proof, and the modulus is not explicit.

## ADVERSARIAL REVIEW OF THE S7 CHAIN (Rule 6) — one real defect found

Four attacks survived, one landed. S7's label is DOWNGRADED accordingly.

**SURVIVED — quantifiers in Lemma T.** ‖d_n‖→0 gives φ_n − λ_n cos → 0 with
λ_n = φ_n(β)/cos β a POINT VALUE, not controlled by ‖η_n‖_{L²}. It is
controlled because β lies in the middle phase where H¹ control holds, so λ_n
is bounded and a subsequence converges. Step was missing from the write-up;
it holds. Added.

**SURVIVED — shape of the limit.** The cap weight sin²t degenerates only AT
t=0, so ∫sin²t(η_x′)² → 0 still forces η_x′ = 0 a.e. on (0,β). The limit is
constant on the caps; the bite control and the weighted-derivative control
agree (over-determined).

**SURVIVED — C₀ independence.** C₀ depends only on β, the mask table and the
arc count; the Agmon absorption uses the middle phase only.

**SURVIVED — circularity.** Lemma T → Prop 7′ → N5/N7/N9/masks. Acyclic.

**LANDED — ONE-SIDEDNESS. 🌊** Q_true from second differences is the AVERAGE
of the two one-sided second variations. Local maximality needs each branch:

    F(±ε) − F₀ = −(ε²/2)[ −Q_rel + 2N(±φ) ] + O(ε³),

so the + branch requires −Q_rel + **2N(φ)** > 0, whereas M bounds
−Q_rel + N(φ) + N(−φ). Because the bite is genuinely one-sided (measured
N(φ)=0, N(−φ)=26.24 on cap 1), these differ. **Theorem 9 as assembled bounds
the symmetric second difference, not the quantity local maximality needs.**

*Missing piece — Lemma O.* On the cone where both caps are outward (zero bite
on that branch), −Q_rel alone must be coercive. Evidence: of 200 000 random
K=24 directions, 1990 lie in that cone and over them min −Q_rel = **1470**,
against a global minimum of **0.201** — the dangerous near-null directions are
oscillatory and bite on BOTH branches, as the mechanism predicts. Encouraging,
but 1990 samples in 48 dimensions is thin sampling, and Lemma O is NOT proved.

**ALSO NOTED — endpoint restriction.** Prop 7′ discards endpoint junction
terms using η(0)=η(π/2)=0, i.e. it is proved on the endpoint-vanishing
subspace only. Part II handled the general case with extra work (slope
carriers, τ_s = 0.063). Not done for Σ. This caveat was NOT stated when
Theorem 9 was assembled; it is stated now.

**REVISED STATUS.** S7 drops from PROVED to CONJECTURE. What stands: 12a
(interpolation), 12b-ii (Lemma T), 12b-iii (Prop 7′ on the endpoint-vanishing
subspace) — all PROVED. What is missing: Lemma O (one-sidedness) and the
endpoint-general case. The review did its job: a chain assembled in one
session was bounding the wrong quantity, and no result was built on it.

## ONE-SIDEDNESS: FALSIFICATION RUN (2) AND LEMMA O (1) — the result is negative for a UNIFORM statement

**(2) Falsification.** Minimised G(η) := −Q_rel(η) + 2[N₁(φ)+N₂(ψ)] over the
whole sphere (which covers both branches, since G₋(η) = G₊(−η)), by projected
gradient with 200 restarts seeded on the near-null eigendirections.

  min G = **0.2328** at K=24, of which −Q_rel = 0.2321 and the bite = 0.0007.

No counterexample: G > 0. **But the margin is essentially −Q_rel's own margin,
and the bite contributes nothing there.** The exact bite at that direction
(computed with `bite_area`, not the bound) is 0.0072 — 2.8x the lower bound
and still negligible. Confirmed against the TRUE oracle: at that direction
G(+) = 0.32–0.56 and G(−) = 98.0. Both branches strictly decrease, so local
maximality holds THERE, but one-sidedly the decrease is weak.

**(1) Lemma O.** Minimised −Q_rel on the zero-bite cone {d₁ ≤ 0, d₂ ≤ 0} by
penalty + projected gradient: **min = 0.2966** (constraint violation 0).
Lemma O holds numerically at K=24 — but note this demolishes the earlier
random-sampling estimate of 1470, which was worthless in 48 dimensions. The
cone does contain near-null directions of −Q_rel.

**CONSEQUENCE — the uniform one-sided statement is not supported.** −Q_rel's
L² margin decays: 8.116 / 1.295 / 0.239 at K = 10/16/24. Since the one-sided
minimum tracks it (the bite vanishing exactly where −Q_rel is small), the
one-sided margin decays too. So:

* the SYMMETRIC second difference is uniformly coercive (M ≥ ≈6.5, K-stable) —
  this stands;
* the ONE-SIDED branches are strictly negative at every direction tested, but
  with NO uniform L² modulus.

**S7 must therefore be restated.** "Σ is a strict local maximum with L²
modulus m > 0" is NOT established and the evidence suggests it is FALSE AS
STATED — the modulus degenerates along outward cap-oscillatory directions.
What the computations support is the weaker claim that Σ is a local maximum
whose second-order decrease is directionally strict but not uniformly so in
L². Identifying the correct norm (or the correct weaker statement) is now the
open problem, and it is a different problem from the one this section set out
to solve.

## 🌊 RED FLAG ON PART II — the structure-following form may not dominate

Audit of the Gerver chain for the same one-sidedness defect. Added a GERVER
mode to `sigma_area.rs` (single hallway family) to get an exact one-hallway
true area, and compared against the structure-following oracle
(`true_hessian probe`) on ADMISSIBLE (endpoint-vanishing) sine modes:

| mode | eps | true dF | struct dF | struct >= true? |
|------|-----|---------|-----------|-----------------|
| e_x sin2t | ±2e-3 | −9.2991e-6 | −9.6072e-6 | **NO** |
| e_x sin6t | ±2e-3 | −6.6213e-5 | −6.9123e-5 | **NO** |
| e_y sin4t | ±2e-3 | −4.1826e-5 | −4.1766e-5 | yes |

**Not discretization**: refining n 1201→2401 moves true dF by 9e-9 against a
gap of 3.2e-7. The structure-following form decreases MORE than the true area
on the x-modes, i.e. F_struct <= F_true there — domination the WRONG WAY.

**Why this is geometrically expected, and where the earlier L4 audit erred.**
A structure-following arc that detaches INWARD cuts into the body, so the
form is not a superset upper bound. The FROZEN reconstruction with chords is
the upper bound (chords bridge gaps from outside); structure-following is
neither in general. The L4 entry earlier in this session asserted that the
Part-II jet oracle "is the smooth structure-following SUPERSET form ... so the
manuscript's ladder-negativity chain is VALID and strengthened". **That
assertion is now contradicted by direct measurement and is withdrawn.**

**What is and is not at risk.** The manuscript's reduction theorem uses the
FROZEN reconstruction, which is superset-valid (lem:superset, Lean-verified),
and the K=16 frozen block is certified negative definite — that part stands.
At risk is the step that leans on the true-Hessian ladder (m∞ ≈ 0.765) to
carry the argument past K=32, where the frozen form goes indefinite: if the
structure-following object does not dominate the true one-sided response,
negative definiteness of that ladder does not by itself give one-sided local
maximality. The envelope identity (N3) is what relates the two families and
is the natural place to repair or refute this.

**Status: FLAGGED, not concluded.** Three sine modes are not an audit. The
required work is (i) a systematic sign test across many modes and amplitudes,
(ii) checking whether the gap is an O(eps^3) artifact rather than a second-
order one, and (iii) re-deriving what the envelope identity actually licenses.
Part II's headline result is NOT withdrawn; it is marked at risk pending that
audit.

## PART II SIGN TEST — INCONCLUSIVE (oracle validity must be settled first)

Systematic order test of D(ε) := dF_struct − dF_true across 9 modes and three
amplitudes (`gerver_domination.py`), exact true area from `sigma_area` GERVER
mode:

| mode | D(2e-3) | local order | reading |
|------|---------|-------------|---------|
| e_x sin2t | −3.08e-7 | 2.09 | plausible |
| e_x sin4t | **−6.46e-3** | **1.00** | implausible |
| e_x sin6t | −2.91e-6 | 2.16 | plausible |
| e_x sin10t | −8.14e-6 | 2.29 | plausible |
| e_x sin16t | **−2.58e-2** | **1.01** | implausible |
| e_y sin2t | +2.84e-7 | 1.04 | small, unclear |

**Two findings, one of them not mathematics.** A discrepancy LINEAR in ε means
one functional is not critical at c_G in that direction. F_true is critical, so
a linear term of size 1e-2 must come from the structure-following oracle —
and junction-solve failure on particular modes is a documented failure mode of
`true_hessian` in this project (basin jumps, kink stalls, transition-straddling
stencils, all fixed piecemeal). Those rows are almost certainly broken solves.

**On the clean modes the discrepancy IS O(ε²)** — about 1.7% of the second
variation, with structure-following slightly MORE negative than true
(Q_struct ≈ −4.80 vs Q_true ≈ −4.65 for e_x sin2t). So the ε³ hypothesis
formed from two data points is REFUTED by the third point. What this implies
is narrow: on these modes both forms are clearly negative, so the CONCLUSION
holds; what fails is the automatic implication Q_struct < 0 ⟹ Q_true < 0.

**Status: INCONCLUSIVE.** The test cannot be read until the structure-following
oracle is validated mode by mode against the independent mpmath analytic
oracle, so that broken solves are separated from real discrepancies. Part II's
flag stays open, neither confirmed nor cleared.

**Method note for the log.** Twice now in this session an exponent was inferred
from two amplitudes and was wrong (first the "3/2-law" of N11, now this ε³
reading). Two points determine a slope and nothing else. Order claims need at
least three amplitudes plus an independent check.

## ORACLE VALIDATED — and it exposes a NONZERO FIRST VARIATION 🌊🌊

**Task 1 result.** `true_hessian` (Rust) agrees with `analytic_oracle`
(independent mpmath implementation) to **4.4e-16** on every mode tested, with
identical junction values. There is no solver bug. The earlier "implausible"
rows are real behaviour of the object.

**What the scaling test shows** (six amplitudes, 5e-5 … 2e-3):

| mode | behaviour | reading |
|------|-----------|---------|
| e_x sin2t (k=1, odd) | 2dF/ε² → −4.812, stable to 4 digits | clean quadratic |
| e_x sin4t (k=2, even) | dF = −3.23·ε, EXACTLY linear | nonzero 1st variation |
| e_x sin16t (k=8, even) | dF = −12.9·ε, EXACTLY linear | nonzero 1st variation |

Junction moves scale linearly with ε throughout — no basin jump, no
continuation failure. **The structure-following functional is NOT STATIONARY
at c_G in the even-k x-modes**, while the true functional is. Those are
precisely the modes ANTISYMMETRIC under t → π/2 − t, i.e. the ones breaking
Gerver's symmetry.

**Transfer (Rule 1): singularity theory of envelope unfoldings.** The
discrepancy F_struct − F_true is the SIGNED AREA OF SELF-INTERSECTION LOOPS of
the traced curve: when an arc detaches, the structure-following curve develops
a swallowtail, and Green's theorem counts the loop with a multiplicity that is
wrong for the true region. A loop that appears LINEARLY in ε contributes a
linear term — exactly what is measured. At a DEGENERATE fan the same mechanism
is ε²-homogeneous, which is N12. So N12 and this defect are one phenomenon at
two unfolding types.

**Consequences, carefully bounded.**
* The LADDER NUMBERS are unaffected: a second difference
  (F(+ε) − 2F(0) + F(−ε))/ε² annihilates any linear term. So Part II's
  m₁(K) = 0.805…0.775 remain what they always were.
* What fails is the INTERPRETATION: with a nonzero first variation,
  F_struct is not a stationarity-preserving surrogate, so "Q_struct < 0"
  cannot be read directly as one-sided local maximality.
* The frozen reconstruction is unaffected (its linear term vanishes by
  criticality, and it is superset-valid) — the certified K=16 chain stands.

**Open and now sharply posed.** Either (i) both oracles share an arc-range
convention that is wrong on symmetry-breaking modes, or (ii) the
structure-following object genuinely fails stationarity there. These are
distinguishable: compare the first variation against the frozen form's, which
is provably zero. That is the next test, and it decides whether Part II's
ladder step needs repair or merely reinterpretation.

## 🌊🌊🌊 THE SUPERSET SIDE CONDITION FAILS AT FIRST ORDER (Part II foundation)

**Test.** First variation of the FROZEN reconstruction (junctions fixed at
c_G) versus the structure-following one, ε = 2e-4:

| mode | frozen dA/dε | struct dA/dε | |
|------|--------------|--------------|---|
| e_x sin2t | 2.2e-12 | 1.1e-12 | both zero |
| e_x sin6t | −2.2e-12 | −1.9e-11 | both zero |
| e_y sin4t | 3.3e-12 | 4.4e-12 | both zero |
| **e_x sin4t** | **−3.227526** | **−3.227527** | **both NONZERO** |
| **e_x sin16t** | **−12.91011** | **−12.91011** | **both NONZERO** |

Two facts, both clean. (a) Frozen and structure-following first variations
agree to SEVEN digits — the envelope identity N3 is confirmed directly:
junction solving does not change the first variation. (b) Both are nonzero on
the even-k x-modes, the ones antisymmetric under t → π/2 − t.

**The consequence is structural.** If a reconstruction satisfies R(Γ) ⊇ S with
equality at c_G, then A_rec − A_true ≥ 0 attains a minimum at c_G, so its first
variation MUST vanish. It does not. Equality at c_G does hold (both give A*).
Therefore **the reconstruction is NOT superset-valid for symmetry-breaking
perturbations**: Γ_ε cuts into the body, at ARBITRARILY SMALL ε.

**This is the same phenomenon as the L2-CORRECTION** logged earlier in this
session, where the frozen curve was found to genuinely self-intersect at
ε ≈ 0.45 along the x-ray. There it appeared at large ε; here it appears
immediately. One mechanism — the swallowtail of the envelope unfolding —
with the loop area entering linearly.

**What this means for Part II.** The manuscript's reduction theorem
(thm:reduction) applies Lemma superset to Γ_ε under an explicit side
condition: simplicity of the reconstruction for ε‖η‖_{C¹} ≤ r₀. The present
measurement says that side condition FAILS for symmetry-breaking directions
at every ε > 0, i.e. r₀ = 0 for those η. So the reduction theorem does not
cover them, and the chain that concludes local maximality from negative
definiteness has a genuine hole on half the mode space.

**Not withdrawn, but the burden has moved.** The K=16 certified frozen block
and the ladder numbers are unaffected as COMPUTATIONS. What is affected is the
theorem that consumes them. Establishing Part II now requires either (a) a
repaired reconstruction that is superset-valid on symmetry-breaking modes, or
(b) the winding-number form of the superset lemma (wind ≥ 1 on S, ≥ 0 off),
already identified in the L2 work, which tolerates self-intersection and
counts loops correctly.

**Route (b) was proposed on the swallowtail hypothesis — FIRST TEST NEGATIVE.**
Tracing the A-arc at ε=1e-3 for both a symmetric (sin2t) and a symmetry-
breaking (sin4t) mode found **ZERO self-crossings** and zero loop area, against
a predicted loop area of 3.2275·ε = 3.2e-3. So the linear term is NOT explained
by an A-arc swallowtail. The test is incomplete — it does not cover crossings
between DIFFERENT arcs — but the hypothesis is unconfirmed and must not be
used as an explanation until a loop is actually exhibited. **The mechanism
producing the first-order discrepancy remains UNKNOWN.**

## M-LADDER COMPLETE: the symmetric bound is K-stable

| K | 10 | 16 | 24 | 32 |
|---|----|----|----|----|
| m(M) | 8.5314 | 6.8415 | 6.5555 | **6.4806** |

Decrements 1.69, 0.286, 0.075 — ratio ≈0.26 per step, extrapolating to
**≈6.45**. The symmetric-second-difference coercivity of Σ is K-stable, now
confirmed to K=32 with the exact released oracle. This result is independent
of the Part II difficulties above and of the one-sidedness gap; it is what
stands from the Σ line.

## MECHANISM LOCALIZED: a cancellation that holds only on symmetric modes

**Both sides now measured.**

*True functional* (exact one-hallway oracle): dA_true/dε = 0 for every mode.
For sin4t and sin16t the residuals SHRINK with ε (−5.8e-5 → −8e-6 as ε goes
4e-4 → 2e-4, scaling ~ε^2.8), i.e. they are higher-order, not a first
variation. c_G is critical in all directions, as it must be.

*Reconstruction* (both oracles, frozen and structure-following agreeing to 7
digits): dA_rec/dε = −3.227527 (sin4t), −12.91011 (sin16t) — CONSTANT in ε.

So **δA_true = 0 while δA_rec ≠ 0** on the symmetry-breaking modes. The
reconstruction and the body agree in value at c_G but not in first derivative.

**Term-by-term decomposition** of the Green sum (IA, IC, ID, Ix, IB, and the
three closing segments) at ε = 2e-4:

| mode | IA | IC | ID | Ix | IB | S2 | S3 | total |
|------|----|----|----|----|----|----|----|-------|
| sin2t (sym) | −0.345 | +1.573 | +0.526 | −0.490 | −0.036 | −1.421 | +0.193 | **−0.000000** |
| sin4t (antisym) | −1.611 | −4.066 | +0.355 | −1.182 | +0.049 | +2.841 | +0.386 | **−3.227527** |

**There is no single culprit piece.** Every term is individually large and
nonzero in BOTH cases; for symmetric modes they cancel to machine zero, and
for antisymmetric modes the cancellation simply fails. So the defect is not a
mis-specified arc range or a wrong sign on one term — it is that the
reconstruction's global first-order balance is tied to the t → π/2 − t
symmetry of c_G, and antisymmetric perturbations break it.

**Status.** Mechanism localized but not yet explained: we know WHAT fails (the
global cancellation) and on WHICH modes (antisymmetric), not WHY the identity
is symmetry-dependent. The earlier swallowtail hypothesis is not supported (no
self-crossing found). Part II's reduction theorem remains holed on those modes.

**This is the correct place to stop and think rather than compute.** The next
step is analytic: derive δA_rec in closed form from the per-arc formulas and
compare against the classical first-variation formula δA = ∮ v_n ds for the
true body, term by term. The difference is then an explicit expression whose
vanishing on symmetric modes should be visible.

## Σ RECONSTRUCTION IS CLEAN — this session's Σ results are unaffected 🔥

Safety check (task 3): first variation of the Σ reconstruction vs the true Σ
area, all modes k = 1..6 in both components, ε = 2e-4.

**Every dA_rec/dε is ~1e-6 or smaller** (quadrature noise) — symmetric and
antisymmetric modes alike. (The true column scatters up to 2e-3, which is
polygon discretization at n=1201; the reconstruction column is uniformly
tiny.) So the Gerver defect does NOT appear in Σ, and the Σ results of this
session — N9, N12, the interpolation estimate, Lemma T, Prop 7', the K-stable
symmetric coercivity ≈6.45 — do not inherit it.

**Why the difference is itself the lead.** Σ's traversal was DERIVED
empirically (mask table + arc matching + junction solve) and validated (Green
area = A_R* to 2.6e-9, junction residuals ~1e-10). Gerver's arc table was
inherited. A wrong range or orientation would cancel at c_G by its t → π/2 − t
symmetry and fail off it — exactly the observed pattern.

## Gerver traversal map — a lead, not yet a verdict

Mapping ∂S the way ∂Σ was mapped (700 boundary probes, n=2401):

    measured:  X [0.0458, 1.5296] · D [0.619, 0] · C [1.516, 0] ·
               X [0.9746, 0.5989] · A [1.5708, 0.0550] · B [1.5708, 0.9117]
    assumed :  A [0, PI2] · C [0, PI2] · D [0, TH=0.6813] ·
               B [PI2-TH=0.8895, PI2] · X [PHI=0.0392, PI2-PHI]

Two discrepancies worth chasing: (a) the corner path X appears in TWO runs, the
second traversed backwards over [0.599, 0.975], where the assumed table has it
once; (b) the arc endpoints differ from the assumed ones (A from 0.055 not 0,
C to 1.516 not PI2) — though A's start is expected, since the phase-1 fan is
stationary on [0, PHI] and the table extends it there deliberately.

**Not conclusive**: 700 probes is coarse and nearest-arc matching can
mis-assign points where two arcs run close together. The doubled X run must be
confirmed at higher resolution before any claim. But if real, a duplicated or
mis-oriented corner segment is exactly the kind of error that cancels on
symmetric perturbations and not on antisymmetric ones.

**Task 1 (closed-form δA_rec vs ∮v_n ds) is NOT done.** The empirical lead
above is a substitute for direction, not for the derivation.

## THE DOUBLED-CORNER LEAD IS DEAD (matching artifact)

Re-mapped ∂S at 5000 probes with match distances reported:

| run | probes | median distance |
|-----|--------|-----------------|
| X | 1357 | 1.27e-4 (good) |
| D | 344 | **9.75e-2** |
| C | 1258 | 1.24e-4 (good) |
| X (2nd) | 439 | **3.57e-1** |
| A | 1258 | 1.24e-4 (good) |
| B | 344 | **9.78e-2** |

The suspicious runs are not matches at all — distances of 0.1 to 0.36. Gerver's
boundary contains STRAIGHT WALL SEGMENTS which the matcher did not include, so
those probes were assigned to whatever arc happened to be nearest. **The
doubled corner run is an artifact; the arc table is not shown to be wrong.**

## δA_rec DERIVATION — the criterion, and why B alone is not the answer

For a p-slot arc, δP = pμ + p′ν and P′ = λν, so the Green integrand is
δP∧P′ = **p·λ**, while the true first variation contributes
⟨η,n⟩·(ds/dt) = **p·|λ|**. They agree iff λ > 0. For a ν-slot arc,
δP = −q′μ + qν and P′ = λ_C μ give δP∧P′ = **−q·λ_C**, which agrees with
q·|λ_C| iff λ_C < 0. So each arc's table sign must match its wedge
orientation, and the criterion differs by slot.

Measured envelope speeds on the assumed ranges:

| arc | λ range | fraction λ<0 | slot | consistent? |
|-----|---------|--------------|------|-------------|
| A | [0, +1.399] | 1% | p | yes |
| C | [−1.399, 0] | 98.2% | q | yes (ν-slot self-corrects) |
| D | [+0.132, +0.500] | 0% | q | **no — λ>0 on a ν-slot** |
| B | [−0.500, −0.132] | 100% | p | **no — λ<0 on a p-slot** |

So B and D are the two arcs whose slot formula and speed sign disagree.

**But this does not yet explain the magnitude.** From the term decomposition,
IB = +0.0488 and ID = +0.3546 for sin4t; flipping both signs moves the total by
−0.807, against a defect of −3.2275. So the sign criterion identifies a real
inconsistency but is NOT the whole mechanism. Something else contributes the
bulk.

**Honest status.** The derivation produced a genuine structural criterion and
two candidate arcs, and killed the previous lead. It did not close the
question. The remaining work is to carry the δA_rec computation through in
closed form — including the chord/segment terms, which the decomposition shows
are large (S2 = +2.841 on sin4t) and which no hypothesis has yet addressed.

## GERVER TRAVERSAL RE-DERIVED — the arc table is CORRECT

Re-mapped ∂S the way ∂Σ was mapped, this time classifying probes that match no
arc (tolerance 2e-3, 4000 probes):

    X(corner) 1086 · D 95 · STRAIGHT y=0 (−1.4245,0)→(−2.2235,0) ·
    C 639 · STRAIGHT y=1 (−1.4169,1)→(+0.1900,1) ·
    A 638 · STRAIGHT y=0 (+0.9976,0)→(+0.1964,0) · B 94

All three straight pieces have max deviation 0 (exactly straight). This
reproduces the assembly's "three outer segments are FIXED wall lines", and the
arc pairings across the segments — {C,D}, {A,C}, {A,B} — match the assumed
closing terms seg(Ce,D0), seg(Ae,C0), seg(Be,A0).

**The arc table's structure is correct.** Fourth hypothesis eliminated (after
basin jump, swallowtail, and mis-specified ranges).

## LEAN F7/F8, and an honest analysis of what blocks "no more HEURISTIC"

### What was added (7 theorems, all VERIFIED)

`lake build` clean, zero sorry, `#print axioms` reports only `propext` and
`Quot.sound` for each -- no `Classical.choice`.  32 theorems total in the file.

    intersection_chain   F7a  the S8 route's chain: dominance + margin + slack
                              gives atrue <= astar + s - m.  Pins the quantifiers
                              and shows exactly where the slack enters.
    slack_squeeze        F7b  x <= y + s_n for all n, some s_n <= 0, gives x <= y
                              (the Int-exact form of "let the slack tend to 0")
    sq_nonneg_int        F8   0 <= x*x
    weighted_sq_nonneg   F8   0 <= d*x^2 for d > 0
    weighted_sq_pos      F8   0 < d*x^2 for d > 0, x != 0
    sum_nonneg           F8   non-negative entries have non-negative sum
    sum_pos_of_one_pos   F8   non-negative entries with one positive give a
                              positive sum -- the step from a sum-of-squares
                              certificate to STRICT definiteness

Note on tooling, recorded so it is not rediscovered: core Lean has NO `ring` and
no `positivity`.  Degree-4 identities (e.g. the 2x2 Sylvester identity
a(au^2+2buv+cv^2) = (au+bv)^2 + (ac-b^2)v^2) are therefore impractical: `simp` with
`Int.add_mul, Int.mul_add, Int.mul_comm` plus `omega` handles degree 2 but fails on
the 4-fold products.  This is why F8 formalizes the LOGIC of a certificate rather
than the algebraic identity producing one.

### The two different things being called HEURISTIC

They need separating, because only one of them is a formalization problem.

(1) STRUCTURAL claims measured numerically but with an available exact route.
    Example: G8a, the corner-region coverage margin (+3.852e-05, converged under
    t-refinement).  The obstruction is that it is stated as "min over a region of
    max over t"; the reduction q in Q_t <=> arg(q-c(t)) - t in (pi,3pi/2) turns it
    into 1-D root existence, which is attackable analytically.  This is ordinary
    mathematical work, not a tooling problem.

(2) LADDER MARGINS -- the eigenvalue claims (G7 -5.021155, G10 -4.948650,
    S8a -6.029329).  These CANNOT be lifted by formalization alone, and it is worth
    being exact about why:

      * the Hessian entries are CENTRAL DIFFERENCES of a floating-point polygon
        area.  FD truncation error is O(eps^2 * M4) with M4 a fourth-derivative
        bound that is not currently known, so there is no rigorous enclosure of
        the entries -- and without an enclosure there is nothing for a Lean proof
        to consume;
      * the polygon vertices involve cos/sin of grid angles, so exact rational
        arithmetic is not directly available either.

    Formalizing `sum_pos_of_one_pos` supplies the LAST step (certificate implies
    definiteness).  The MISSING step is the certificate itself, in exact
    arithmetic.

### The route that already has precedent in this project

`certify_sigma_struct.py` did exactly this for Q_struct: closed-form assembly, arb
ball arithmetic at 300 bits (radius ~1e-90), Sylvester's criterion on the ball
matrix, minors positive through order 20.  That produced a genuine
computer-assisted proof, not a HEURISTIC.

For |R_n| the same route is available and the reason is N10 (certified cell-wise
QP): on each COMBINATORIAL CELL -- a fixed set of active constraints and a fixed
vertex incidence -- the polygon area is a POLYNOMIAL in the trajectory
coefficients.  So on the cell containing c_R the Hessian of |R_n| is closed-form,
and can be assembled and certified in ball arithmetic exactly as Q_struct was.
The steps are:

  1. identify the active-constraint cell at c_R (which half-planes and which wedge
     edges contribute vertices, and in what cyclic order);
  2. write |R_n| on that cell as an explicit polynomial in the mode amplitudes;
  3. differentiate it exactly (no finite differences);
  4. certify negative definiteness in arb by Sylvester minors;
  5. check the perturbation stays inside the cell -- a separate inequality, and
     the one that the old ray/cell certificates (N10, ray_graph_cert.py) exist to
     supply.

Only after step 4 does the margin become PROVED, and only after step 5 does it
mean anything for local maximality.  Until then S8a stays HEURISTIC, and saying
otherwise would be false.

### Honest status of the demand

"Formalize everything" is achievable for the structural and logical content, and
that has now been done as far as core Lean allows (F1, F6, F7, F8, plus the
existing F2-F4).  It is NOT achievable for the ladder margins without first
producing exact-arithmetic certificates, which is steps 1-5 above and is the
principal remaining piece of work in the whole program.
## 🔥🔥🔥 S8 RESULT: THE INTERSECTION RECONSTRUCTION IS NEGATIVE DEFINITE

The Hessian of |R_n| at K=16, n_theta=1201 (Rule-8 checkpointed, 528 entries,
12.4 min):

    spectrum min -3191.1305    max -2.892347
    8 largest: -97.4496 -96.9738 -51.1693 -48.8627 -28.0820 -23.3920
               -6.0293 -2.8923
    translation projected out:  max -6.029329
    NEGATIVE DEFINITE,  margin 6.029329

This is a Σ ladder against a reconstruction with NO exposure to either failure
mode: no chords (Mode 1 impossible) and a region area rather than a signed Green
sum (Mode 2 impossible), and superset validity is immediate from
`superset_principle`, which is machine-verified.  For comparison the old margin
under the signed evaluation was 6.4563; the intersection bound is slightly looser,
as a coarser bound should be.

WHAT THIS IS, PRECISELY.  One (K, n) pair.  The construction trades "equality at
the base point" for "uniformity in n", so certifying Theorem 9 this way now needs
TWO ladders, not one:

  * the n-ladder, that the margin does not degrade as n grows (the superset slack
    C/n -> 0 while the margin must stay bounded below);
  * the K-ladder, as before, plus the tail bound above K.

Neither is done.  What IS established is that the route exists and its first rung
is clean, after two sessions in which every route was breaking.

Command: `python3 sigma_inter_hess.py 16 1201 1e-4 40` -> sigma_inter_K16_n1201.npy.

## G10: GERVER'S CHORD-FREE HESSIAN IS NEGATIVE DEFINITE AT K=16 AND K=24  🔥🔥

The chord-free reconstruction's second variation, computed against A_rep (not the
chorded A_rec), Rule-8 checkpointed:

    K=16  spectrum min -1473.727246   max -4.273730
          translation projected out:  max -5.021155   NEGATIVE DEFINITE
    K=24  spectrum min -3389.505756   max -4.186595
          8 largest: -70.8345 -61.2017 -40.5484 -34.6700 -17.4225 -14.8465
                     -4.9487 -4.1866
          translation projected out:  max -4.948650   NEGATIVE DEFINITE

Margin 5.021155 -> 4.948650 from K=16 to K=24, a drop of 0.0725.  So the K=16
result is NOT a truncation artifact, and the margin is settling near 4.95.

Combined with A_rep(c_G) = A* to 7.2e-11, stationarity to +-1.7e-10 on every mode,
the containment certificate, and the corner criterion, Part II's local chain now
holds at K=24 with only two items open: G8b (the corner margin analytically rather
than as a certificate) and G9 (a tail bound against A_rep rather than A_rec).

Commands: `gerver_rep_hess.py 16 22 1e-5`, `gerver_rep_hess.py 24 20 1e-5`.
Sizing note carried: high-k entries are much slower than a linear ETA suggests
(oscillatory mp.quad); K=24 took 48 minutes against a 26-minute initial estimate.

## S12: the N12 bite does NOT absorb the lens — they live on OPPOSITE branches  💧💧

Time-boxed cheap test before committing to the expensive route.  The Mode-2 repair
costs L/gl of margin; the Σ dichotomy already credits a one-sided bite bonus
2(N1+N2).  Does the bite cover the lens, branch by branch?

    dir  eps      L(v)     L/gl    2(N1+N2)   absorbed?
    1   +0.004   1.1006   1.4013     6.1968     yes
    1   -0.004  10.4068  13.2503     0.4677     NO
    1   +0.002   1.1116   1.4154     6.1968     yes
    1   -0.002   9.8576  12.5511     0.4677     NO
    2   +0.004   1.3458   1.7135     8.7690     yes
    2   -0.004   3.9058   4.9730     0.0623     NO
    2   +0.002   1.1748   1.4958     8.7690     yes
    2   -0.002   3.8279   4.8739     0.0623     NO
    3   +0.004   0.7606   0.9685     0.1269     NO
    3   +0.002   0.8092   1.0303     0.1269     NO
    (dir3 negative branch skipped: matched residual 2.5e-1)

NO on 5 of 10 probes, and the pattern is worse than a mere shortfall: **the bite is
small exactly where the lens is large.**  On direction 1 the bite is 6.20 on the +
branch where the lens costs 1.40, and collapses to 0.4677 on the − branch where the
lens costs 13.25.  The two one-sided objects are supported on OPPOSITE branches, so
no reweighting of the dichotomy can absorb Mode 2.  S12 is a clean negative and the
cheap route is closed.

METHOD ERROR CAUGHT AND FIXED, recorded because it nearly produced a false
positive.  The first version of the test compared G_corr = -Q/gl + bite - L/gl
against 0 on RANDOM directions and reported "the dichotomy absorbs Mode 2".  That
is meaningless: -Q/gl is the RAYLEIGH QUOTIENT on a random direction (measured
128-308), which has nothing to do with the margin, which is the MINIMUM eigenvalue
(6.4563).  Any random direction passes.  The correct statistic is the absorption
ratio bite/(L/gl), which must be >= 1; its worst value here is far below 1.

## S8: the reconstruction that avoids ALL THREE failure modes is not a curve

Trimming arcs at their crossings was the plan.  There is a cleaner object.  Take

    R_n(c) := intersection over a grid t_1..t_n of H_{t_i}(c).

Then:

  * S(c) ⊆ R_n(c) for EVERY c, directly by `superset_principle` -- no hypothesis
    about chords, supporting lines, or simplicity.  MODE 1 cannot arise (there are
    no chords at all) and MODE 2 cannot arise (a region area is computed, never a
    signed Green sum).
  * |R_n(c)| is computed EXACTLY by polygon arithmetic: half-plane clipping plus
    the exact wedge subtraction already implemented and validated in
    `sigma_area.rs`.
  * |R_n(c_R)| = A_R* + C/n, so equality at the base point holds only in the
    limit.  Measured at n = 1201: 1.6450802579 against A_R* = 1.6449552184, slack
    +1.250e-04, positive as a superset bound must be.

The base-point slack is harmless.  If the Hessian margin m is uniform in n,

    A_true(c_R + eps eta) <= |R_n(c_R + eps eta)|
                          <= A_R* + C/n - (m/2) eps^2 ||eta||^2,

and letting n -> infinity gives the exact statement: the offset vanishes, the
quadratic decrease survives.  So uniformity in n replaces equality at the base
point, and that is a ladder in n rather than a new geometric construction.

### The realisation that makes this cheap

`sigma_area.rs` ALREADY COMPUTES |R_n|.  It is the same binary this project has
been calling "the exact true-area oracle", and what was recorded throughout as its
"offset C/n" is precisely the superset slack -- not an error to be subtracted, but
the very quantity that vanishes in the limit.  No new Rust is needed; the object to
certify is the Hessian of the oracle itself, and `sigma_inter_hess.py` computes it
with Rule-8 progress, ETA, atomic checkpoint and resume.

This also retires a caveat carried for several sessions ("the oracle overestimates,
so area comparisons at the 1e-5 level are not decisive").  The overestimate was
never noise; it was the bound doing its job.
## 🌊🌊 THE MODE-2 CORRECTION DESTROYS Σ's MARGIN — Theorem 9's strategy fails

The Mode-2 repair (evaluate the REGION, not the signed sum) removes the domination
failure, but it is not free.  Since

    A_region = A_signed + lens,     lens >= 0,     lens = (1/2) L(v) eps^2,

the second variation picks up  Q_region = Q_signed + L  with L >= 0, so the ladder
margin DROPS by L(v)/(pi/4).  Measured (K=6, matched beta, offsets handled):

    dir eps       lens         L(v)     margin loss   6.4563 - loss
    1  +0.004   8.805e-06     1.1006      1.4013         5.0550
    1  -0.004   8.325e-05    10.4068     13.2503        -6.7940
    1  +0.002   2.223e-06     1.1116      1.4154         5.0409
    1  -0.002   1.972e-05     9.8576     12.5511        -6.0948
    2  +0.004   1.077e-05     1.3458      1.7135         4.7428
    2  -0.004   3.125e-05     3.9058      4.9730         1.4833
    2  +0.002   2.350e-06     1.1748      1.4958         4.9605
    2  -0.002   7.656e-06     3.8279      4.8739         1.5824
    3  +0.004   6.085e-06     0.7606      0.9685         5.4878
    3  +0.002   1.618e-06     0.8092      1.0303         5.4260
    (dir3 eps=-0.004 and -0.002 skipped: matched Newton residual 2.5e-1)

Direction 1's negative branch costs 13.25 against a margin of 6.4563, i.e. the
corrected form has margin -6.79.  **The Mode-2-corrected reconstruction is NOT
negative definite.**  And these are sampled directions, so 6.4563 - loss is an
UPPER bound on the corrected margin: the truth can only be worse.

### What this does and does not say

It does NOT say Σ fails to be a local maximum.  It says the RECONSTRUCTION used to
certify it is too lossy: the region-area bound pays the whole lens, and the lens is
larger than the margin.  Theorem 9's proof strategy fails; the theorem itself is
undecided.

### The lens is one-sided, not a quadratic form

L(+eps) = 1.1006 vs L(-eps) = 10.4068 on direction 1, and 1.3458 vs 3.9058 on
direction 2, stable across eps (1.1006/1.1116 and 9.8576/10.4068).  So the lens is
exactly eps^2-homogeneous but NOT a quadratic form -- it is one-sided, structurally
the same object as the N12 fan bite (recorded there as "exactly eps^2-homogeneous,
one-signed, not a quadratic form").  Any repair must treat it the way N12 is
treated, not as a matrix correction.

### The route this leaves

Do not CORRECT for the lens -- eliminate it.  If the reconstruction curve is
SIMPLE, signed area equals region area and there is no penalty at all.  The
self-intersections come from arcs running past their junctions, so the
construction to build is: TRIM each arc at its actual crossing with its neighbour
(a Sutherland-Hodgman-style clip, which `sigma_area.rs` already implements for
half-planes) instead of at a matched-beta parameter.  That gives a simple curve, a
chord-free closure, and no lens -- all three failure modes closed at once.

## S7b RESOLVED — the residual is INSTRUMENTAL

The two ~5e-7 residuals left by the Mode-2 repair are within the oracle's own
convergence error.  A_true(0.004) - A_true(0) measured at n = 2401, 4801, 9601:

    -1.2214e-03,  -1.2220e-03,  -1.2223e-03

i.e. the difference is n-stable only to ~5e-7, exactly the size of the residuals.
They cannot be distinguished from zero at n = 4801, and resolving them would need
n ~ 6e5 (the difference converges like C/n).  Not a mechanism.

## S7c PARTIAL — and the matched system has a floor

Amplitude continuation (walk the amplitude 0 -> 1 in stages, restarting Newton
from the previous solution, aborting a rung the moment a stage fails) gives, at a
realistic tolerance, 10 of 12 probes converged versus the plain Newton's 9 of 12.
Direction 3's negative branch still fails at 2.5e-1.

More important, and found by this test: the BASE residual at c_R is 3.4e-05.  The
matched system cannot be solved better than that, because the arc table's own
junction endpoints already disagree by 2.5e-06 at c_R.  So "matched" means matched
to ~1e-5, not to machine precision, and any argument resting on exact matching
inherits that floor.  Recorded as a standing caveat.

## LEAN — the F6 block, all VERIFIED

Added to `lean/MovingSofa/MovingSofa/Basic.lean`, `lake build` clean, zero sorry:

    chord_sliver        F6a  the sliver between wall line and departing chord has
                             twice-area l*h -- the -(l/2)h term of the rank-one law
    bowtie_signed_zero  F6b  a self-intersecting closed quadrilateral has signed
                             shoelace 0
    square_signed       F6c  the same four vertices traversed simply give
                             twice-area 2  =>  signed area != region area
    selection_rule      F6d  a T-invariant form vanishes between opposite-sign
                             eigenvectors of an involution
    ueig_opposite       F6e  modes in different grading classes have opposite
                             U-eigenvalue
    grading_selection   F6f  hence the Z2 block-diagonalisation of the Σ form

`#print axioms` on all of these, plus `safe_closure` and `superset_principle`,
reports nothing beyond `propext` and `Quot.sound` -- no `Classical.choice`.

`lean/MAPPING.md` now carries the Rule 5 paper-to-Lean table for all 25 theorems,
WITH an explicit section on what is NOT formalized and why (the rank-one law needs
Green's theorem for piecewise-C1 curves; Mode 2 in general needs Jordan; the corner
criterion needs ring normalisation of a degree-4 identity, unavailable in core
Lean).  Those labels stay PROVED, not VERIFIED.
## S6 SOLVED: the second mechanism is a SELF-INTERSECTION LENS  🔥🔥🔥

The repair for Σ is not geometric at all -- it is in how the area is EVALUATED.

Lemma `lem:superset` is a statement about the enclosed REGION: S(c) ⊆ R(Γ), hence
|S| ≤ |R(Γ)|.  But every reconstruction in this project evaluates a SIGNED area,
a Green/shoelace sum, and

    signed area  =  |R(Γ)|   ONLY IF Γ is simple.

When Γ self-intersects, the shoelace SUBTRACTS the lens instead of adding it, so
the computed number falls below |R(Γ)| and can fall below |S| even though the
region still contains the sofa.  The lemma was never wrong here; the evaluation
was.  This is a SECOND failure mode, independent of the chord gap.

### Evidence

Lens area (resolved region area minus |shoelace|) on the MATCHED Σ curve, against
the deficits measured in sigma_matched.py:

    case            lens        deficit      agreement
    c_R          +5.45e-13         --        (curve is simple at c_R)
    dir1 -0.004  +8.312e-05    -8.270e-05     0.5%
    dir2 -0.004  +3.125e-05    -3.016e-05     3.6%
    dir2 -0.002  +7.612e-06    -7.066e-06     7.7%

The lens is exactly QUADRATIC in ε: over the three amplitudes ε = -0.004, -0.002,
-0.001 it is 3.125e-05, 7.612e-06, 1.878e-06, giving local exponents 2.04 and
2.02.  (Three amplitudes, per the standing rule that order claims need ≥3.)

### The repair, and how far it goes

Evaluate the enclosed REGION's area, resolving self-intersections (shapely
`buffer(0)` returns exactly the outer region).  Measured, offsets subtracted,
K=6, exact Rust oracle n=4801:

    signed shoelace : 7/9 probes with Δ < 0,  worst -8.290e-05
    region area     : 2/9 probes with Δ < 0,  worst -6.456e-07

A factor 375 on the worst case.  The dominant ε² deficit is GONE.

The two survivors are NOT sampling error -- they converge under refinement
(n/arc = 600, 1200, 2400 gives -6.456e-07, -5.976e-07, -5.856e-07 and
-2.794e-07, -2.728e-07, -2.710e-07).  But their scaling is ε^1.11, not ε², so
they are not the ε² mechanism; and at ~5e-7 they sit 50x below the Σ oracle
offset (3.14e-05), whose own perturbation dependence is unquantified at that
level.  Honest status: unresolved, plausibly an oracle artifact, definitely not
the mechanism that was breaking Theorem 9.

### Caveat carried forward

`sigma_matched.solve_matched` failed to converge on 3 of 12 probes (Newton
residuals 5.6e-2, 5.1e-2, 2.9e-3).  Those rows are excluded everywhere above.
The Newton needs a better initial guess or a continuation in ε before the matched
response can be used at scale.

## G8: THE CORNER-PATH STEP, reduced and certified  🔥🔥

The chord-free Γ has three kinds of piece.  Wall-line segments and envelope arcs
are rigorous (each lies on the boundary of a half-plane containing S, resp. bounds
the intersection of such half-planes).  The open piece was the CORNER PATH, which
enters with a MINUS sign, so we need

    (region bounded by the corner path)  ⊆  ⋃_t Q_t.

REDUCTION (this is the new content).  Write points as complex numbers.  With
μ_t = (cos t, sin t), ν_t = (−sin t, cos t),

    ⟨q − c(t), μ_t⟩ + i ⟨q − c(t), ν_t⟩  =  e^{−it} ( q − c(t) ),

and Q_t is exactly the open third quadrant in the (μ_t, ν_t) frame at c(t).  Hence

    q ∈ Q_t   ⟺   arg( q − c(t) ) − t  ∈ (π, 3π/2)   (mod 2π).

Membership in ⋃_t Q_t is therefore a ONE-DIMENSIONAL root-existence question for
the scalar function θ(t) = arg(q − c(t)) − t.  That is a form a proof can attack;
the raw two-dimensional covering statement was not.

CERTIFICATE.  min over the corner region of max_t min(−f_μ, −f_ν), as the t-grid
refines:

    n_t = 3001    Δt = 5.24e-04    margin -1.063e-04
    n_t = 12001   Δt = 1.31e-04    margin +1.687e-05
    n_t = 48001   Δt = 3.27e-05    margin +3.247e-05
    n_t = 192001  Δt = 8.18e-06    margin +3.852e-05

Converging to ≈ +3.9e-05, POSITIVE.  The negatives at the coarse grid were pure
t-discretisation, and discretising t can only UNDERestimate a max, so refinement
could only help -- which it did.  Every point the reconstruction subtracts is
already excluded from S by some wedge.

Label: HEURISTIC (Rule 7 -- a converged certificate, not a proof), but the other
two piece types are PROVED and the corner criterion is now explicit enough to
attempt analytically.

## Scripts

`sigma_crossing.py` (self-intersection / lens detector), `sigma_resolved.py`
(region vs signed area, domination test), `gerver_corner.py` (the corner
criterion and its margin).
## Σ's SECOND MECHANISM: chords are NOT the only problem  💧💧

`sigma_envelope.py`'s contract reads: "Every such reconstruction is superset-valid,
so its second-order coefficient Q_beta bounds the true second variation from above
for EVERY beta, and the envelope over beta is attained at the implicit-function
response: Q_true = min_beta Q_beta = Q_frz − Cᵀ H_bb⁻¹ C."

The defect is exactly in "for EVERY beta".  Diagnosis: of Σ's ten closures, the
four anchored at t = 0 and t = π/2 stay shut to 1e-17 (the perturbations vanish
there), but the SIX at the interior junctions t = β and π/2−β open up under
perturbation.  Measured at ε = 1e-3, random direction:

    dA(0)      -> rA(0)          1.628e-02
    dB(β)      -> dX(β)          8.492e-03
    dX(π/2−β)  -> dD(π/2−β)      5.587e-03
    rC(π/2−β)  -> dC(π/2−β)      9.216e-03
    rD(π/2−β)  -> rX(π/2−β)      5.587e-03
    rX(β)      -> rB(β)          8.492e-03

(the ρ-conjugate pairs agree exactly, as they must).  area_rec closes these with
CHORDS, so those members of the β-family are not superset-valid, and a minimum
taken over all β can dip below the true second variation.  **S4 is FALSE.**

So the natural repair is to restrict the envelope to the MATCHED response: the β
making the ten interior arc ends coincide pairwise, leaving no chords.  That is a
square system (5 interior junctions x 2 arcs = 10 parameters; 5 junctions x 2
coordinates = 10 equations), solved by Newton in `sigma_matched.py`.

RESULT: **the matched response ALSO fails.**  Offset −3.140e-05 subtracted,
exact Rust oracle n=4801, K=6:

    dir eps      max|gap|   Delta frozen   Delta matched   D/eps^2 matched
    1  +0.004    1.9e-10    -2.976e-05     -1.569e-06      -0.0980
    1  -0.004    1.5e-10    -9.906e-05     -8.270e-05      -5.1688
    1  +0.002    2.1e-10    -7.105e-06     -5.160e-07      -0.1290
    2  +0.004    1.1e-10    +2.304e-05     +4.237e-05      +2.6482
    2  -0.004    6.1e-11    -4.664e-05     -3.016e-05      -1.8853
    2  +0.002    1.1e-10    +6.457e-06     +1.102e-05      +2.7540
    2  -0.002    1.4e-10    -1.126e-05     -7.066e-06      -1.7665

(one further probe, dir 1 at ε=−0.002, had Newton residual 5.6e-2 -- NOT converged
-- and is excluded.)

Reading: matching helps a great deal on the ε>0 branch (−2.976e-05 → −1.569e-06,
a factor 19, essentially zero) but the ε<0 branch stays negative at −1.8 to −5.2
times ε², and Δ/ε² is STABLE as ε halves (dir 2: −1.885 at ±0.004 vs −1.767 at
±0.002), so it is a genuine ε² effect and not the oracle offset.

CONCLUSION: **Σ's superset failure has a second, one-sided mechanism beyond the
chords.**  Note the sign rules out the obvious candidate: a cap/fan bite makes the
TRUE area smaller, hence Δ = A_rec − A_true MORE positive, whereas the observed
Δ < 0 means the reconstruction UNDERestimates -- its curve cuts inside the true
sofa.  Identifying that mechanism (S6) is now the critical path for Theorem 9;
S7 (chord-free Σ) and S8 (recomputed ladder) wait on it.

## GERVER PART II IS REPAIRED AT K=16  🔥🔥

The chord-free reconstruction now has the complete local chain at K=16:

    A_rep(c_G)          = 2.21953166887          (A* to 7.2e-11)
    stationarity        = +-1.7e-10 on every mode tested
    containment         = min viol > 0 on every probe (certificate)
    Hessian spectrum    : min -1473.727246,  max -4.273730   -> NEGATIVE DEFINITE
      8 largest: -71.2316 -61.7756 -40.7427 -34.8940 -17.4304 -14.8770 -5.0212 -4.2737
      translation projected out: max -5.021155 -> NEGATIVE DEFINITE

Command: `python3 gerver_rep_hess.py 16 22 1e-5` -> gerver_rep_K16.npy.
Note for future sizing: the high-k entries are much slower than a linear ETA
suggests, because sin(2kt) integrands with k ~ 16 are oscillatory and mp.quad
needs far more nodes; the reported ETA drifted from 10.9m to 12.8m+.

What remains for Part II: G8 (turn the containment certificate into a proof --
the wall lines and envelope arcs are rigorous, only the corner-path/wedge-union
step is open) and G9 (a tail bound against A_rep rather than A_rec).

## RULE 10 / RULE 17 COMPLIANCE FIXED

`private/` did not exist, was not in either `.gitignore`, and there was no
`private/RESEARCH_LOG.md` -- a standing violation of Rules 10 and 17 through this
whole program.  Now created: `private/` gitignored in both the working tree and
the repo, and `private/RESEARCH_LOG.md` carries the GOAL, the full atom table, key
decisions, ten logged dead ends with reasons, exact job commands, and the standing
numerical caveats.

## 🌊 Σ'S SUPERSET PROPERTY FAILS AT SECOND ORDER — Theorem 9 has the same hole

This was found by asking the item-5 question ("does Σ need the chord-free
treatment too?") and it is the most consequential result of the session.

Σ's closure chords are degenerate at c_R (max 2.5e-6, the junction-solve
residual) but they OPEN UP LINEARLY under perturbation.  Measured max closure
chord length over random directions:

    c_R          2.501e-06
    eps = 1e-4   1.158e-03,  1.560e-03
    eps = 1e-3   1.090e-02,  7.848e-03
    eps = 1e-2   1.755e-01,  6.316e-02      (Gerver's, fixed: 8.069e-01)

so l(eps) ~ C eps with C ~ 8-18.  For Gerver l is O(1) and the chord defect is
-(l/2)L = O(eps), first order.  For Σ, l = O(eps) makes the defect O(eps^2) --
which is exactly the order the Σ-local theorem lives at.  This is why Σ's FIRST
variation looked clean (1e-6) while the problem was there all along.

DIRECT TEST.  Delta(eps) := [A_rec - A_true](eps) - offset, exact Rust oracle
(n=4801, offset -3.140e-05 subtracted), K=6 random directions:

    random #1   Delta/eps^2 = -1.8602, -6.1912 (eps=+-0.004);  -1.7762, -5.9424 (+-0.002)
    random #2                 +1.4402, -2.9152             ;   +1.6142, -2.8155
    random #3                 -0.3873, +0.0251             ;   -0.3711, +0.0624

8 of 12 probes have Delta < 0.  Crucially Delta/eps^2 is STABLE as eps halves
(-1.86 vs -1.78; -6.19 vs -5.94), so this is a genuine eps^2 effect and NOT the
oracle offset -- an offset contamination would scale like C/eps and blow up as
eps shrinks.

CONSEQUENCE.  The Σ ladder (m(M) ~ 6.45, the whole S1-S7 chain, Theorem 9) does
NOT establish local maximality as it stands, for exactly the same structural
reason as Gerver's Part II: the reconstruction is closed with chords, and chords
are not constraint boundaries.  The ladder NUMBERS remain valid computations; the
INFERENCE from them does not.

The fix is known and demonstrated (see below for Gerver): rebuild Σ's Γ so every
closure is a constraint boundary.  Σ's arcs meet at junctions at c_R, so at c_R
there is nothing to do; the work is in closing the gaps that open under
perturbation with wall lines rather than chords.

## ITEM D5 — CONTAINMENT CERTIFICATE FOR THE CHORD-FREE Γ PASSES  🔥

Two wrong tests before the right one, recorded so they are not repeated:

  (a) "check S_finite ⊆ R(Γ)".  WRONG DIRECTION: S_finite ⊇ S_true (dropping
      constraints enlarges), so this is STRONGER than needed and must fail at
      c_G where R(Γ) = S_true exactly.  It did, identically at c_G and under
      perturbation (-1.33e-3), with the area gap 8.4e-4 = C/n = 0.589/700.
  (b) same test with outward normals from a centroid heuristic.  WRONG on the
      CORNER arc, which is re-entrant (the wedge is subtracted), so the normal
      pointed inward and min viol came out as exactly -delta.

The correct test: S ⊆ R(Γ) iff every point OUTSIDE R(Γ) violates some hallway.
Step delta = 1e-3 outward from ∂R (orientation fixed by actual polygon
containment, not a heuristic) and compute
viol = max_t [ max(f_mu-1, f_nu-1, -max(f_mu,f_nu)) ]; viol > 0 means that point
is excluded by some constraint, as required.  Result (n_s = 20001 hallways):

    c_G              min viol +6.799e-04   CONTAINED
    x sin4t  +0.01            +6.784e-04   CONTAINED
    x sin4t  -0.01            +3.498e-04   CONTAINED
    x sin16t -0.01            +4.556e-05   CONTAINED   <- tightest
    y sin4t  +0.01            +6.215e-04   CONTAINED

Every probe passes, INCLUDING the eps=0.01 x-modes where the area comparison had
gone negative.  So those negative readings were the oracle's error, exactly as
suspected, and A_rep >= A_true.  [HEURISTIC by Rule 7 -- a certificate, not a
proof -- but the structural argument covers the wall lines and envelope arcs
rigorously; only the corner-path piece needs the wedge-union argument.]

## THE CHORD-FREE RECONSTRUCTION IN GREEN FORM — exactly stationary

`gerver_rep_green.py` integrates the corrected curve term by term instead of
shoelacing a polygon: ~100x faster and far more accurate.

    A_rep(c_G) = 2.21953166887      (A* to 7.2e-11; polygon form agrees to 4.5e-7)

    first variation:  x sin4t  +1.68e-10     (chorded law -3.22753)
                      x sin8t  -1.68e-10     (chorded law -6.45505)
                      x sin12t +1.68e-10     (chorded law -9.68258)
                      x sin16t +1.68e-10     (chorded law -12.9101)
                      y sin4t  -1.52e-10
                      y sin10t +1.68e-10

Machine-precision zero on every mode.  The rank-one defect is gone.

## ITEM 4 — paper and Lean now match what is used

Paper: `lem:superset` now carries the hypothesis that each chord "lies on a
supporting line of the family", its proof covers that case explicitly, and
`rem:chord-hypothesis` records that the hypothesis is NOT removable, pointing at
the first-order counterexample.  Compiles clean, 48pp.

Lean: added `safe_closure` --

    theorem safe_closure {α ι} {S : SetP α} (H : ι → SetP α)
        (h : ∀ t, SetP.Subset S (H t)) : SetP.Subset S (fullInter H)

-- if the body lies in EVERY assembled piece it lies in their intersection.
That is the exact content the corrected lemma needs, and its docstring records
that a chord supplies no such hypothesis.  `lake build` clean, zero sorry.

## ITEM 3 — NOT ATTEMPTED this turn, deliberately

Closed-form Toeplitz symbol coefficients were deprioritised: item 5 turned up a
correctness problem in Theorem 9, and a correctness problem outranks closing a
tail bound for a theorem whose inference step is broken.  Item 12b is now
downstream of repairing Σ's reconstruction, not upstream.

## POST-BLACKOUT SESSION: Lean audit, K=48, the chord-free rebuild, and ker L

Blackout killed the K=48 job but it had already FINISHED (4656/4656, symmetric,
uncorrupted); the Rule-8 checkpoint did its job.  Disk recovered to 24 GB free.

### The Lean formalisation is SOUND but does not cover the paper's usage [PROVED]

`superset_principle` in lean/MovingSofa/MovingSofa/Basic.lean states

    SetP.Subset (fullInter H) (famInter H P)

-- dropping constraints enlarges the intersection.  True, correctly proved, zero
sorry.  But it is a statement about INTERSECTIONS OF CONSTRAINT SETS and says
nothing about chords.  The paper's `lem:superset` claims more: constraint subarcs
TOGETHER WITH straight chords.  So:

  * no false theorem has been machine-verified -- the Lean is fine;
  * but F1 does NOT underwrite the step the paper uses it for, because the
    reconstruction Γ contains chords.

The gap is in the paper, not in the Lean.  Recorded so the VERIFIED label on F1
is not read as covering more than it does.

### ITEM 12b — the symbol route is a DEAD END at feasible K  🌊

K=48 re-fit of the 2x2 matrix symbol, same acceptance test:

    K=32:  symbol min -1.083  vs H1 margin +0.068467   gap 1.151
    K=48:  symbol min -0.531  vs H1 margin +0.066555   gap 0.597

The gap halves as K goes 32 -> 48, i.e. it closes like ~1/K.  Accepting at
|gap| < 0.05 would need K ~ 570, which is 325k Hessian entries, far beyond
reach.  The block-Toeplitz STRUCTURE is right (the selection rule shows exactly
in the fitted blocks), but fitting the symbol numerically will not close item
12b.  The only remaining route is CLOSED-FORM symbol coefficients.

Per Rule 16 this is a 🌊: the symbol was this session's main new idea for item
12b and it did not converge.  Item 12b has now survived several sessions.

What K=48 DID give, cleanly:

    K      L2 margin    H1 margin    H1 even-k    H1 odd-k
    10        8.5314     0.679412     0.871104     5.607622
    16        6.8415     0.225626     0.324905     1.335908
    24        6.5555     0.083236     0.161535     0.432817
    32        6.4806     0.068467     0.143725     0.341266
    48        6.4563     0.066555     0.143618     0.338414

L2 margin converging to ~6.44 (changes -1.69, -0.286, -0.0749, -0.0243); the H1
PARITY BLOCKS are essentially converged (even-k 0.143725 -> 0.143618, a change
of 1.1e-4).  Both are finite-K UPPER bounds on the infinite margin, so they are
evidence, not proof.

### ITEM 3 — THE CHORD-FREE REBUILD KILLS THE FIRST-ORDER DEFECT  🔥 [PROVED]

The root cause says: rebuild Γ from constraint boundaries only.  Measured facts
that make it possible (η(0) = η(π/2) = 0, so c(0), c(π/2) and every constraint
line of H_0, H_{π/2} are FIXED):

    A(φ)        lies on x = c_x(0) + 1       to 1.4e-11 under perturbation
    C(π/2−φ)    lies on x = c_x(π/2) − 1     to 1.4e-11
    B(π/2)      lies on y = c_y(0)
    D(0)        lies on y = c_y(π/2)
    A(π/2), C(0) lie on y = c_y(0)+1 and do not move

So the closed curve

    X[bx1→bx2] · D[bD→0] · {y=c_y(π/2)} · {x=c_x(π/2)−1} · C[π/2−φ→0]
      · {y=c_y(0)+1} · A[π/2→φ] · {x=c_x(0)+1} · {y=c_y(0)} · B[π/2→bB]

uses ONLY envelope arcs, the corner path, and wall lines -- no chords.  At c_G
both closure corners degenerate and Γ = ∂S exactly.

RESULT (shoelace on the assembled polygon, 3000-4000 pts/arc):

    A_rep(c_G) = 2.2195321200   (sampling error +4.5e-07)

    first variation:   x sin4t  +0.000005   (chorded law: −3.227526)
                       x sin8t  +0.000003   (chorded law: −6.455053)
                       x sin12t +0.000013   (chorded law: −9.682579)
                       y sin4t  −0.000001

The rank-one defect is GONE -- zero to the sampling noise floor on every mode.
This is the repair the root cause dictated, and it works.

DOMINATION: not numerically settled, and the reason is instrumental.  The Rust
oracle OVERestimates the true area with offset exactly C/n (measured +1.227e-4,
+4.906e-5, +2.453e-5 at n = 4801, 12001, 24001 -- clean 1/n), and that offset is
PERTURBATION-DEPENDENT since a higher-curvature trajectory is under-resolved by
the same grid.  At n=24001, A_rep − A_true is −2.4e-5 at ε=0.002 (inside the
+2.45e-5 offset, i.e. ≈ 0) but −1.0e-4 to −2.0e-3 at ε=0.01, where the active
structure plausibly changes and the fixed arc table stops applying.  So the
measurement neither confirms nor refutes domination.  Domination for A_rep should
come from PROOF -- every piece is a constraint boundary, so the Lean
`superset_principle` argument applies -- not from this comparison.

### ITEM 4 — the ker L fallback is DEAD  💧 [PROVED]

I previously offered "restrict Part II to ker L" as the safe fallback.  It does
not work.  On ker L the first-order AREA discrepancy cancels, but the chord
still leaves the supporting line, so CONTAINMENT still fails and `lem:superset`
still does not apply.  Measured on odd x-modes (which lie in ker L, since
η_x′(0)+η_x′(π/2) = 2k + 2k(−1)^k = 0), oracle offset subtracted:

    x sin2t   Δ/ε² = −0.0971, −0.0971, −0.0878, −0.0878   (ε = ±0.02, ±0.01)
    x sin6t   Δ/ε² = −0.9661, −0.9661, −0.9108, −0.9108

Δ < 0 on every probe, and identical for ±ε -- a genuine second-order deficit
with no first-order part, confirming these directions really are in ker L.  So
A_rec < A_true on ker L at second order.

CONSEQUENCE: neither of the two fallbacks works.  The additive correction fails
(item B4, refuted last session) and ker L fails (here).  Only the chord-free
rebuild restores containment, which makes item 3 the ONLY route for Part II.

### Scripts

`gerver_repaired.py` (the chord-free reconstruction; `curve()` is reusable).

## THE ROOT CAUSE: a gap in Lemma `lem:superset` (the paper's load-bearing lemma)

Lemma `lem:superset` ("One-sided reconstruction") is stated for closed curves
assembled from constraint subarcs **together with straight chords**, but its
proof establishes only the constraint-subarc case: "each point excluded from
R(Γ) by a constraint subarc is excluded from S(c) by that same constraint."

**A chord is not a constraint boundary.**  Nothing stops a chord from cutting
INTO S(c); when it does, S ⊄ R(Γ) and the conclusion g_true ≤ g_Γ fails.  The
missing hypothesis: each chord must lie on a SUPPORTING LINE of the family.

That hypothesis fails for Gerver at FIRST order.  At c_G the two bottom chords
lie exactly on the wall line y = 0, so the lemma applies.  Under a perturbation
with η(0) = η(π/2) = 0 the chord endpoints A(0) and C(π/2) lift off that line at
rates η_x′(0) and η_x′(π/2), the chords leave the supporting lines, and the
enclosed region loses the sliver beneath them — which is exactly the measured
−(ℓ/2)L, and exactly the observed SIGN (|S| > |R|).

This is the root cause of everything recorded above, and it supersedes the
framing of the defect as a mysterious reconstruction bug.  It also explains why
the additive repair fails item B4: adding a term to the FUNCTIONAL cannot restore
CONTAINMENT of the region.

### ITEM B4 — REFUTED [PROVED]

A_corr := A_rec + (ℓ/2)(c_x′(0) + c_x′(π/2)) restores stationarity in every
direction but does NOT dominate the true area.  Measured
Δ(ε) := [A_corr − A_true](ε) − [A_corr − A_true](0), oracle offset subtracted:

    x sin4t   ε=+0.02 → −1.8e-6    ε=−0.02 → −3.6e-4   (Δ/ε² = −0.005 / −0.900)
    x sin8t   ε=+0.01 → −1.2e-6    ε=−0.01 → −1.3e-4   (Δ/ε² = −0.012 / −1.278)
    y sin4t   both signs → +5e-8 (no defect in y, as expected)

Δ < 0 on the ε<0 branch of every x-mode, strongly asymmetric between branches
(a kink).  So B4 FAILS.  Part II must use the ker L restriction, or rebuild
Γ_ε with chords pinned to the moving supporting lines.  The additive route is
closed.

### ITEM 5 — the certified ladder does NOT need recomputation [PROVED]

The defect is LINEAR in ε and the ladder entries are symmetric second
differences, which annihilate linear terms exactly.  Verified directly: the
second difference of A_rec and of A_corr agree to 0.0 in the last digit
(x sin4t −14.25946675, x sin8t −55.14424039, x sin12t −128.7951754,
y sin4t −20.92292313).  So the certified K=16 block and the whole ladder stand
as COMPUTATIONS; what the defect invalidates is the INFERENCE from them via
`lem:superset`.

### ITEM 3 — the selection rule is PROVED, and it is a Z₂ grading

Not "odd Δ vanishes" — that was only the same-component part, and it was
incomplete.  Measured exhaustively at K=32:

    same component (xx, yy):  M[(c,k),(c,k′)] = 0  unless k+k′ EVEN   (ratio 1e-10)
    cross component  (xy)  :  M[(0,k),(1,k′)] = 0  unless k+k′ ODD    (ratio 1e9)

Both are one statement: M is block-diagonal for the Z₂ grading
g(c,k) := (k+c) mod 2, i.e. M[u,v] = 0 unless g(u) = g(v).

PROOF.  Let U(η)(t) := (η_x(π/2−t), −η_y(π/2−t)) — reverse t and flip y, which
is Σ's ambidextrous symmetry (the ρ-conjugation of SIGMA_LOCAL.md §1 composed
with time reversal).  Since sin(2k(π/2−t)) = (−1)^{k+1} sin(2kt),

    U(x,k) = (−1)^{k+1}(x,k),      U(y,k) = (−1)^{k}(y,k),

so U = +1 exactly on {x odd k} ∪ {y even k} (the g=1 block) and U = −1 on the
g=0 block.  A U-invariant form cannot couple the two eigenspaces. ∎

Confirmation that the grading is the true block structure: the two graded blocks'
L² margins are 6.4806 and 3.8725, which are exactly the two smallest eigenvalues
of the full M.

### ITEM 12b — the correct model is BLOCK-Toeplitz with a 2×2 matrix symbol

Three fits, with the acceptance test "symbol min must equal the measured H¹
margin" applied to each:

  1. scalar Toeplitz, xx block        min f = −0.613  vs H¹ = +0.068   REJECTED
  2. scalar Toeplitz, graded g-blocks min f = +3.139  vs H¹ = +0.068   REJECTED
  3. 2×2 matrix symbol                min f = −1.083  vs H¹ = +0.068   REJECTED

Fit 1 failed because the xx block is not an invariant block.  Fit 2 failed
because the graded block alternates component with k: its a₀ came out
12.95 ± 2.78, and 12.95 = (10.3+15.8)/2 while 2.78 = (15.8−10.3)/2 — the
"spread" was a period-2 structure, not noise.  Fit 3 uses the right model and
the selection rule shows PERFECTLY in the fitted blocks (D=0 diagonal only,
D=1 off-diagonal only, D=2 diagonal only, D=3 off-diagonal only), but the
coefficients have not converged: the xx entries carry 5–13% spread against
yy's 0.1%.

So the structure is settled and the obstruction is quantified: the x-component
has not reached its Toeplitz limit by k=32.  Item 12b stays OPEN pending the
K=48 ladder (running, checkpointed to sigma_rel_K48.npy).

No f_min from a rejected fit is quoted as a tail bound anywhere.

### Scripts

`sigma_graded_symbol.py`, `sigma_matrix_symbol.py`, `gerver_superset.py`.

## ITEM 12b — the Σ tail is TOEPLITZ.  Half of it is now closed.  [PROVED / OPEN]

### Why every previous weld failed

The 2×2 weld and the dyadic graded weld both tried to bound M below by pairing
band minima against coupling maxima.  Re-run at K=32 the graded weld returns
m ≥ −3252.3, useless: the couplings grow ~3.3× per band (287, 1055, 3374) while
λ_min per band is erratic (9.8, 247, 56, 1055).  No choice of weights repairs
that, because the band decomposition is the wrong decomposition.

### The structure they missed

Normalise out the diagonal's k² growth, N[k,k′] := M[k,k′]/(k k′).  Then N is
**Toeplitz** — a function of Δ = |k−k′| alone — and vanishes identically for odd
Δ (a parity selection rule: M[16,15] = M[16,17] = M[16,1] = 0 exactly).
Measured across k = 8,12,16,20,24:

    Δ=0   10.55  9.93 10.33 10.50 10.20
    Δ=2   -3.97 -4.70 -4.78 -4.44 -4.39
    Δ=4   -1.60 -1.69 -2.09 -1.92 -1.48

A Toeplitz form's spectrum is the range of its symbol
f(θ) = a₀ + 2 Σ_{Δ>0} a_Δ cos(Δθ), so the INFINITE tail is controlled by one
number, min_θ f — no band decomposition and no coupling maxima at all.

### Why this makes the tail easy rather than hard

For the tail block (k > K),

    M(η_tail) ≥ f_min Σ_k k²|η_k|² ≥ f_min K² ‖η_tail‖²_{L²},

so the tail's L² margin grows like K² while the target is the FIXED number
m ≈ 6.45.  The tail requirement is only f_min ≥ m/K², which at K=32 is 0.00633.
The tail was never the tight part; it only looked tight because it was being
bounded in the wrong decomposition.

### Result: the y-component tail is CLOSED

    a₀ = +15.8376 ± 0.0183   (spread 0.12%)
    every other |a_Δ| ≤ 0.113 ± 0.017
    symbol range [15.0419, 16.0856]
    f_min = 15.042  vs requirement 0.00633   — SATISFIED by a factor 2376.

The y-block Toeplitz limit is clean and strongly positive.  That half of the
tail is done.

### Result: the x-component fit is INVALID at K=32 — reported as a failure

    a₀ = +10.2972 ± 0.2306   (2.2%)
    a₂ =  -4.4988 ± 0.2249   (5.0%)
    a₄ =  -1.7834 ± 0.2416   (13.5%)
    symbol range [-0.6128, 16.4243],  f_min = -0.613

f_min = −0.613 CONTRADICTS the directly measured H¹ margin +0.068467 (the two
must agree if the model is right).  The disagreement is in SIGN, so the
conclusion is that the x-component Toeplitz fit is not yet valid at K=32 — NOT
that the form is indefinite.  The 13% coefficient spreads say the same thing.
The x-block has not reached its Toeplitz limit by k=32.

### Honest status of item 12b

Reduced from "the whole tail is open" to "the x-component tail is open".  Still
OPEN.  The route is now specific: push the ladder to K=48 or 64 and re-fit the
x symbol, checking convergence of a_Δ and agreement of min_θ f with the measured
H¹ margin as the acceptance test.  Do NOT accept a symbol fit whose min
disagrees with the measured margin.

### Norm note, recorded to prevent a repeat

The H¹ margin DEcreases along the ladder (0.679, 0.226, 0.083, 0.068) while the
L² margin CONverges (8.53, 6.84, 6.56, 6.48, changes shrinking ~4× per step).
L² is the right norm for the theorem: M is unbounded ABOVE (diagonal ~ k²),
which never obstructed a lower bound.  The H¹ margin is exactly the Toeplitz
symbol minimum and is the right diagnostic for the TAIL, not for the theorem.

### Scripts

`sigma_h1.py` (L² vs H¹ margins along the ladder, parity blocks),
`sigma_symbol.py` (symbol fit, min, and the tail requirement).

## THE RANK-ONE LAW IS NOW PROVED, AND UNIFIED WITH Σ  [PROVED]

### Theorem (rank-one defect)

Let η perturb c_G with η(0) = η(π/2) = 0.  Then

    d/dε A_rec(c_G + ε η)  =  −(ℓ/2) ( η_x′(0) + η_x′(π/2) ),

ℓ = 0.806881614715 the common length of the two bottom wall segments of ∂S.

PROOF.  Γ_rec is a closed curve, so the first variation of the enclosed area is
the closed integral of (u dy − v dx), (u,v) = d/dε of the boundary point, with
NO boundary terms (they telescope).

(i)  Arc A is CONSTANT on [0,φ], identically the corner (1,0); arc C is
     constant on [π/2−φ,π/2], identically (x_C,0).  Verified to 3e-31.  A
     constant piece has dx = dy = 0, so it contributes nothing.
(ii) The top chord lies on y = 1 with both endpoints fixed (measured drift 0),
     so it contributes nothing.
(iii) Each bottom chord lies on y = 0, so dy = 0 and its contribution is
     −∫ v dx.  One endpoint moves vertically at rate η_x′(0) resp. η_x′(π/2);
     the other does not.  v interpolates linearly along a chord, so
     −∫_0^ℓ h(1−u/ℓ) du = −(ℓ/2) h.  Summing the two chords gives the claim.
(iv) The true boundary keeps both bottom segments on y = 0 — they are the wall
     lines y = c_y(0) and y = c_y(π/2), fixed because η(0) = η(π/2) = 0 — so
     dA_true = 0 and the whole discrepancy is (iii).  QED

VERIFICATION: the two bottom segments have EXACTLY equal length (difference 0.0
at dps=30), ℓ = 0.806881614715, so the predicted a = −ℓ/2 = −0.403440807358
against the independently fitted −0.40344081.  The law matches measured dA_rec
on random mixed directions to 2.04e-9.

This upgrades the law from HEURISTIC to PROVED.  The constant is no longer
fitted: it is half the bottom-segment length.

### The repair, and its limit

The fix CANNOT be localised to the chord term.  Projecting A(0) and C(π/2) onto
the wall lines was tried and makes the defect WORSE (measured), because the
Green boundary terms telescope globally but not piecewise: the raw chord term's
own variation is +x_B η_x′(0)/2, not the −(ℓ/2) η_x′(0) that the closed-curve
integral assigns to that stretch.

What the proof licenses is the ADDITIVE correction.  Since c_G has
c_x′(0) = c_x′(π/2) = 0, the functional L is read off the trajectory itself:

    A_corr(c) := A_rec(c) + (ℓ/2) ( c_x′(0) + c_x′(π/2) ).

Well-defined, equals A_rec at c_G, and STATIONARY there in every direction
(verified to 1.7e-8 on random directions).

CAVEAT [OPEN]: A_corr's SUPERSET property is NOT established.  A_rec ≥ A_true
was the entire point of the reconstruction and the added term has no sign.  So
A_corr repairs stationarity only.  Part II still needs either (a) a proof that
A_corr ≥ A_true near c_G, or (b) the restriction to ker L plus separate
treatment of the one missing direction.

### THE CHORD-LENGTH LAW — why Σ escapes  [PROVED]

Σ HAS the same degeneracy.  Measured: arcs dA and rA are both CONSTANT on
[0, β], β = 0.289654, both pinned at (1, 1/2) — which is the ρ-FIXED point,
since ρ(x,y) = (x, 1−y).  The earlier note claiming Σ had no such degeneracy was
wrong and has been corrected in place.

What saves Σ is not the absence of the degeneracy but the CHORD LENGTH.  The
defect is −(ℓ/2) L with ℓ the closure-chord length adjacent to the constant arc.
Measured closure-chord lengths:

    Σ:      max over all ten closures   2.5e-6   (junction-solve residual)
    Gerver: both bottom chords          8.069e-1

Σ's arcs meet at genuine junctions, so every closure chord is degenerate and
ℓ = 0; Gerver's three closures are real segments of the sofa boundary.  Hence
Σ's reconstruction is stationary — confirmed directly, worst |dA_rec/dε| =
2.6e-6 over five random directions in 12 dimensions, at the n=1400 quadrature
resolution.

This is the unified statement: ONE law explains both sofas.

### Scripts

`gerver_proof.py` (the proof's four facts + the repair), `sigma_degeneracy.py`
(Σ's constant-arc audit and chord lengths).  Caution recorded in the latter: arc
ranges may DESCEND (t0 > t1), so speeds must be taken with |dt| or argmin picks
the most negative rather than the smallest magnitude.

## PART II DEFECT — FULLY DIAGNOSED.  It is exactly RANK ONE.  [HEURISTIC]

Seven hypotheses were tested against measurement.  Six were killed (basin jump,
swallowtail, wrong arc list, wrong arc ranges, wrong chord endpoints, and the
chord-vs-wall-segment story as tested on the y-component).  The seventh is
CONFIRMED, quantitatively and on directions it was never fitted to.

### The law

For every perturbation eta vanishing at t = 0 and t = pi/2,

    dA_rec/deps |_{c_G}  =  a * L(eta),    L(eta) := eta_x'(0) + eta_x'(pi/2),
    a = -(x_B - x_D)/4 = -0.40344081,

while dA_true/deps = 0 identically (exact Rust oracle, GERVER mode, n=4801).
Here x_D = -1.4206448 and x_B = +0.1931160 are the endpoints of the TOP wall
segment, of length x_B - x_D = 1.6137632 = 4|a|.  Note x_D = -c_y'(0) exactly.

Evidence: a was fitted from the pure sin-mode family alone, then tested on six
RANDOM mixed directions in a 12-dimensional space (K=6, both components).
Worst relative error 1.4e-8 at dps=30.  Structured checks: the law predicts
dA_rec = 0 for every ODD k (since eta_x'(pi/2) = 2k(-1)^k cancels eta_x'(0)),
confirmed for k = 1,3,5,7; and -1.6137632*k for every even k, confirmed for
k = 2,4,6,8 to 8 digits.

### The mechanism

Arc A is IDENTICALLY the wall line y = 0 on [0, phi], and arc C on
[pi/2 - phi, pi/2], phi = 0.039177.  Measured: A(s)_y = 0 to 1e-32 for
s <= 0.01, and 0.0839 at s = 0.1.  So on those intervals the hallway touches
the sofa along a SEGMENT, not a point, and the contact-point formula is a
spurious selection there.

Under an x-perturbation the two selected endpoints lift off the wall at
exactly the rate of the perturbation's endpoint derivative:

    d/deps A(0)_y = eta_x'(0),     d/deps C(pi/2)_y = eta_x'(pi/2)

(measured 4.00000 for k=2, both).  The two bottom closing chords then stop
lying along y = 0 and pick up a first-order sliver:

    d/deps seg(C(pi/2),D(0)) = -(1/2) x_D eta_x'(pi/2) = +2.8412897,
    d/deps seg(B(pi/2),A(0)) = +(1/2) x_B eta_x'(0)    = +0.3862368

for k = 2, summing to +3.2275264 -- and the arc terms contribute exactly twice
that with the opposite sign, for a net -3.2275264.  Both chord values are
reproduced in closed form from x_D, x_B to all printed digits.

The y-component shows NO defect on any mode, because a y-perturbation does not
lift the endpoints off the wall (measured drift 0.00000 on all six endpoints).

### What this does and does not mean

DOES: Part II's reduction theorem is FALSE as stated on the full tangent space.
Since a != 0 and L is linear, one SIGN of any eta with L(eta) != 0 sends
A_rec below A_true at first order, breaking the superset property.

DOES NOT: it does not hole the reduction on ker L.  The defect is a SINGLE
linear functional -- rank one.  On the codimension-1 subspace {L(eta) = 0},
which contains every y-mode and every odd x-mode, A_rec is stationary at c_G
(measured 1.5e-8) and the reduction stands.  So the corrected statement is:

    Part II's reduction is valid on ker L, a closed subspace of codimension 1.

Closing Part II therefore needs ONE extra direction handled, not a rebuild.
That is a far smaller gap than "Part II is holed", which is how this was
recorded before the measurement.

### Attempted repair that did NOT work, recorded so it is not retried

Treating the two wall contacts as moving junctions (Newton-solve a0 near 0 with
A(a0)_y = 0, and c1 near pi/2 with C(c1)_y = 0, then integrate A over [a0,pi/2]
and C over [0,c1]) does NOT fix it: at c_G the arcs do not CROSS the wall
transversally, they COINCIDE with it, so the Newton step is degenerate and
a0, c1 never move.  Verified: dA_fix = dA_rec to all digits on every mode.
See `gerver_fixed.py`, kept as a negative result.

### Gauge note

The true area is invariant under reparametrisation c(t) -> c(t + eps s(t)),
s(0) = s(pi/2) = 0 -- the sofa depends only on the SET of hallways.  Gauge
directions eta = s c' have L(eta) = s'(0) c_x'(0) + s'(pi/2) c_x'(pi/2) = 0,
because c'(0) = (0, 1.4206448) and c'(pi/2) = (0, -1.4206448) have NO
x-component.  Consistently, measured dA_rec on gauge directions is ~3e-3
against a defect scale of 3.2.  So the defect is not gauge-breaking; the gauge
directions sit inside ker L.  (Caution recorded: the first version of this test
dropped the eps*s'' term in the chain rule for c'' and gave spurious values
~1.6; the term is first order and must not be dropped.)

### Scripts

`gerver_decomp.py` (term-by-term first variation), `gerver_active.py` (measured
active t-ranges -- all five assumed ranges are 100% correct), `gerver_fixed.py`
(the failed six-junction repair), `gerver_gauge.py`, `gerver_rankone.py`.

## SUPERSEDED: the remaining candidate as stated before measurement

## THE REMAINING CANDIDATE, now sharply identified

The reconstruction closes the three gaps with **CHORDS between arc endpoints**:
seg(u,v) = ½(u ∧ v). The true boundary instead follows the **WALL LINE** there.
At c_G the two coincide (the arc endpoints sit on the wall), so the areas agree
— which is why A_rec(c_G) = A* exactly. Under perturbation the wall line moves,
and if the arc endpoints drift off it, the chord no longer reproduces the true
segment, giving a FIRST-ORDER area difference.

This is consistent with every observation: no single arc term is the culprit
(the defect lives in the closure, not the arcs); the segment terms are large in
the decomposition (S2 = +2.841 on sin4t); and the discrepancy would cancel when
the endpoint drifts cancel by symmetry — which is exactly the symmetric/
antisymmetric split observed.

**Test to run:** track the three arc-endpoint pairs under an antisymmetric
perturbation and check whether they remain collinear with the moving wall line.
If they do not, the chord closure is the defect and the repair is to close with
the wall segment rather than the chord.

**Σ is unaffected** -- but NOT for the reason first written here.  The original
claim (that Σ's traversal was derived with its junction structure) was not the
mechanism; it is superseded.  See the CHORD-LENGTH LAW: Σ has the SAME
constant-arc degeneracy and is saved by its closure chords having zero length.

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
