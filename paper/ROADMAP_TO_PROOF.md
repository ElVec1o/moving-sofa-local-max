# Roadmap to a proof of local maximality of Gerver's sofa (second-variation route)

Status (v0.7.x): the proof is reduced to one statement,
**Conjecture (Boundary-layer subdominance)** in the manuscript. Its leading
term is proved (Gaarding, `lambda_min(D_tot)=1` from the persistent contacts A,C);
every clause is verified to 30 digits by the exact analytic oracle at all four
breakpoints. What is missing is the *matched-asymptotic* passage to the `w->0`
limit — and, concretely, the explanation of one cancellation.

## The single obstruction, stated sharply

Along the normalized bump `eta_hat_w` at a breakpoint `b`:

- the oracle finds `Q(eta_hat_w) = O(w^2)` (and `= -(1/5)w^2 * <e,D_tot e> + o(w^2)`);
- but the moving-breakpoint calculus *a priori* predicts an `O(w)` term:
  `Q ~ Delta(d_theta J) * (delta b)^2`, with `delta b ~ w^{1/2}` and
  `Delta(d_theta J) != 0` because the sofa boundary has a genuine corner at `b`
  (verified: tangent cross-product `-0.705`, not `0`).

So an `O(w)` contribution **cancels**, leaving `O(w^2)`. That cancellation *is*
the proof. Identifying the structural identity that forces it is the crux.

## Inventions that would close it (most promising first)

### I1. An envelope/Danskin second-variation calculus for intersection-area functionals
`F(c) = area( intersect_theta (R_theta H + c(theta)) )` is a *lower-envelope*
(intersection) functional. Its boundary is the inner envelope of the moving
hallway walls, and the breakpoints are where the active envelope switches.
- First order: by the envelope theorem (Danskin), the switch locations are
  *optimal* and contribute nothing — this is exactly the observed `Delta J = 0`
  (`d_b G = 0`).
- **Invention:** the *second-order* Danskin/envelope formula for area-of-
  intersection, showing the switch-point terms are absorbed into the smooth
  (Gaarding) part, i.e. the `O(w)` term is structurally zero. This is the most
  likely explanation of the cancellation, and it connects directly to why Baek's
  global functional is concave (intersection/`min` structure). *Test:* derive the
  2nd-order envelope formula for a model 2-wall corner and check it kills the
  `Delta(d_theta J)` term.

### I2. The blow-up (Gamma-limit) variational problem at the corner
Rigorously define `G_{j,e}(eps) = lim_{w->0} w^{-2}(F[c_G+eps eta_hat_w]-F[c_G])`
as a Gamma-limit / matched-asymptotic inner limit.
- **Invention:** the *limiting inner functional* — a variational problem on the
  rescaled profile at the breakpoint corner (straight-line envelopes + the fixed
  bump profile), whose value is the negative quadratic. Requires compactness of
  the rescaled family, identification of the limit, and its sign.
- This is standard Gamma-convergence machinery applied to a genuinely new setting
  (a moving corner with a concentrating perturbation). The reward: `G < 0` becomes
  a finite, explicit computation.

### I3. A breakpoint-adapted space + refined two-norm sufficiency
The classical obstruction is the two-norm discrepancy: `Q` is coercive only in
`H^1`, but `F` is defined only on `H^2 -> C^1`, and the cubic carries `eta''`.
- **Invention:** the intermediate space `X = H^1` augmented by the breakpoint
  1-jets `{eta(b_j), eta'(b_j)}`, with a norm in which (a) `F` is `C^2`, (b) `Q`
  is coercive, (c) the remainder is `o(||.||_X^2)`. The measured slope-slot `~ 0`
  (Lemma 8 pairs `eta` with `eta''`, never `eta'` with `eta''`) is the sign that
  the jet terms are benign; formalize the space where Ioffe (1979) /
  Dambrine-Lamboley (2019) two-norm sufficiency then applies verbatim.
- Risk: needs the slope-slot to be provably `0` (or sign-definite), currently only
  measured `<= 5e-4`.

### I4. A local bridge from Baek's concave majorant
Baek (2024) proves a quadratic functional `Q_Baek` on cap-boundary-direction
triples is concave and upper-bounds area, with `c_G` a local optimum.
- **Invention:** the explicit change of variables (corner trajectory `c` <->
  cap-boundary-direction triple) near `c_G`, and a lemma that the `H^2` second
  variation of `F` is dominated by the (concave, sign-definite) second variation
  of `Q_Baek`. Local maximality then transfers *for free* from Baek's concavity,
  bypassing the matched asymptotics entirely.
- Highest payoff, highest cost: requires digesting Baek's 119-page construction.

### I5. Validated matched asymptotics (interval Gamma-limit)
Combine the blow-up with certified numerics.
- **Invention:** an `arb`-interval version of the analytic oracle **plus** a
  certified bound on the convergence rate `|g_w(eps) - G(eps)| <= C(eps) w^{1/2}`,
  so that `g_w(eps) < 0` for all `w < w_0` follows from `G(eps) <= -c_0 eps^2`
  (computer-verified) and the certified remainder. This is "validated matched
  asymptotics": it does not need a closed form for `G`, only rigorous enclosures
  and a rigorous modulus of convergence.
- Most mechanizable; closes caveat (i) as a by-product.

## What is already in hand (do not redo)

- Exact analytic oracle (`analytic_oracle.py`): `A*` to `4e-16`. Interval-ready.
- Gaarding `Q_smooth ⪯ -||.'||^2_{L2}`, `delta=1`, from A,C persistence + `mu ⊥ nu`
  (`prop:multicontact`, PROVED).
- Blow-up limit `G(eps) < 0` at all 4 breakpoints, both components, 30 digits;
  pure quadratic at `b_1`, `<= 4-8%` cubic at `b_2`.
- Reduction of general `eta` to worst-case localized bumps (bulk `Q` dominates).
- `Sigma`: symbol degenerates at the end caps (`lambda_min ~ 4.95 theta^1.69`), a
  prior obstruction before any of the above applies.

## Recommended order of attack

1. **I1 (envelope calculus)** — most likely to *explain the cancellation* and
   hence prove clause (ii)/`O(w^2)` directly. Start with a 2-wall model corner.
2. **I5 (validated asymptotics)** in parallel — mechanizable, and certifies the
   finite data regardless of how I1 goes.
3. **I4 (Baek bridge)** if I1/I5 stall — it sidesteps the asymptotics but costs the
   most to set up.
