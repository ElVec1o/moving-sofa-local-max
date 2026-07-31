## 🔴🔥 THE DISC COUNTEREXAMPLE WAS WRONG AS COMMITTED, AND THE CORRECTED ONE IS BETTER

### 🔴 What I got wrong, and how

Last block I committed: "for c in (0,1), H_c = 1-c+c(sin+cos) satisfies gauge + mirror +
convexity + (RC) yet the ordering fails", instantiated at c = 0.3.  I checked H_c + H_c''
= 1-c on (0,pi) and stopped there.  That is not the convexity of the body.

C2 is rho-symmetric, so h(theta) = h(-theta) + sin(theta) DEFINES h on [pi,2pi] from H on
[0,pi].  On (pi,2pi) one gets h + h'' = (H+H'')(2pi-theta), no new condition.  But the
extension has DERIVATIVE JUMPS at the two junctions,

    atom at 0   = 2 H'(0) - 1 ,      atom at pi = -2 H'(pi) - 1 ,

which are atoms of the surface area measure there.  For the disc both equal 2c - 1.  At
c = 0.3 they are -0.4: the extended body is NOT CONVEX.  My "counterexample" was not a
convex body at all.

### 🔥 LEMMA (forced boundary derivatives).  Under (RC),  H'(0) = 1/2 and H'(pi) = -1/2.

Convexity needs both atoms >= 0; (RC) permits atoms only at +-pi/2, so both vanish.  Two
boundary conditions that were never written down.  Sigma satisfies them: computed
H'(0) = 0.4999999990, H'(pi) = -0.4999999987 (finite-difference error).  This is what
makes the admissible class rigid at the endpoints.

### 🎆 THE CORRECTED COUNTEREXAMPLE IS SHARPER: exactly one disc, and it IS a sofa

The lemma selects c = 1/2 uniquely from the family (c < 1/2 non-convex, c > 1/2 forbidden
atoms).  At c = 1/2 the body is the disc of radius 1/2 centred at (1/2,1/2), the incircle
of the unit square, and everything holds with margin: gauge exact, mirror A = 1 to 3e-16,
H + H'' = 1/2 constant.  Its arms are alpha_1 = alpha_2 = -1/2 identically, so
{alpha_1<0} = [0,pi/2) and {alpha_2>0} = empty: the ordering fails.

AND IT IS REALIZABLE.  |N| = 0 exactly (polygon oracle), |C2| = pi/4 = 0.785398163 by
both the cap formula and the oracle, so the maximal ambidextrous sofa with this cap datum
IS the disc; a disc of diameter 1 moves freely through a unit corridor and turns either
corner.  So CRUX-D is answered NEGATIVELY: sofa-realizability does not force the ordered
sign structure either.  The hypothesis in the mirror stability theorem is PERMANENT.

The corrected version is strictly stronger than what I claimed: it is one canonical body
instead of a family, and it settles realizability, which the c = 0.3 version could not
have done.

### 🔴 AND IT EXPOSED AN UNSTATED HYPOTHESIS IN THE NICHE FORMULA

Running the disc through the Reynolds regression gave V = -0.142699 against |N| = 0, i.e.
V < |N|, contradicting the proposition.  Diagnosis: the face-1 segment is
s in [alpha_1^+, sigma], so its contribution is (1/2)((sigma - alpha_1^+)^+)^2, and
writing it as (1/2)(sigma - alpha_1)^2 -- as the note does -- silently assumes

    (SEG)   sigma >= alpha_1^+   on [0,pi/2].

The disc has alpha_1^+ = 0 and sigma decreasing to -1/2, so (SEG) fails and the written
expression over-counts.  With the segment truncated, V = 0 = |N| and the tension
disappears.  Sigma SATISFIES (SEG), and it is already a theorem: sigma - alpha_1 =
cos t x'(t) (Prop "sigx") with x strictly increasing (Prop "mono", PROVED), plus
sigma >= 0; computed min of sigma - alpha_1^+ is +2.5e-7 as t -> pi/2.  Every use of the
formula in the note is on data satisfying (SEG), which is now stated at the formula.

### Ledger

Forced boundary derivatives PROVED.  Disc counterexample CORRECTED and strengthened
(PROVED, and realizable).  CRUX-D CLOSED, negative.  (SEG) hypothesis now explicit.
Process note: the error was caught by asking whether a claimed body actually exists, which
is I6's non-vacuity requirement -- the examples battery, applied to my own counterexample,
is what found it.  It should have been run before the commit, not after.

## 🔥 THE SIGN HYPOTHESIS IS ESSENTIAL (A DISC SAYS SO); AN EXPLICIT C^2-BALL; ONE METHOD

### 🔥 Item 1 RESOLVED BY COUNTEREXAMPLE: single-crossing cannot be dropped

Attempting to derive the ordered-anchored sign hypothesis from the rest of the domain
produced first a new lemma, then a counterexample killing the attempt.

  LEMMA (arm sandwich).  Under 0 <= (H+H'')_ac <= 1:
      alpha_2 <= alpha_1' <= alpha_2 + 1        and        -alpha_1 - 1 <= alpha_2' <= -alpha_1.
  The pair (alpha_1, alpha_2) ROTATES: arm 1 strictly increases where arm 2 is positive,
  arm 2 strictly decreases where arm 1 is.  This is the differential form of the
  oscillator mechanism behind (RC) => injectivity.  PROVED, two lines; Lean F30a-b.

  COUNTEREXAMPLE (the disc).  H_c = 1 - c + c(sin + cos), the support data of the disc
  of radius 1-c centred at (c,c): gauge holds, mirror holds (A = 2c), and
  H_c + H_c'' = 1 - c identically, so convexity AND (RC) hold with margin.  Yet
  alpha_1 = alpha_2 = -c identically: {alpha_1 < 0} = [0, pi/2), {alpha_2 > 0} = empty.
  The ordering fails.  So the sign hypothesis of the mirror stability theorem CANNOT be
  derived from gauge + mirror + convexity + (RC); it is essential at the level of the
  function domain.  Whether sofa-realizability rescues it is OPEN and now precisely posed.

  En route, constants satisfying the sandwich inequalities were checked BEFORE
  integrating them to a body (I3 step 3): the disc is the integral of the constant
  solution (u,v) = (-c,-c).

### 🔴 A GRID BUG THAT NEARLY POISONED THE BALL CONSTANTS

The first margin run reported alpha_1 dipping to -0.4168 on [beta+0.15, pi/2], which
would have meant Sigma's sign pattern was wrong and five sessions of cell analysis with
it.  It was np.arange(lo, hi+h, h) OVERRUNNING the interval: the last grid point exceeded
pi/2, sending the evaluator past theta = pi where it returns garbage.  Cross-check
against the project evaluator (agreement 5.6e-16) plus clipped grids: alpha_1 >= +0.122
on that interval, pattern intact.  Rule: grids are clipped and endpoints pinned,
always.

### 🔥 Item 2: AN EXPLICIT C^2-BALL INSIDE THE DOMAIN.  r0 = 1/20.  PROVED.

Every mirror-gauge eta with max(||eta||, ||eta'||, ||eta''||) <= 1/20 keeps
H_Sigma + eta inside D, with ordered anchored signs along the whole segment:

  (RC)     0.8389 (closed form) + 2 r0 = 0.1     <= 1        margin 0.0611
  ceiling  0.38784 (closed form) + sqrt2 r0      <  1/2      margin 0.0414
  signs    |delta alpha| <= 2 r0 = 0.1 < g = 0.1224, with six grid margins at
           h = 5e-4 and the PROVED Lipschitz constant L <= 1.76 from the sandwich
           (bootstrap: S <= 0.7506 + (S+1)h/2 => S <= 0.7513), and transversality
           FREE from the sandwich: alpha_1' >= alpha_2 >= 0.5975 - 0.1 > 0 in
           alpha_1's window, alpha_2' <= -alpha_1 <= -(0.4975) in alpha_2's.

Replaces the load-bearing direction of the old HEURISTIC "D is a C^2-ball": the domain
CONTAINS the explicit ball of radius 1/20 in the mirror class.  The outer k^-2 radius
stays a measurement.  Grid points are double precision; margins exceed evaluation error
by eleven orders; the Lipschitz constant is proved, not sampled.

### 🟢 Item 3: ONE CERTIFICATION METHOD END TO END

Sigma's cell constant 73/100 is now ALSO certified by the covering route alone:
spectrum >= -4 (absorption) + covering [-4, 73/100] at lens (beta, pi/2-2beta, beta),
3074 boxes.  Negative control at 74/100 refused, failing box c in [0.7310, 0.7313],
bracketing c* = 0.7309566.  The decoupled chain and its min-max oscillation step are no
longer load-bearing anywhere; they remain in the note as the hand-checkable route to 2/3.

### Ledger

Sandwich PROVED (Lean F30).  Disc counterexample PROVED (Lean F30c for the curvature
identity).  Ball r0 = 1/20 PROVED (grid + proved Lipschitz standard).  Unified
certificate VERIFIED-by-covering.  108 Lean theorems, zero sorry.  The open question that
remains from this block: does sofa-realizability force the ordered sign structure?

## 🧮🎆 CONCAVITY ON EVERY ORDERED ANCHORED CELL, PROVED.  UNIFORM CONSTANT ON MIRROR.

Crux (I1): CRUX-C -- the main theorem was perturbative for two reasons, (RC) and
concavity known only on measured cells.  The second reason is now REMOVED.

### The reduction (Lemma M, one line)

  B_{E1,E2}[eta] = B_{E2,E2}[eta] - int_{E2 \ E1} (q-p')^2  <=  B_{E2,E2}[eta]

for ANY E1 subset E2 (E1 need not be an interval).  So concavity for every cell with
{a1<0} subset {a2>0} and {a2>0} = [0,tau) anchored reduces to the DIAGONAL family
D_tau = B_{[0,tau),[0,tau)}.  Falsified first: 60 random (t1,t2,eta), min slack +1.5e-2.

### THEOREM (diagonal concavity): D_tau <= 0 for every tau in [0, pi/2].  PROVED.

Three overlapping ranges:
  (a) tau <= 1/sqrt(3): by hand.  Trace + Poincare + Young at s = 1/(2tau); the
      p'-coefficient collapses to (-3/2 + 1 + 1/2) = 0 exactly and the q'-coefficient is
      3tau^2 - 1 <= 0.  Verified on 1000 random (p,q): zero violations.
  (b) sigma = pi/2 - tau <= 1/18: by hand, spectral splitting q = a sin t + r.  The
      marginal mode (0, sin t) of the corner (D_{pi/2} annihilates it -- this is the
      "-0.0001 E1-all-E2-all" mystery row of the old table, EXPLAINED) forces the
      argument to see the mode: DN gap 9 gives int r'^2 <= (9/8)D, ||r||^2 <= D/8; the
      damping is -(1/2) a^2 sin 2sigma; collected coefficients (x = 5/4, y = 9/25):
      a^2: (4/5)sigma(cos^2 sigma - 1) <= 0;  D: -2/7 + 25pi sigma/16 <= 0 for
      sigma <= 1/18;  P^2: -174/100 + 5/4 + 9/25 = -13/100 < 0.  600 random checks pass.
  (c) tau in [0.55, 1.5153]: CERTIFIED.  D_tau is ambi_system's 2x2 system with lens
      [tau, 0, pi/2 - tau].  Spectrum bounded below by -4 (one-line absorption), and
      Phi(c;tau) != 0 on [-4,0] x [0.55,1.5153] by ADAPTIVE INTERVAL COVERING: 305 boxes,
      no enclosure contains 0, lengths carried as balls.  ambi_anchored.py, checkpointed.

Ranges overlap: [0, 0.5774] u [0.55, 1.5153] u [1.51524, pi/2].  QED

NEGATIVE CONTROLS (I12/I16).  Sub-second certification triggered the too-fast alarm; the
controls answered it: widening the c-window past the measured first eigenvalue is REFUSED,
and the failing boxes LOCALISE the eigencurve -- mirror at (0.7853, 0.376) matching the
family minimum 0.370 at pi/4, diagonal at (1.514, 0.041) matching c1 ~ 0.043.  The
covering is fast because the certified region is far from the spectrum, not because it is
vacuous.

🔴 AN ENDPOINT GAP CAUGHT IN MY OWN RUN.  The first mirror covering used tau <= 0.7853,
which is LESS than pi/4 = 0.78539816: a 1e-4 sliver of the family was uncovered.  Re-run
with tau <= 0.7854 > pi/4.  For tau slightly past pi/4 the middle length crosses zero and
the transfer formula is an analytic continuation, harmless: the enclosure covers every
real tau in each ball, in particular all of [0, pi/4] where the formula IS the shooting
determinant.

### THEOREM (uniform constant on the mirror family).  c1(tau) > 3/10 for all tau in
[0, pi/4]: covering of [-4, 3/10] x [0, 0.7854], 249 boxes.  Measured: c1 falls 0.875 ->
0.370 along the family; Sigma's cell 0.733.

### THEOREM (stability on the mirror class).  For every CONNECTED ambidextrous sofa with
mirror cap data satisfying (RC), whose alpha_1 stays single-crossing with tau_1 <= pi/4
along the segment from Sigma:

    |T| <= A_R* - (3/10) ||H - H_Sigma||^2_{L^2(0,pi)} .

NO SMALLNESS of H - H_Sigma is assumed.  The class is explicit and contains data as far
from Sigma as tau_1 anywhere in [0, pi/4] (Sigma sits at beta = 0.2897).  The one
smallness constraint remaining in the architecture is (RC) itself.

### Why the decoupled chain could never do this

The scalar chain, optimised over its parameters, gives -0.04 at tau = pi/4 and -1.9 at
tau = 1.45 on the diagonal against true values +0.37 and +0.08.  Past tau ~ 0.6 the
pointwise Cauchy-Schwarz losses exceed the entire eigenvalue.  Only the system
formulation (the F28 total-derivative structure) reaches the family.

### Ledger

Lemma M PROVED (+ Lean cell_mono).  Theorem D PROVED (ranges (a),(b) by hand with 1600
random-function checks, range (c) certified; Lean F29 verifies the collected rational
coefficients incl. the pi-bound steps).  Corollary anchored PROVED.  Mirror-uniform
PROVED.  Mirror stability PROVED.  Prop "beyond"'s eleven-entry table DEMOTED to a
cross-check.  105 Lean theorems, zero sorry.  Exit state: SHIPPED (I19).

## 🎆 GERVER IS EXCLUDED BY CONNECTEDNESS, NOT BY (RC).  AND A MIRROR IDENTITY.

### 🎆 (a) The answer to "find a substitute for (RC) that Gerver satisfies"

The substitute exists ((EB_theta), previous entry), Gerver satisfies it with 150x room,
and it changes nothing, because (RC) was never what excluded Gerver.  Along
H_s = (1-s) H_Sigma + s H_Gerver:

    s          0.000   0.200   0.400   0.406   0.500   0.700   1.000
    M = max c_y  0.388   0.443   0.498   0.500   0.526   0.581   0.664
    omitted strip  0       0       0    1.3e-5  0.0261  0.0815  0.1646

M crosses 1/2 at s = 0.406.  By the Connectedness ceiling (already in the note), M > 1/2
forces every ambidextrous sofa with that corner path to OMIT a vertical strip of width
(2M-1)/(2 tan t_0), and a CONNECTED one to lie entirely on one side of it, contradicting
that it meets both arms of the hallway.  At Gerver M = 0.6643 and the omitted strip has
width 0.1646.

    NO CONNECTED AMBIDEXTROUS MOVING SOFA HAS GERVER'S CAP DATA.

So the framework excludes Gerver CORRECTLY.  It is a property of the competitor class, not
a defect of the curvature hypothesis, and no weakening of (RC) can or should reach it.
The standing objection "the method fails on the one solved case" is answered: Gerver's
sofa is a one-corner sofa, and its cap is not the cap of any connected ambidextrous sofa.
This is the single most useful thing for the paper's defensibility.

### 💧 (b) The sign cell is NOT automatic -- falsified

Rule 3, 400 random admissible perturbations of H_Sigma (4 modes, sigma = 0.05):
125 gave NON-ANCHORED sign sets.  So the sign-cell restriction cannot simply be dropped;
it is a genuine "near Sigma" condition, consistent with D being a C^2-ball.  0 of the
anchored ones had tau_1 > tau_2.

### 🎆 (c) THE MIRROR IDENTITY, found while testing (b)

Every row of the Gerver-segment table had tau_1 + tau_2 = 1.5695 at grid spacing 0.0026.
At high resolution the sum is pi/2 to 1e-10 along the whole segment, and NOT for random
perturbations (errors up to 7e-2).  So it is structural.

🔴 MY FIRST EXPLANATION WAS FALSE.  I proposed left-right symmetry H(pi-th) = H(th) and
tested it: the discrepancy is 0.33 for Sigma and 1.23 for Gerver.  Not small, not it.

The pointwise test then gave the answer: a2(pi/2 - t) = a1(t), ratio 1.0000 at every
sampled point.  The condition behind it is

    H(theta) - H(pi - theta) = A cos(theta),     A := H(0) - H(pi),                (M)

which says h(u) - h(sigma u) = <(A,0), u> for the mirror sigma(x,y) = (-x,y): the cap
equals its own mirror image TRANSLATED by (A,0), i.e. it is symmetric about the vertical
line x = A/2.  The axis is not x = 0, which is exactly why the naive test failed.
Verified to 7e-16 for Sigma (A = -0.3341), Gerver (A = -1.2275), and arbitrary
interpolations.

  LEMMA (mirror caps).  Under (M), a2(pi/2 - t) = a1(t) for all t, hence E2 = pi/2 - E1
  as sets and tau_1 + tau_2 = pi/2.

  Proof.  (M) gives H(pi/2 - t) = H(pi/2 + t) + A sin t and, on differentiating,
  H'(pi - t) = -H'(t) - A sin t.  Then
    a2(pi/2 - t) = [H(pi/2+t) + A sin t] - 1 + [-H'(t) - A sin t] = H(pi/2+t) - 1 - H'(t)
                 = a1(t).   QED

WHAT IT BUYS.
  * (M) is LINEAR in H once A is a free parameter, so the mirror caps form a linear
    SUBSPACE and intersecting D with it preserves convexity.  Free of charge.
  * On that subclass the anchored sign pattern is fixed by ONE number tau_1, and the
    order condition tau_1 <= tau_2 of Proposition "beyond" collapses to the scalar
    inequality tau_1 <= pi/4 = 0.785398.  At Sigma tau_1 = beta = 0.289654, margin 0.4957.
  * It explains the Sturm-Liouville "miracle": L_1 + L_2 = pi/2 exactly, which forced
    Lambda(0) = 1 exactly, IS this identity -- the two lengths are tau_2 and tau_1.
  * Both Sigma and Gerver's cap satisfy (M), so it is not a restriction tuned to Sigma.

## 🧮🔥 INVENTION SPRINT: (RC) IS REPLACEABLE BY AN EXCESS BUDGET.  GERVER IS STILL OUT.

Crux (I1): (RC) enters at exactly one point -- it forces E := V - |N| = 0 so that
Q = |C2| - 2V is TIGHT.  Separation and Reynolds give, with NO curvature hypothesis,

    |T| = |C2| - 2|N| = Q + 2E ,    E >= 0 .

Unblocking criterion: the weakest convex condition replacing {E = 0}, at PROVED, with a
measurably larger domain.

### 🧮🎆 (a) NO-GO: task #21 as stated is IMPOSSIBLE.  PROVED.

Task #21 asked for a CONCAVE upper bound Etil on the excess.  There is none.  If Etil is
concave with Etil >= 0 and Etil(Sigma) = 0, and Sigma is in the algebraic interior of a
convex D', pick a, b in D' with Sigma = (a+b)/2; concavity gives

    0 = Etil(Sigma) >= (1/2) Etil(a) + (1/2) Etil(b) >= 0 ,

so Etil(a) = Etil(b) = 0, hence Etil = 0 and E = 0 on all of D'.  Any architecture of that
shape is confined to the injectivity locus, which is where the theorem already lives.
Four sessions of task #21 were chasing an object that cannot exist.  Kill it.

### 🧮🔥 (b) The spec was too strong.  (EB_theta), and it is a two-line proof.

U = Q + 2 Etil concave does NOT need Etil concave, only that Etil's convexity fit inside
Q's STRICT concavity.  With (1/2) d^2 Q <= -c ||eta||^2 there is a budget of exactly c.

  THEOREM (EB_theta).  D' convex, Sigma in D', theta in [0,1], with separation M < 1/2,
  (1/2) d^2 Q <= -c ||eta||^2 on D', and

      (EB_theta)    E(H) <= (1/2) theta c ||H - H_Sigma||^2_{L^2(0,pi)} ,

  then  |T| <= A_R* - (1-theta) c ||H - H_Sigma||^2.

I13 BACK-TRANSLATION.  Compiling the U-construction down, it is elementary and U is
scaffolding:  |T| = Q + 2E <= (A_R* - c||eta||^2) + theta c ||eta||^2.  Reported as the
two-line chain, machinery demoted.  Rule 4: neither ingredient is new -- a non-negative
concave function vanishing at an interior point is identically zero, and restoring
concavity by adding a quadratic is ordinary semiconcavity.  What is new is WHICH condition
this identifies.  theta = 0 is the existing theorem; theta > 0 ADMITS E > 0.  The size of
the escape is proportional to c, so this session's 0.1532 -> 0.7310 is a 4.8x larger
budget, not a cosmetic gain.

### 🧮🔥 (c) CASH VALUE (I14): the domain radius grows about 4.8x

Along the bump at c0 = 1.0, w = 0.45, using the excess scan and theta = 2E/(c*||eta||^2):

    eps      0.0141   0.0200   0.0283   0.0400   0.0566   0.0800
    theta     0.100    0.301    0.683    1.276    2.090    3.106

theta = 1 is crossed between eps = 0.0283 and 0.0400, both in the RELIABLE range of the
Richardson extrapolation.  (RC) fails at eps_c = 0.006492.  So (EB) extends the admissible
radius from 0.0065 to about 0.031: a factor of 4.8, with a positive stability constant
retained for any theta < 1.  Separation does not bind until eps = 0.444, i.e. 68x later.

### 💧💧 (d) BUT GERVER IS STILL OUT, AND NOT BECAUSE OF (RC)

Along H_s = (1-s) H_Sigma + s H_Gerver, with |N| Richardson-corrected at n = 2000, 4000:

    s        0.15     0.30     0.45     0.60     0.75     0.90     1.00
    tau_1  0.2568   0.2188   0.1769   0.1284   0.0694   0.0210   0.0000
    tau_2  1.3127   1.3507   1.3926   1.4411   1.5001   1.5485   1.5708
    E      2.4e-8   7.6e-8   1.5e-7   1.2e-6   2.2e-5   4.3e-4   1.2e-3
    theta  0.0000   0.0000   0.0000   0.0000   0.0002   0.0030   0.0066

(EB) holds all the way to Gerver at theta = 0.0066, and at theta = 0.0072 even if every
unreliable row's excess is bounded by its own Richardson correction.  The concavity
constant RISES along the segment (0.753 at s = 0.15 to 0.875 at s = 1), so Sigma's own
cell is binding and c = c* is correct.  All cells are anchored with tau_1 <= tau_2, which
is exactly the family Proposition "Beyond Sigma's own cell" covers.

So (RC) is NOT what keeps Gerver out.  SEPARATION is:

    (RC) fails at        s = 0.3979
    separation fails at  s = 0.4058        <- binds 2% later, and the chain stops
    (EB) fails at        never (s > 1)

M = max c_y crosses 1/2 at s = 0.406.  Past that the two niches OVERLAP, so
|U u rho U| < 2|N| and the true area EXCEEDS |C2| - 2|N|: the identity |T| = Q + 2E fails
in the wrong direction and the bound is void.  Gerver sits at s = 1, still 2.5x away.

I12 TOO-STRONG TEST, passed.  The maximal ambidextrous sofa with Gerver's cap data has
area |C2| - 2|N| = 1.213, against A_R* = 1.645, so nothing false is proved.  The (EB)
bound at s = 1 would read |T| <= 1.292, which is consistent and not vacuous.
(Gerver's own 2.2195 is its area as a ONE-CORNER sofa; that shape is not ambidextrous.)

### I13 DIFFICULTY ACCOUNTING, and a correction to my own advice

The obstruction MOVED, it did not disappear.  Last session I said the highest-leverage
move was "find a substitute for (RC) that Gerver's cap satisfies".  The substitute exists,
Gerver satisfies it with 150x room, and it does not help: on the Gerver segment (RC) and
separation fail 2% apart, so (RC) was never the binding constraint in that direction by
any margin worth having.  The real obstruction on the road to Gerver is OVERLAPPING
NICHES, and it is a different problem: it needs |U u rho U| rather than 2|N|, i.e. an
inclusion-exclusion term, not a curvature condition.

I19 EXIT STATE: SHIPPED for the domain widening (contracts proved, cash value banked at
4.8x radius), and the Gerver target is a fresh crux entry, not this one.

## 🔥 TASK #21: THE PIVOT WAS TRUE AND VACUOUS.  THE REAL QUESTION IS THE ONSET AT (RC).

### 🔴 My framing of #21 was wrong, and the answer needs no measurement

I framed #21 as: is d^2 E(Sigma) = 0 for the flux excess E = V - |N|?  If so, A = Q + 2E
has d^2 A(Sigma) = d^2 Q(Sigma) and the TRUE functional is sharply concave at Sigma.

It is zero, and no measurement is needed.  (RC) implies all three injectivity conditions,
hence V = |N|, hence E = 0 EXACTLY (result 31, PROVED); and (RC) holds on a
C^2-neighbourhood of Sigma (result 44).  So E vanishes IDENTICALLY near Sigma and
d^2 E(Sigma) = 0 trivially.

The pivot is therefore TRUE and VACUOUS.  d^2 A = d^2 Q holds exactly where E = 0, which
is exactly the domain D on which the theorem already holds.  It buys no widening at all.

E is not a power of eps.  It is ZERO up to a threshold eps_c -- where the perturbation
first pushes max(H+H'') past 1 -- and grows past it:

    bump (1.0,0.45):  eps_c = 0.006475        bump (0.6,0.30):  eps_c = 0.001999

My sweep ran eps in [0.0141, 0.08], i.e. 2x to 12x PAST the threshold in the first
direction and 7x to 40x in the second.  Fitting a power of eps to a function of
eps - eps_c is what produced the spurious "local exponent" drifting 3.14, 3.42, 3.81,
4.35.  It was measuring the far field.

### 🔥 THE QUESTION THAT ACTUALLY MATTERS, and what the data says

For eps just past eps_c, how fast does E turn on?  If E ~ (eps - eps_c)^p with p >= 2,
then A = Q + 2E still has a non-positive second variation across the (RC) boundary and D
CAN be widened past (RC).  If p < 2, (RC) is the true limit.

Refitting against eps - eps_c, with a reliability flag: corr/E is the 1/n bias SUBTRACTED
at n = 8000 divided by what survives the subtraction.  Above 1 the extrapolation removes
more than it keeps and the row is not evidence.

  bump (1.0,0.45), eps_c = 0.006475          bump (0.6,0.30), eps_c = 0.001999
   eps    E_inf      p     corr/E             eps    E_inf      p     corr/E
  0.0800  4.351e-4    --    0.02  ok         0.0800  6.214e-4    --    0.02  ok
  0.0566  1.466e-4  2.840   0.06  ok         0.0566  2.465e-4  2.592   0.04  ok
  0.0400  4.468e-5  2.953   0.21  ok         0.0400  9.415e-5  2.656   0.10  ok
  0.0283  1.196e-5  3.070   0.77  ok         0.0283  3.588e-5  2.621   0.26  ok
  0.0200  2.639e-6  3.159   3.52  UNREL      0.0200  1.592e-5  2.143   0.58  ok
  0.0141  4.361e-7  3.141  21.34  UNREL      0.0141  7.786e-6  1.801   1.19  marginal

🔴 THE CLEANEST-LOOKING NUMBERS ARE THE WORST ONES.  The first direction's p = 3.159 and
3.141 sit beautifully on p = 3 and are both UNRELIABLE: at eps = 0.0141 the Richardson
correction is twenty-one times the value it leaves behind.  I had those two rows in hand
and read "p is about 3" off them before the diagnostic was written.  It is not a
conclusion, it is the extrapolation's own noise.

WHAT THE RELIABLE ROWS SUPPORT.  Every one of them, in both directions, has p > 2 -- the
smallest is 2.143.  That is the encouraging direction.  But the two directions do not
agree (about 2.95 versus about 2.6), the second one TRENDS DOWNWARD as eps decreases, and
its least reliable row falls to 1.801.  So:

    p > 2 is SUGGESTED, NOT ESTABLISHED.  #21 stays open.

The obstruction is precision, and it is well identified: |N| carries a 1/n polygon bias of
about 7.4e-2/n, identical across directions and eps, and the signal near the threshold is
smaller than the correction.  Settling p needs |N| computed EXACTLY, not by a
floating-point polygon oracle -- Rule 8 puts that in Rust.  That is now the whole of #21.

## 🎆🎆 THE SHARP CONSTANT, CERTIFIED.  0.1532 -> 2/3 -> 73/100, sharp 0.7309566

### 🎆 Item A: the 2/3 certificate is now RIGOROUS, not 30-digit floating point

Rule 7 says floating point is evidence, never proof, and the headline 2/3 ended in two
sign evaluations at 30 working digits.  `algorithm/rigorous/ambi_certify.py` replaces them.
Three things had to be made rigorous, not one:

  beta is not a decimal but the root of a cubic, tan(beta) = u/2 with u^3+3u = 2.
  Certified by EXACT RATIONAL bisection (f is strictly increasing, so a sign change on a
  rational interval is a proof of enclosure), then a ball-arithmetic arctangent.

  The transfer matrices: at kappa = 1/4, lambda = 37/50, c = 2/3 every weight and mass is
  an exact rational, so each k^2 = (m+c)/w is exact.  Only the three lengths and the
  trigonometric functions are inexact, and arb carries rigorous error bounds:

      Phi_L(2/3) = 0.0046739486452026048... +/- 6.4e-73    certified > 0
      Phi_R(2/3) = 0.0026447861413929500... +/- 8.3e-73    certified > 0

  🔴 A REAL GAP IN THE PROOF, found by writing this out.  Phi(2/3) > 0 does NOT by itself
  give c_1 > 2/3: Phi is positive on (-inf,c_1), negative on (c_1,c_2), and POSITIVE AGAIN
  on (c_2,c_3).  One also needs 2/3 < c_2.  Min-max supplies it crudely: since
  int w eta'^2 >= w_min int eta'^2 and -int m eta^2 >= -m_max int eta^2,

      c_k >= w_min * lambda_k - m_max,   lambda_k = (2k)^2 (DD), (2k-1)^2 (DN) on length pi/2

  giving c_2 >= (3/4)(16) - 63/13 = 7.15 on the left and 1*9 - 6 = 3 on the right, both far
  above 2/3.  At k = 1 the same bound gives -1.85 and -5, useless -- which is exactly why
  the transfer matrix is needed for c_1 and not for c_2.  The note now carries this step.

Cross-checked in mpmath interval arithmetic sharing no code, with beta re-certified the
other way round (pick rational bounds, verify tan(b_lo) < u/2 < tan(b_hi)).  Negative
control: the certificate correctly REFUSES at c = 0.68, 0.70, 0.75.

### 🎆 Item B: the splitting was unnecessary.  The SHARP constant, in closed form.

The two halves of [0,pi] are the SAME interval re-indexed.  Put p(t) = eta(t) and
q(t) = eta(t+pi/2) on [0,pi/2]; then the whole of (Q2) is ONE quadratic form in (p,q),

    (1/2) d^2 Q = int_0^{pi/2} L,
    L = 2p^2 - 2p'^2 + q^2 - q'^2 - 1_{E2}(p+q')^2 + 1_{E1}(q-p')^2 ,

with every boundary condition forced: p(0) = p(pi/2) = 0 is the gauge, q(0) = eta(pi/2) = 0
is the same gauge from the other half, q(pi/2) = eta(pi) is free.  NOTHING is discarded, so
the first eigenvalue of this system IS the sharp constant.

WHY THE SPLITTING LOST.  Writing M = -L as a p'^2 + b q'^2 + g p^2 + d q^2 + 2e pq' + 2f qp':

             piece          a    b    g    d    e    f
          [0,beta)          1    2   -1   -2    1    1
    [beta,pi/2-beta)        2    2   -1   -1    1    0
    [pi/2-beta,pi/2)        2    1   -2   -1    0    0

On [0,beta) -- exactly where the obstruction lives, since that is where E1 and E2 overlap --
e = f = 1 and 2pq' + 2qp' = 2(pq)' is a TOTAL DERIVATIVE.  The obstruction and the resource
cancel there up to the single boundary value 2 p(beta) q(beta).  The coupling was never
pointwise; that is why every pointwise Cauchy-Schwarz splitting loses and this loses nothing.

SOLVING IT.  With momenta P = a p' + f q and Q = b q' + e p the EL system is first order in
(p,P,q,Q) with piecewise constant matrix

    A(c) = [[0, 1/a, -f/a, 0], [g-c-e^2/b, 0, 0, e/b],
            [-e/b, 0, 0, 1/b], [0, f/a, d-c-f^2/a, 0]] ,

so the transfer is a product of three 4x4 matrix exponentials.  p(0) = q(0) = 0 leaves a
2-dimensional solution space; propagating a basis and imposing p(pi/2) = 0, Q(pi/2) = 0
gives a 2x2 determinant Phi(c) whose zeros are the eigenvalues:

    c* = 0.730956620836

CERTIFYING IT WITHOUT A MASLOV INDEX.  For a system the oscillation count is a Maslov index,
not a zero count, so the scalar trick is unavailable.  It is not needed.  Two facts compose:
(a) c_1 >= 2/3, PROVED above; (b) Phi has no zero on [2/3, 73/100], certified by covering
that interval with 60 balls at 400 bits and checking that no enclosure contains 0.  Hence

    (1/2) d^2 Q[eta] <= -(73/100) ||eta||^2_{L^2(0,pi)} .        PROVED

    0.1532 (20.9%)  ->  2/3 (91.2%)  ->  73/100 (99.9% of sharp)

EQUIVALENCE CHECK: the system form and the hat-basis Hessian agree to 6.8e-16 relative on
random eta at m = 64 and 128.  NEGATIVE CONTROL: the same covering of [2/3, 0.74] finds 2
enclosures containing 0, correctly refusing.

### 🔴 A CORRECTION THIS FORCED: the "sharp 0.7323" was never sharp

Earlier turns quoted 0.7323, the P1 finite-element value at m = 256, as the sharp constant.
Rayleigh-Ritz gives an UPPER bound on an eigenvalue and that sequence had not converged:

    m      128       256       512      1024      2048        exact
         0.733086  0.732285  0.731311  0.731247  0.731073   0.7309566

The true sharp constant is 0.7309566, so every "sharp value" quoted before this turn is an
over-estimate by about 0.2%.  NO conclusion moves: every certificate in the project is a
lower bound and every finite-element number an upper bound, so the two never crossed.  The
target was mis-stated, not the results.  Corrected in note.tex, README and here.

### 🟢 Item 3: the covering reaches every c < c*, and the limit is compute

Nothing in the argument stops at 73/100.  Certifying a target c requires the enclosures of
Phi to separate from 0 on every subinterval of [2/3, c], and near the root those intervals
must shrink:

    target      73/100     0.7305     0.7309    0.73095    0.730956
    gap to c*   9.6e-4     4.6e-4     5.7e-5     6.6e-6     6.2e-7
    N needed        60         60        800     12000     > 12000

0.73095 is certified, i.e. 99.9991% of c*.  73/100 stays the headline because a reader can
check it with 60 balls.  There is no residual gap in the method, only compute.

### 🔴 CORRECTION TO THE PREVIOUS ENTRY: it was the GAUGE, not the ceiling atom

The previous entry blamed the (1.4,0.35) blow-up on V_of being invalid across the ceiling
facet atom.  That is WRONG, and the right explanation is simpler and more useful.

sigma = (F-1) tan t + G-1 is integrated up to t = pi/2, where tan diverges.  It stays
finite for one reason only: F(pi/2) = H(pi/2) = 1, so F-1 vanishes there at the same rate.
That is exactly THE GAUGE, H(0) = H(pi/2) = 1, i.e. eta(0) = eta(pi/2) = 0.  A bump with
bump(pi/2) != 0 breaks it, sigma genuinely diverges, and V is infinite.  The clean
E/eps^2 = 4.010e4 was sigma^2 ~ eps^2 tan^2 t, a divergence sampled at fixed quadrature
nodes -- correctly proportional to eps^2, and meaningless.

    direction        bump(0)      bump(pi/2)    gauge
    (1.0,0.45)       0            0             RESPECTED
    (0.6,0.30)       0            0             RESPECTED
    (1.4,0.35)       0            2.691e-1      VIOLATED

So V_of is not broken and the ceiling atom is not involved.  The direction was never an
admissible competitor.  ambi_excess.py now ASSERTS the gauge before measuring, which is
the durable fix; the same trap would catch any future bump straddling pi/2.

### 🔥 AND THE NOISE FLOOR IS |N|, NOT V -- SO IT IS REMOVABLE

V is a one-dimensional integral of an analytic integrand and is already converged: at
eps = 0.02 it agrees to 14 digits at 200, 400 and 800 Gauss-Legendre nodes per phase.
The floor is entirely the polygon oracle for |N|, and it is a clean 1/n bias:

    n         2000        4000        8000       16000
    E       3.976e-5    2.119e-5    1.192e-5    7.278e-6
    diffs      1.857e-5    9.27e-6     4.64e-6           ratios 2.003, 1.997

Differences halving exactly means bias = C/n with C independent of n, so Richardson
removes it: E_inf = 2 E(2n) - E(n).  Both pairs give E_inf = 2.6e-6 at eps = 0.02,
against a raw reading of 2.1e-5 -- the "floor" was 8x the signal.  Extracting 2.6e-6 by
differencing two numbers of size 0.187 is a 5-digit cancellation, which is what stalled
the earlier sweep.  ambi_excess.py does the extrapolation and sweeps eps to read off the
order of vanishing.

### 🔴 TASK #21 PIVOT IDENTIFIED, MEASUREMENT INCONCLUSIVE, AND A TOOL BUG FOUND

The question that decides #21 is narrower than "find a concave upper bound on the excess".
Write A := |C2| - 2|N| for the TRUE area of the maximal sofa with cap data H, so that
A = Q + 2E with E = V - |N| >= 0 the flux excess and E(Sigma) = 0.  Since Sigma minimises
E, d^2 E(Sigma) >= 0.  If it is ZERO, then

    d^2 A(Sigma) = d^2 Q(Sigma) <= -0.73 ||eta||^2 ,

so the TRUE functional is strictly concave at Sigma with the sharp constant, and (RC)
would be needed only for the non-local statement, not the local one.  That is the pivot.

MEASURED, AND INCONCLUSIVE.  Along two valid bump directions E falls faster than eps^2
between eps = 0.08 and 0.04 (by 7.2x and 5.7x, against 4x for a quadratic), consistent
with d^2 E = 0.  But below eps = 0.02 the values stop falling -- 2.12e-5 then 1.87e-5 at
(1.0,0.45) -- which is the Shapely polygon-oracle noise floor, not a signal.  So the
measurement is consistent with d^2 E = 0 and does NOT establish it.  Settling it needs an
EXACT excess computation, which by Rule 8 belongs in Rust, not in a floating-point
polygon oracle.  NOT claimed either way.

🔴 SUPERSEDED BY THE CORRECTION ABOVE -- the cause is the gauge, not the atom.
A DIRECTION THAT NEARLY BECAME A FINDING.  A third direction, the bump at c0 = 1.4 with
w = 0.35, gave E/eps^2 = 4.010e4 CONSTANT across eps = 0.08, 0.04, 0.02, 0.01 -- a
textbook clean second-order term, and it would have refuted the pivot.  It is an artefact.
That bump spans [1.05, 1.75] and straddles theta = pi/2, where the cap carries the ceiling
FACET, an atom of the surface measure.  Checking the pieces separately: |N| = 0.1987 and
|C2| = 2.0160 are both sane, but V_of returns 256.9 against a sofa area of 1.645.  So
V_of is INVALID for perturbations straddling the atom, and the constant E/eps^2 was
measuring that failure.  Recorded so the same number is not believed later.

### 🟢 Lean F28

`overlap_integrand`            the integrand on E1 n E2 collapses to diagonal + 2 cross terms
`cross_is_total_derivative`    given the product rule, those cross terms are -2 (pq)'
`telescope_gauge`              with p(0) = 0 the telescoped integral is 2 p(beta) q(beta)

100 theorems, 14 defs, zero sorry.  Axioms [propext, Quot.sound].  NOT formalized: the
product rule, the EL system, the 4x4 matrix exponential, the interval covering.

### New files

`algorithm/rigorous/ambi_certify.py`  the 2/3 certificate in arb ball arithmetic, with the
                                      min-max step, an independent mpmath recheck, and a
                                      negative control.
`algorithm/rigorous/ambi_system.py`   the 2x2 system, the sharp constant, the equivalence
                                      check, the interval covering, and its negative control.

## 🎆 THE CONSTANT IS NOW WITHIN 9% OF SHARP: 0.1532 -> 2/3, PROVED

### 🔥 Item 1: the concavity constant, by two Sturm-Liouville eigenvalues

The previous chain lost a factor of 4.8 in two places.  It split [0,pi/2] into [0,beta]
and [beta,pi/2] and applied a SEPARATE Poincare inequality on each (P1 = 29.4135,
P2 = 1.5035, P3 = 1), and it DISCARDED the E2 term of (Q2) instead of spending it.  Both
losses go away if each half is treated as ONE weighted eigenvalue problem.

Two Cauchy-Schwarz steps, with free parameters lambda in (0,1) and kappa in (0,1):

  (S1)  -(a+b)^2 <= -lambda b^2 + [lambda/(1-lambda)] a^2,   a = eta(t), b = eta'(t+pi/2)
        on E2.  Exact, because (1+r)(1-lambda) = 1 makes
        (1+r)a^2 + 2ab + (1-lambda)b^2 = (sqrt(1+r) a + sqrt(1-lambda) b)^2.
        BUYS gradient weight lambda on [pi/2,pi-beta]; PAYS mass r on [0,pi/2-beta).
  (S2)  (x-y)^2 <= (1+1/kappa) x^2 + (1+kappa) y^2,   x = eta(t+pi/2), y = eta'(t) on E1.
        PAYS mass q = 1+1/kappa on [pi/2,pi/2+beta]; PAYS gradient weight 1+kappa
        on [0,beta).

After substituting s = t + pi/2 the two halves DECOUPLE:

  (1/2) d^2 Q[eta] <= int_0^{pi/2} (m_L eta^2 - w_L eta'^2)
                    + int_{pi/2}^pi (m_R eta^2 - w_R eta'^2)  =: B[eta]

  w_L = 1-kappa on [0,beta), 2 after      m_L = 2+r on [0,pi/2-beta), 2 after
  w_R = 1+lambda on [pi/2,pi-beta), 1 after   m_R = 1+q on [pi/2,pi/2+beta), 1 after

so B[eta] <= -min(c_L,c_R) ||eta||^2_{L^2(0,pi)} with c_L, c_R the first eigenvalues of

  -(w_L eta')' - m_L eta = c eta on (0,pi/2),  eta(0) = eta(pi/2) = 0        [the GAUGE]
  -(w_R eta')' - m_R eta = c eta on (pi/2,pi), eta(pi/2) = 0, eta'(pi) = 0   [pi is free]

CERTIFYING THEM IN THE RIGHT DIRECTION.  FEM / Rayleigh-Ritz gives an UPPER bound on an
eigenvalue, which is useless here.  Both coefficients are piecewise constant with three
pieces, so the IVP solution is a product of three 2x2 transfer matrices, and by Sturm
oscillation the first eigenvalue is the SMALLEST ZERO of the shooting function Phi, with
Phi > 0 strictly below it.  So ONE SIGN EVALUATION is a lower bound.  At kappa = 1/4,
lambda = 37/50:

    Phi_L(2/3) = +0.00467395 > 0        Phi_R(2/3) = +0.00264479 > 0

hence c_L, c_R > 2/3 and, PROVED,

    (1/2) d^2 Q[eta] <= -(2/3) ||eta||^2_{L^2(0,pi)} .

    certified 0.1532 -> 2/3          sharp 0.732285 (m=256)
    20.9% of sharp  ->  91.0%        grid optimum 0.674944 at (kappa,lambda)=(0.26,0.74)

Since ||eta||_{L^2(0,pi/2)} <= ||eta||_{L^2(0,pi)}, this also lifts the [0,pi/2] constant
from 0.371 to 2/3, so the stability theorem now carries ONE constant, not two.

FALSIFICATION (Rule 3).  The chain is only valid if B - Hessian is positive semidefinite.
Assembled on the same hat basis, its smallest eigenvalue is +0.00e+00, -1.81e-14,
-4.92e-14 at m = 32, 64, 128: PSD at every resolution, so nothing was tightened anywhere.
The transfer-matrix roots also agree with a P1 FEM computation to 6 digits.

### 🔥 Item 2: the [pi/2,pi] eigenvalue IN CLOSED FORM, and Lambda > 1 PROVED

With mass 1 and weight w = 1+lambda_J on [pi/2,pi-beta], 1 on [pi-beta,pi], the transfer
product collapses to a transcendental equation:

    sqrt(w_1) cot( L_1 sqrt(Lambda/w_1) ) = tan( L_2 sqrt(Lambda) ),
    w_1 = 1 + lambda_J,   L_1 = pi/2 - beta,   L_2 = beta.                        (SL)

At lambda_J = 0 this reads cot(L_1 sqrt Lambda) = cot(pi/2 - L_2 sqrt Lambda), so
sqrt(Lambda)(L_1 + L_2) = pi/2; and L_1 + L_2 = pi/2 EXACTLY, so Lambda(0) = 1 EXACTLY.
That is precisely the marginal P3 = 1 that blocked the old chain, and it explains WHY
nothing was available on [pi/2,pi] until the weight was raised.

PROOF THAT Lambda > 1 FOR lambda_J > 0.  Put G(w_1) := sqrt(w_1) cot(L_1/sqrt(w_1))
- tan(beta).  Then G(1) = 0, and G INCREASES in w_1: the prefactor increases, while
L_1/sqrt(w_1) decreases and cot decreases on (0,pi), so the cotangent increases.  Hence
G > 0 for w_1 > 1.  The left side of (SL) decreases in Lambda and the right increases, so
the root moves right.  QED

    lambda_J     0       0.05      0.10     0.16483    0.25      0.35
    Lambda (SL)  1     1.049467  1.098883  1.162878  1.246819  1.345183
    Lambda (FEM) 1     1.049466  1.098881  1.162875  1.246814  1.345175
    G(1+lam_J)   0     0.042139  0.083948  0.137745  0.207843  0.289487

### 🟢 Item 3: the sigma term is assembled without evaluating tan anywhere

hess_sets in ambi_concavity.py now assembles -int_0^{pi/2}(eta tan t + eta')^2 in the
equivalent form +int_0^{pi/2}(eta^2 - eta'^2), valid because eta(0) = eta(pi/2) = 0 and
sec^2 - tan^2 = 1.  Identical spectrum (-0.735818, -0.733924, -0.733086, -0.732285 at
m = 32/64/128/256), and no unbounded coefficient is evaluated in the Hessian at all.
make_Q still uses tan: that is the FUNCTIONAL, not the Hessian, and is correct there.

### 🟢 Item 4: the lam_max/h proxies are RETIRED project-wide

Earlier turns quoted "lambda_max/h" for the concavity check.  Its SIGN is right (the mass
matrix is positive definite, so lam_max(M) < 0 iff lam_max(Mass^{-1}M) < 0), but its
MAGNITUDE is not a constant.  Every quoted magnitude is now normalised against
mass_stiff, in note.tex and in ambi_concavity.py:

    sign pattern                              old proxy    mass-normalised (m=128)
    Sigma's own cell                            -0.7216         -0.7331
    Baek injectivity (E1 empty, E2 all)         -0.8616         -0.8751
    crude worst case (E2 empty, E1 all)         +1.2306         +1.2499
    E1 = E2 = [0.4,1.2]  (NOT anchored)         +0.4071         +0.4123
    E1 = E2, three pieces                       +0.4156         +0.4225

and the eleven anchored (tau1,tau2) entries of Prop "beyond" likewise, all still negative.
ZERO sign changes, so no conclusion moves.  Two stale numbers in note.tex were fixed at
the same time: Remark "garding" quoted the pre-fix 0.7285 sequence, and the paragraph
after Theorem "concave" compared a half-interval bound against a full-interval measurement.

### 🔴 A duplicate LaTeX label found while recompiling

`eq:a1` was defined TWICE: on the constant a_1 = (1/4)sqrt(4+w) and on the arm
alpha_1(t) = G-1-F'.  LaTeX resolves duplicates to the LAST definition, so the three
references meaning the CONSTANT were silently pointing at the ARM.  The arm is now
`eq:arm1` and its five references were repointed.  note.tex compiles with 0 errors,
0 multiply-defined labels, 0 undefined references, 28 pages.

### 🟢 Lean F27

`e2_completion`  M*(P a^2 + 2K ab + M b^2) = (Ka + Mb)^2  when  M*P = K*K
`e1_split`       n(m+n)x^2 + m(m+n)y^2 - mn(x-y)^2 = (nx+my)^2   (no side condition)
`form_nonneg_of_completion`  M > 0 and M*F = S*S  =>  F >= 0

97 theorems, 14 defs, zero sorry.  Axioms [propext, Quot.sound]; the third needs only
[propext].  Core Lean has no `ring`; both identities go through as
`simp [Int.mul_add, Int.mul_sub, Int.mul_comm, Int.mul_left_comm]` then `omega`, which
works because simp's AC normalisation leaves a LINEAR identity in product atoms.  The `2`
in F27a had to be written `K*(a*b) + K*(a*b)`: with the literal, simp normalises to
`M*(K*(a*b)*2)` and omega no longer sees the same atom.

### New file

`algorithm/rigorous/ambi_sturm.py` reproduces all of the above: the PSD falsification
test, the two-parameter optimisation, the transfer-matrix roots at 30 digits, the sign
certificate, the sharp constants, and the closed form (SL) against FEM.

## THE ENDPOINT BUG AUDITED ACROSS THE PROJECT; THE J3 OBSTRUCTION REMOVED; LEAN F26

### Item 4 first: audit the endpoint-hat bug everywhere it could have propagated

ambi_garding.py had the SAME hand-built mass matrix, giving the endpoint hat at theta = pi
the interior weight 2h/3.  Fixed by adding a correctly ASSEMBLED helper mass_stiff(B) to
ambi_hessian.py and routing everything through it, with a docstring recording why.

Re-verification of every measured constant that used a hand-built matrix:

  Garding constant   0.7285 -> 0.7323   (now converging from above: .7358 .7339 .7331 .7323)
  anchored-cell table  all twelve entries shift by about 1.5%, ZERO sign changes:
     (0,pi/2) -0.863 -> -0.875   (beta,pi/2-beta) -0.723 -> -0.733
     (0.1,0.2) -0.139 -> -0.141  (0.3,0.5) -0.355 -> -0.361
     (0.5,0.9) -0.533 -> -0.541  (0.8,1.2) -0.445 -> -0.451
     (1.0,1.3) -0.340 -> -0.344  (1.2,1.4) -0.228 -> -0.231
     (1.4,1.5) -0.109 -> -0.110  (1.5,pi/2) -0.047 -> -0.047
     (0.2,1.5) -0.777 -> -0.788  (0.05,0.06) -0.040 -> -0.041
  non-concave counterexamples   [0.4,1.2] +0.409, three pieces +0.411 -- still positive

So EVERY concavity conclusion in the project is unaffected; only the magnitudes moved, and
only the single constant 0.7285 was ever quoted.  The coefficient-space "lambda_max/h"
proxies used in earlier turns never touched a mass matrix and are unaffected.

### 🔥 Item 1: the J3 obstruction is REMOVED

Stop splitting E2 off from the cap.  Writing the E2 bound as
-lambda int_{pi/2}^{pi-beta} eta'^2 + (lambda/(1-lambda)) int_0^{pi/2-beta} eta^2 and
splitting lambda = lambda_r + lambda_J, with lambda_r = B beta^2/2 absorbing the r^2
remainder as before, the [pi/2,pi] block becomes

    int eta^2 - int_{pi/2}^{pi-b} (1+lambda_J) eta'^2 - int_{pi-b}^{pi} eta'^2 ,

whose sign is governed by a WEIGHTED STURM-LIOUVILLE EIGENVALUE

    Lambda(lambda_J) = min [ int w eta'^2 ] / [ int eta^2 ],  eta(pi/2) = 0, eta(pi) free,
    w = 1 + lambda_J on [pi/2,pi-beta],  w = 1 on [pi-beta,pi].

The J3 coefficient is 1 - Lambda, and

    lambda_J   0      0.05     0.10    0.165    0.25     0.35
    Lambda     1     1.0495   1.0989  1.1629  1.2468   1.3452

Lambda(0) = 1 EXACTLY, reproducing the marginal P3 = 1 that blocked the previous chain, and
Lambda > 1 for every lambda_J > 0.  So J3 CAN be given a negative coefficient.

Best admissible parameters delta = 0.07, kappa = 3, lambda = 0.257 give coefficients
-0.4194, -0.1572, -0.1532 on J1, J2, J3, hence a FULL-INTERVAL estimate

    (1/2) d^2 Q <= -0.1532 ||eta||^2_{L^2(0,pi)} .

Neither this nor the earlier -0.3710 ||eta||^2_{L^2(0,pi/2)} implies the other: the first
has the better constant, the second controls the whole interval.  Both are now in the
stability theorem.  The gap to the sharp 0.7323 is still a factor of about 4.8, so the
obstruction is removed but the constant is not sharp.

### Item 2: the H^1 constants are in the note as a proposition

c1 = 0, 0.1, 0.3, 0.5 give c0 = 0.7323, 0.6114, 0.3571, 0.0760, each converging in m, with
the frontier close to c0 = 0.732 - 1.31 c1.

### 🟢 Item 3: LEAN F26

  sec_sq_sub_tan_sq   C^2 + S^2 = 1  =>  1 - S^2 = C^2, i.e. sec^2 - tan^2 = 1 cleared
  sigma_term_bounded  SQ - TQ = 1  =>  -E*TQ + E*SQ - D = E - D: the two unbounded pieces
                      of the sigma integrand cancel, leaving eta^2 - eta'^2

94 theorems, 14 defs, zero sorry, axioms [propext, Quot.sound].  The integration by parts
itself is analysis and is not formalized.

## 🎆 THE H^1 ESTIMATE HOLDS.  ONE WRONG MATRIX ENTRY CAUSED TWO FALSE NEGATIVES.

### 🔴 The bug

The hat at theta = pi is an ENDPOINT hat: its support is [pi-h, pi] only, so
int phi^2 = h/3 and int phi'^2 = 1/h -- HALF the interior values 2h/3 and 2/h.  My
hand-built mass and stiffness matrices used the interior values there.  One entry.

Consequences, all now corrected:

  * "The H^1 estimate could not be confirmed" -- WRONG.  It holds.
  * "The tan singularity in the sigma term is to blame" -- WRONG.  The singularity-free
    form gives IDENTICAL numbers.
  * "The maximiser concentrates on [pi-beta,pi] where cross terms offset the derivative" --
    an artefact of the wrong pencil.
  * The measured sharp L^2 constant 0.7285 -- WRONG; it is 0.7323.

The PROVED constant 0.3710 is unaffected: it comes from the analytic Poincare chain, not
from any matrix.  So the stability theorem in the paper stands as stated.

### 🔥 With correct matrices, the H^1 estimate holds and CONVERGES

    c1     0.0      0.1      0.3      0.5      0.7      1.0
    c0    0.7323   0.6114   0.3571   0.0760  -0.2560  -1.0000     (m = 256)

each converging in m.  So

    (1/2) d^2 Q  <=  -0.357 ||eta||^2_{L^2}  -  0.3 ||eta'||^2_{L^2} ,

and the frontier is close to c0 = 0.732 - 1.31 c1, vanishing near c1 = 0.56.  This is
STRICTLY STRONGER than the L^2 estimate.

### 🟢 A genuine simplification found en route (not the bug, but worth keeping)

    -int_0^{pi/2} (eta tan t + eta')^2 dt  =  int_0^{pi/2} (eta^2 - eta'^2) dt

for eta vanishing at 0 and pi/2, because -2 int eta eta' tan t = -int (eta^2)' tan t =
int eta^2 sec^2 t and sec^2 - tan^2 = 1.  Verified to 1e-12 on five test functions.  The
second variation therefore has NO unbounded coefficients anywhere.

### Item 1: the J3 gap is located, not closed

Reallocating the E2 budget CAN give J3' (on [pi/2,pi-beta]) a negative coefficient --
best found -0.1969 at delta=0.08, kappa=3, lambda=0.234 -- but J3'' on [pi-beta,pi] stays
at 0.  P3 = 1 is sharp there: the first Dirichlet-Neumann mode eta = sin(theta-pi/2) has
int(eta^2 - eta'^2) = 0 EXACTLY, so all of its negativity must come from the E2 term, which
acts only on [pi/2,pi-beta].  Closing the gap needs E2 handled JOINTLY with the cap on
[pi/2,pi], not split off first.  Still open, now precisely located.

### Item 3: anchoredness is stable near Sigma

    perturbation        tau1        tau2
    Sigma             0.2895      1.2800
    +-0.01 sin(2t)    0.3157/0.2751   1.2944/1.2538
    +-0.005 sin(4t)   0.2922/0.2869   1.2826/1.2773
    +-0.002 sin(6t)   0.2895          1.2800

Both sign sets stay anchored intervals with tau1 < tau2, so the segment argument's
hypothesis holds on a neighbourhood of Sigma and the extension is not vacuous.  Whether it
holds on all of D is untested.

### Item 4: Lean F25

  second_diff_nonpos_mono  non-positive second difference => slopes non-increasing
  concave_along_segment    + first slope <= 0 => the function never exceeds its start
  concave_from_critical    the case actually used, first slope = 0 from dQ(Sigma) = 0

92 theorems, 14 defs, zero sorry, axioms [propext, Quot.sound].

## ITEM 3 DELIVERED: THE RESULT EXTENDS BEYOND SIGMA'S CELL.  ITEMS 1 AND 2 DID NOT.

### 🔥 The bound and the uniqueness extend past the single cell

Q is C^1 and piecewise quadratic, so if EVERY cell met by the segment [H_Sigma, H] has
d^2 Q <= 0, then Q is concave ALONG THAT SEGMENT and

    Q(H) <= Q(Sigma) + dQ(Sigma)[H - H_Sigma] = A_R*,

using dQ(Sigma) = 0.  Convexity of the union of those cells is NOT needed -- only concavity
along the one segment.  This holds in particular whenever the segment meets only cells whose
sign sets are ANCHORED intervals E1 = [0,tau1), E2 = [0,tau2) with tau1 <= tau2:

  (tau1,tau2)  (0,pi/2) (.1,.2) (.3,.5) (.5,.9) (.8,1.2) (1,1.3) (1.2,1.4) (1.4,1.5) (1.5,pi/2) (.2,1.5) (.05,.06)
  lambda_max    -0.863   -0.139  -0.355  -0.533   -0.445  -0.340   -0.228    -0.109    -0.047   -0.777   -0.040

all negative, with Sigma's own cell at -0.723.  Sigma sits at (beta, pi/2-beta) with
beta < pi/2-beta, so it lies in the family, and the class of competitors covered is
STRICTLY LARGER than D and checkable from the sign pattern alone.

The restriction to ANCHORED intervals is essential: the unanchored E1 = E2 = [0.4,1.2] has
lambda_max = +0.407, which is what killed the earlier "tau1 <= tau2 suffices" claim.

### 🔴 Item 1 NOT delivered: the constant gap is identified, not closed

The proof gives 0.3710 on L^2(0,pi/2); the measured sharp value is 0.7285 on L^2(0,pi).
The factor is exactly the J3 coefficient the concavity proof DISCARDS: P3 = 1 makes
int_{pi/2}^pi (eta^2 - eta'^2) <= 0 only marginally, and recovering a positive coefficient
there requires spending the E2 term on [pi/2,pi] instead of on J1 and J2.  Sketched, not
carried out.  The note says so.

### 🔴 Item 2 NOT delivered: the H^1 estimate could not be confirmed, and my reasoning
###    for expecting it was too quick

The coefficient of eta'(theta)^2 in (Q2) is -1 or -2 throughout, so an H^1 estimate SHOULD
exist.  It could not be confirmed.  Testing (1/2)d^2Q + c1*K against the mass matrix gives
values that GROW with the mesh (+667 at m=64, +2669 at m=128 for c1 = 1) instead of
converging, and c0 turns non-positive already near c1 = 0.03.

The reason is a delicate cancellation the basis cannot hold: the sigma term contains
-2 int eta eta' tan t, which integrates by parts against eta(pi/2) = 0 into
+ int eta^2 sec^2 t, so two unbounded quantities cancel near theta = pi/2.  In exact
arithmetic that is fine; in the piecewise-linear basis it is not.  So the DISCRETISATION
fails, not necessarily the claim -- but the claim is unconfirmed and is recorded as open.

Recorded as a caution: "the principal symbol is negative, therefore the form dominates the
stiffness" is exactly the kind of step that skips a cross term.  It did.

## 🔥🔥🔥 TWO NEW POSITIVE THEOREMS, FREE FROM WHAT WAS ALREADY PROVED

Strict concavity had been proved and never cashed.  Q is EXACTLY quadratic on the cell, so

    Q(H_Sigma + eta) = Q(Sigma) + dQ(Sigma)[eta] + (1/2) d^2Q[eta]

exactly, with no remainder.  dQ(Sigma) = 0 and Q(Sigma) = A_R* are proved, and the Garding
chain gives (1/2) d^2Q[eta] <= -1.6013 J1 - 0.3710 J2.  Hence:

  THEOREM (STABILITY).  For every ambidextrous moving sofa T whose cap data
  H = H_Sigma + eta lies in D,

      |T|  <=  A_R*  -  0.3710 ||eta||^2_{L^2(0,pi/2)} .

  COROLLARY (UNIQUENESS).  Sigma is the UNIQUE ambidextrous moving sofa of area A_R* with
  cap data in D; every other one loses area by the quadratic amount above.

Uniqueness: equality forces eta = 0 on [0,pi/2]; and with eta = 0 there the E2 term of the
second variation contributes -int_0^{pi/2-beta} eta'(t+pi/2)^2 dt, negative unless eta is
constant on [pi/2,pi], and eta(pi/2) = 0 makes that constant zero.

The constant 0.3710 is the one the concavity proof delivers.  Measured, the sharp constant
against the L^2(0,pi) norm is larger: sup (1/2)d^2Q/||eta||^2 = -0.7059, -0.7188, -0.7255,
-0.7285 at m = 32, 64, 128, 256.

Neither result needed a new argument -- only assembly.  Both are PROVED.

## ITEM 2 (task #21): TIME-BOXED AND STOPPED, with the structure identified

Literature search for the doubly-covered area of a tangent-segment sweep turned up
envelope/caustic theory but no usable formula.  Deriving instead: the flux
(1/2) int alpha_2^2 IS the signed area of the closed curve formed by the corner path, the
envelope and the two end segments; the swept area is the area of its image.  For a closed
curve with a self-intersection,

    signed area  -  image area  =  the area of the doubly-wound LOBE.

So the excess is a lobe area -- which is exactly the Mode-2 / signed-Green phenomenon this
project identified years ago in the second-variation line, reappearing.  Lobe areas are not
concave functionals of H in any obvious way, so the route needs an idea rather than a
search.  Stopped there per Rule 2 rather than grinding.

## ITEM 3: the abstract now states the independence of (c)

One clause, not a paragraph: "The separation inequality is independent of (RC) and cannot
be removed."  The abstract otherwise leads with the positive results -- the niche formula,
(RC) implies injectivity, Q(Sigma) = A_R*, dQ = 0, d^2 Q < 0, and now the stability bound
and uniqueness -- with the two limits in a final short paragraph.

## HYPOTHESIS (c) IS INDEPENDENT OF (RC) -- FALSIFIED, NOT PROVED (item 2)

Rule 3 first, and it paid.  Add to H the function delta*sin(theta - pi/2) on [pi/2,pi],
zero on [0,pi/2].  Then H + H'' of the addition is IDENTICALLY ZERO, so (RC) is preserved
exactly; H(0) and H(pi/2) are unchanged, so the gauge is preserved; H' gains delta at
pi/2, so the ceiling facet grows; and G(t) = H(t+pi/2) gains delta*sin t, so c_y gains
delta*sin t*cos t, maximal delta/2 at t = pi/4.  Measured:

    delta     0.0000   0.1000   0.2243   0.3000   0.5000
    density   0.83863  0.83863  0.83863  0.83863  0.83863   (RC) holds throughout
    facet     1.1670   1.2670   1.3913   1.4670   1.6670
    M         0.38784  0.43784  0.49999  0.53784  0.63784   crosses 1/2 at delta ~ 0.2243

So (c) CANNOT be derived from (RC) and the gauge, and must remain a hypothesis.

This also RETRACTS the suggestion in the previous commit that "(c) never binds" was
evidence of an implication.  It never binds among SMALL perturbations of Sigma, which is a
statement about the probe, not about the geometry.

## ITEM 3: WIDENING D NEEDS A CONCAVE BOUND ON THE EXCESS, NOT A WEAKER CONSTANT

How badly does the bound degrade past (RC)?  Comparing the flux V_2 = (1/2) int (a2^+)^2
with the area |W_2| actually swept:

    max density   0.838    0.976    1.004    1.047    1.119    1.267
    excess       4.4e-08  4.3e-08  4.3e-08  5.4e-07  9.5e-06  7.4e-05
    relative      0.0000%  0.0000%  0.0000%  0.0003%  0.0056%  0.0424%

Below 1 the excess sits at the quad-discretisation floor.  Past 1 it is the area
double-counted by the flux -- and it is TINY: 0.04% even at density 1.27.  Gerver's own
excess is V - |N| ~ 0.0016, about 0.25%.

NUANCE, and it corrects the previous commit.  (RC) is sharp for INJECTIVITY -- violations
appear at density 1.004 -- but the architecture degrades GRACEFULLY: those first violating
pairs cover essentially no area.  So "Gerver is outside for real reasons" is true of the
condition and misleading about the magnitude; the quantitative failure there is 0.25%.

WHY A WEAKER CONSTANT STILL DOES NOT WORK.  To widen D one needs V minus an upper bound on
the excess to remain a LOWER bound for |N|, and for Q to stay concave that upper bound must
be CONCAVE in H.  The size of the excess is not the obstruction; its shape is.  Two routes
were checked and rejected:

  (a) TRUNCATE the sweep at lambda(t) = inf_{t'} s22(t,t'), which is exactly the largest
      injective length.  s22 is affine in H, so the infimum is CONCAVE in H, and
      (1/2)lambda^2 of a concave function is neither convex nor concave: the Mamikon
      convexity that the whole architecture rests on is lost.
  (b) Use the FIRST-CAPTURE decomposition, which is exact and injective by construction.
      But once the sweep self-intersects its parameter domain is no longer of the form
      0 <= s <= alpha_2, so its area is not a Mamikon integral and is not quadratic in H.

Logged as dead ends with reasons (Rule 2).  A third route -- bounding the excess directly
by something concave -- is not attempted and is the open direction.

## ITEM 4: algorithm/README.md reframed

It described the directory as "a concrete computational pivot away from the structural
manuscript work", framing from the withdrawn line.  Now states plainly that the current
paper is the ambidextrous note, that the ambi_*.py scripts regenerate everything it cites,
and that the gerver_*/sigma_* scripts belong to the refuted line and support no current
claim.

## THE THEOREM IS C^2-LOCAL; AN INTEGRITY CHECK THAT FOUND THREE STALE FILES; LEAN F24

### 🔴 D IS A C^2-BALL, SO THE MAIN THEOREM IS A C^2-LOCAL STATEMENT (item 3)

Radius of D along H_Sigma + eps sin(2k theta):

    k          2        4        6        8       10
    eps_k   0.0864   0.0117   0.0047   0.0036   0.0021
    eps_k k^2 0.346    0.187    0.170    0.231    0.210

eps_k k^2 stays between 0.17 and 0.35, so the radius scales like 1/k^2.  D contains a ball
in the C^2 norm and in NO WEAKER ONE -- exactly what a bound on H'' should give.  It is a
genuine ball rather than a sliver: of 60 random eight-mode perturbations with coefficients
of size 0.02/k^2, 51 land inside (5/60 at 0.05, 0/60 at 0.10).

SO THEOREM thm:final IS A C^2-LOCAL STATEMENT, with explicit convex hypotheses in place of
a neighbourhood of unspecified size.  That is weaker than the phrase "an explicit convex
class containing Sigma with room around it" suggested in the previous commit, and the note
now says so.

In EVERY probe the binding constraint was (RC); condition (c), c_y <= 1/2, NEVER became
active.  Consistent with (c) being implied by (RC) near Sigma -- which the retracted
M <= H'(0) attempt tried and failed to prove.

D does not reach Gerver, and since (RC) is sharp no relaxation of the constant can make it.

### 🔴 AN INTEGRITY CHECK, AND IT FOUND THREE STALE FILES ON ITS FIRST RUN (item 2)

private/tools/check_sync.sh compares every file the release repo tracks against its source
counterpart and exits nonzero on divergence.  First run:

  * algorithm/README.md -- the RELEASE copy still advertised the WITHDRAWN paper by title,
    "It supports the numerical experiments in the companion paper *Strict local maximality
    of Gerver's sofa*".  The source had been corrected; the release had not.
  * algorithm/rigorous/romik_hessian.py -- release 8 lines BEHIND source: missing the
    corrected defaults (n_modes 6 -> 16, epsilon -> 1e-5) and the whole NOTE explaining why
    the step size must not be coarsened.  A shipped module that other shipped scripts
    import.
  * algorithm/rigorous/sigma_hessian_released.py -- release had the old checkpoint filename
    without the epsilon exponent.

In all three the SOURCE was authoritative, so the direction discipline held; what failed
was that nobody checked.  Synced, re-run clean.  Eight release-only files (the withdrawn
work kept deliberately, plus release metadata) are now whitelisted so that any NEW
release-only file stands out.

This is the fourth defect in this project traced to sync drift.  The check is now a
one-command gate and should be run before every push.

### 🟢 LEAN F24 (item 4)

  support_point_at_pi    at theta = pi, (C,S) = (-1,0), the boundary point is (-H,-D)
  support_point_at_zero  at theta = 0, it is (H,D)
  boundary_chain         F24a + rho_fixed_height + boundary_term_vanishes composed: the
                         height at pi is -D, rho-fixedness gives D = -1, and the
                         coefficient 2H'(pi)+1 vanishes

89 theorems, 14 defs, zero sorry, axioms [propext, Quot.sound].

NOT formalizable in core Lean, and now stated as such in MAPPING.md: the parametrisation
p(theta) = H mu_theta + H' nu_theta of the boundary point, and the uniqueness of the
extreme point.  Both are geometry, not Int arithmetic.

## ITEMS 2-4: (RC) IS SHARP; LEAN F23; AND THE MAPPING AUDIT FOUND REAL GAPS

### 🟢 (RC) IS SHARP -- D CANNOT BE WIDENED THERE (item 4)

The constant 1 in the forcing R = 1 - (G+G'') is the CORRIDOR WIDTH: it traces to
c(t) = (F-1) mu_t + (G-1) nu_t, hence <c(t),nu_t'> = n + G - 1 and n'' = -n + 1 - (G+G'').
So the proof cannot tolerate density > 1.  The question was whether INJECTIVITY itself
survives past 1.  It does not.  With exact derivatives, H = H_Sigma + eps sin(k theta):

    max density   0.838  0.921  0.976  1.004  1.047  1.119    (k=4)
    face-2 viols      0      0      0    160   1510   3086
    max density   0.976  1.045  1.114                          (k=6)
    face-2 viols      0    200    526

Face-2 injectivity dies exactly as the density crosses 1.  So (RC) is not merely
sufficient: the constant is forced, and GERVER'S CAP (density 1.3986) IS OUTSIDE THE
DOMAIN FOR REAL REASONS, not by an artefact of the proof.  D cannot be widened this way.

A BUG CAUGHT EN ROUTE: the first version of this experiment computed dF, dG by central
differences on a CLAMPED H, which corrupts the derivative at the ends of [0,pi] and
[pi/2,pi].  It reported 596 face-1 violations for SIGMA -- contradicting the exact
computation's 0.  Redone with exact derivatives: 0/0 for Sigma, and the face-1 column is
identically 0 throughout.  The face-2 signal above is from the corrected run.

### 🟢 LEAN F23: the boundary term (item 2)

  rho_fixed_height       in doubled units (reflection y -> 2-y) a fixed height is 1
  boundary_term_vanishes leftmost point has height -H'(pi); rho-fixed forces H'(pi) = -1/2,
                         so the coefficient 2H'(pi)+1 of eta(pi) vanishes
  right_extreme_height   the same at theta = 0 gives H'(0) = 1/2
  extremes_same_height   both extreme points of the cap sit at the same height

86 theorems, 14 defs, zero sorry, axioms [propext, Quot.sound].

### 🔴 THE MAPPING AUDIT FOUND REAL GAPS (item 3)

Rule 5 requires a complete paper-to-Lean table.  It was NOT complete.

  1. F14, F15, F16 had NO rows at all -- 12 substantive theorems unmapped, including the
     two cone-membership lemmas and the whole Cardano chain.  The F16 section had been
     WRITTEN in an earlier session and was LOST, almost certainly to the same
     release->source copy that destroyed the note patches.  Added.
  2. F23 (just added) had no rows.  Added.
  3. The Classical.choice claim was STALE.  Checked properly this time, by running
     #print axioms over EVERY theorem in the file rather than by inspection: exactly TWO
     declarations use it, strip_covers_iff AND cone_nu_iff.  The header had named only the
     first.  This is the THIRD version of that sentence: the first claimed none anywhere,
     the second named only strip_covers_iff.  Corrected, with the history recorded.
  4. The table's Line column has rotted as the file grew; marked indicative.
  5. 15 definitions and one-line helpers are now explicitly declared as deliberately
     unmapped, so "unmapped" no longer hides anything.

RE-AUDIT AFTER THE FIX: 86 theorems, 0 unmapped that are not declared helpers.

## RULE 6 ADVERSARIAL REVIEW OF THE ASSEMBLED NOTE, plus release preparation

### The DAG is acyclic

60 environments, 28 with proofs.  Two forward references, BOTH from remarks and neither
inside a proof: rem:conc -> prop:reynolds and rem:rcclassical -> thm:rc/thm:cross.  Those
are pointers, not dependencies.  No proof cites a later result.

### 🔴 FINDING 1: the BOUNDARY TERM of dQ was never checked

d|C2| = 2 int_0^pi (H eta - H' eta') dtheta - eta(0) - eta(pi).  Integrating the eta' by
parts and using eta(0) = 0 leaves, BESIDES the pointwise Euler-Lagrange equations,

    -(2 H'(pi) + 1) eta(pi).

Theorem thm:el proved only the pointwise equations, so dQ(Sigma) = 0 was NOT established.

It does hold.  dV contributes no boundary term at theta = pi: its only one there carries
the factor alpha_2^+(pi/2), and alpha_2(pi/2) = -0.5 < 0, so the clamp kills it; every
other boundary sits at theta = 0 or pi/2 where eta vanishes.  And H'(pi) = -1/2 exactly
(measured -0.499999998666, error 1.3e-9 at the finite-difference floor).

WHY, structurally: the boundary point of C2 with outer normal mu_pi = (-1,0) is
H(pi) mu_pi + H'(pi) nu_pi = (-H(pi), -H'(pi)), so its height is -H'(pi); C2 is
rho-symmetric about y = 1/2, so its leftmost point is rho-fixed when unique, forcing
H'(pi) = -1/2.  The same mechanism at theta = 0 gives H'(0) = 1/2.  BOTH EXTREME POINTS OF
THE CAP SIT AT HEIGHT 1/2 -- they are the two rho-fixed points, (1, 1/2) and
(-1.334100, 1/2).  So the gap was in the WRITE-UP, not the result.  Fixed.

### 🔴 FINDING 2: main theorem used M <= 1/2 against a corollary needing M < 1/2

Hypothesis (c) is c_y <= 1/2, but cor:sep is stated for M < 1/2 (strict) and concludes
U ^ rho U = EMPTY.  With M = 1/2 the two niches can share the line y = 1/2.  That is a null
set, so |U ^ rho U| = 0 and the area bound is unaffected -- but the proof cited the strict
corollary.  Fixed by arguing the null-set form directly from lem:ceiling and noting that
Sigma satisfies the strict form anyway.

### 🔴 FINDING 3: the covering hypothesis was cited to the wrong result

thm:final cited prop:V for V = |N|, but prop:V ASSUMES covering, disjointness and
injectivity.  The covering and containment arguments live in the proof of prop:convex.
Fixed: thm:final now cites prop:convex.

### 🔴 PROCESS ERROR, caught by verification

While syncing I ran a RELEASE -> SOURCE copy of note.tex, which overwrote the freshly
patched source with the stale release copy and silently destroyed all three fixes.  Caught
by grepping for the patch markers instead of assuming the edit had stuck; redone
source -> release only.  STANDING RULE: never copy release -> source.

### Release preparation

  * CITATION.cff version 0.5.0 -> 0.6.0, date 2026-07-30.
  * paper/manuscript.tex, OFFDIAG_RIGOROUS.tex and UNIQUENESS.tex each get a WITHDRAWN
    header, and manuscript.tex a boxed notice after \maketitle, so a reader who opens them
    cannot be misled.  They are KEPT because the archived release 0.4.0 contained them and
    PROGRAM.md references them.
  * README layout section now states plainly which files are superseded.
  * The 52 gerver_*/sigma_* scripts and PROGRAM.md are KEPT: they are the computational
    record behind the retractions, and PROGRAM.md is advertised by the README as exactly
    that.  Rule 11's ban on narration is aimed at strategy leakage, not at a deliberate
    public ledger.

## 🔴 RULE 4: (RC) IS NOT NEW. It is the classical sliding-ball condition, relaxed.

The audit gap is closed, and it forces a reframing.

### What (RC) actually is

The dual of Blaschke's rolling theorem: a convex body K SLIDES FREELY INSIDE A BALL of
radius R exactly when h_K + h_K'' <= R, equivalently when K is a MINKOWSKI SUMMAND of RB.
(Schneider, Convex Bodies: The Brunn-Minkowski Theory, 2nd ed., section 3.2.)  Our (RC) is
that condition at R = 1, the corridor width, RELAXED to permit atoms at theta = +- pi/2.

Since Minkowski addition ADDS surface area measures, and a body whose surface measure is
two equal atoms at +-pi/2 is a horizontal SEGMENT,

    (RC)  <=>  C2 = [a horizontal segment] (+) D,  D a Minkowski summand of the unit disc.

MEASURED: sigma_{C2} for Sigma has exactly ONE atom in [0,pi], at theta = pi/2, of mass
1.167048 (the corridor facet), and a.c. density at most 0.8389.  So Sigma's cap is a
corridor facet plus a body of curvature radius <= 0.8389, which slides freely in the unit
disc.

SO (RC) IS NOT A NEW CONDITION.  What is claimed is its USE: that it forces the niche
sweep to be injective.  The note, README and abstract are corrected accordingly, and
Schneider is cited.

### The Gerver failure, now classical (item 2)

Gerver's cap also has exactly one atom in [0,pi] at theta = pi/2, of mass 1.613762, but its
a.c. density reaches 1.3986 > 1.  So

    GERVER'S CAP IS NOT A SEGMENT (+) (SUMMAND OF THE UNIT DISC): part of its boundary is
    FLATTER THAN THE CORRIDOR IS WIDE.  Sigma's is not.

That is the one-line classical statement of the difference found last session, and it
replaces the descriptive "Sigma has vertices, Gerver does not" with a standard notion.

### What survives as ours

  * the niche formula in convex-linear data, and its bookkeeping (subtract from the cap,
    single support function H) -- different from Baek's (attach to R, triples (K,B,D)),
    equivalence not determined;
  * (RC) => injectivity, by the forced-oscillator argument;
  * V >= |N| always (Reynolds), hence Q bounds nothing off the injective domain;
  * the main theorem on the convex domain D;
  * dQ = 0 identically in the constants, i.e. Romik's ODEs ARE the critical-point
    equations of Q;
  * the closed forms for Sigma's cap, and A_R* = 1 + 4 tan^2 beta + beta;
  * the negative result that the construction does not recover Gerver, now with a
    classical explanation.

NOT ours: the arm lengths f, g (Baek Def 6.2.1); the cubics (standard); (RC) as a
condition (classical); radius of curvature = surface-measure density (standard).

## RULE 4 NOVELTY AUDIT (item 1), HYPOTHESIS (iii) RESOLVED AS A DOMAIN CONSTRAINT (item 2),
## AND THE MAIN THEOREM STATED (item 3)

### The audit, against Baek's full text (pdftotext of arXiv:2411.19826)

  * ARM LENGTHS f, g ARE BAEK'S (his Definition 6.2.1), via the contact points A and C.
    Our alpha_1, alpha_2 are those shifted by the corridor width.  CITE, do not claim.
  * HIS INJECTIVITY CONDITION (Definition 6.1.2) has three parts.  Part (1): sigma_K is
    absolutely continuous on [0,pi/2) and on (pi/2,pi], i.e. an atom is allowed ONLY at
    theta = pi/2.  Part (3): x'_K(t).u_t < 0 and x'_K(t).v_t > 0 on (0,pi/2).  This
    confirms the record in this ledger verbatim.
  * (RC) DOES NOT APPEAR IN BAEK.  It shares part (1) exactly and ADDS a bound on the
    density, while dropping part (3).  The paper's only mentions of curvature (lines
    948-949, 1698 of the extracted text) are the standard identification of the
    surface-measure density with the radius of curvature, which we also use and which is
    not ours.
  * ARCHITECTURE DIFFERS IN BOOKKEEPING.  He ATTACHES Mamikon regions to the
    overestimating region so the total is LINEAR in the cap; we SUBTRACT them from the
    cap.  He works on a space L of TRIPLES (K,B,D) of convex bodies; we use the single
    support function H on [0,pi].  Whether the two are equivalent is NOT determined.
  * THE AMBIDEXTROUS PROBLEM IS NOT TREATED by Baek, and no upper bound for it was found
    in the literature.  Kallus-Romik's 2.37 is the one-corner bound; Baek's conditional
    paper gives 1 + pi^2/8 = 2.2337 under injectivity.
  * SCOPE OF THE AUDIT: Baek and the Kallus-Romik line only, NOT the wider literature.

### Hypothesis (iii): it is a LINEAR constraint, so it belongs in the domain (item 2)

c_y(t) = (H(t)-1) sin t + (H(t+pi/2)-1) cos t is AFFINE in H, so {c_y <= 1/2} is an
intersection of half-spaces: CONVEX.  It does not have to be derived; it can be part of the
domain exactly as (RC) and the sign cell are.  After the retraction of the M <= H'(0)
attempt there is no derivation, and stating it as a hypothesis is the honest move.

Sigma satisfies it with margin 1/2 - M = 0.112161871.

### THE MAIN THEOREM (item 3)

  Let D be the set of support functions H on [0,pi] of admissible caps with
    (a) H(0) = H(pi/2) = 1                     the gauge
    (b) (RC): sigma_K a.c. on [0,pi/2) and (pi/2,pi] with density <= 1, atom only at pi/2
    (c) c_y(t) <= 1/2 on [0,pi/2]
    (d) alpha_1 < 0 exactly on [0,beta), alpha_2 > 0 exactly on [0,pi/2-beta)
  Then D is CONVEX, Sigma is in D, and |T| <= A_R* for every ambidextrous moving sofa T
  whose cap data lies in D.

PROOF.  (a)-(d) are affine in H so D is convex.  (b) gives injectivity, so V = |N|.  (c)
gives disjoint niches, so |T| <= |C2| - 2|N| = Q.  (d) gives d^2 Q <= 0; criticality gives
dQ(Sigma) = 0; concave + critical on a convex set gives Q(H) <= Q(Sigma) = A_R*.  QED

EFFECTIVE LABEL: PROVED.  Every hypothesis is either proved or an explicit convex
constraint; nothing is assumed without being stated.

D HAS INTERIOR: H + eps sin(k theta) stays in D for k = 2, 4 and |eps| <= 1e-2, both signs,
with (RC) margin falling from 0.161 to 0.024 and the c_y margin essentially unchanged.

### What the theorem is NOT

D is not shown to contain every competitor, and GERVER'S CAP VIOLATES (b) -- concrete
reason for doubt about how much of the problem D covers.  Condition (c) is a hypothesis,
not a consequence; the attempt to derive it failed and is recorded as such.  Optimality of
Sigma remains OPEN.

### Paper restructured

Abstract rewritten to the final structure; a "Relation to prior work" section added with
the audit above; the main theorem and its limitations stated; a bibliography added
(Baek 2024, Gerver 1992, Kallus-Romik 2018, Romik 2018).  24 pages.

## ITEMS 1-3: ONE STRUCTURAL EXPLANATION, ONE RETRACTION, ONE LEAN BLOCK

### 🔴 RETRACTION: the bound M <= H'(0) is FALSE

Attempted for hypothesis (iii).  Solving H'' + H = W with H(0) = 1 gives
H(theta) = cos th + H'(0) sin th + int_0^th sin(th-s) W ds, and substituting into
c_y(t) = (H(t)-1) sin t + (H(t+pi/2)-1) cos t gives

    c_y(t) = H'(0) - sin t - cos t + sin t int_0^t sin(t-s) W ds
                                   + cos t int_0^{t+pi/2} cos(t-s) W ds .

Both kernels are >= 0 on their ranges (|t-s| <= pi/2), so "W <= 1" would give
c_y <= H'(0); and for a rho-symmetric cap h2'(0+) = H'(0), h2'(0-) = 1 - H'(0), so the
atom at theta = 0 has mass 2H'(0) - 1 = the length of the vertical right edge, forcing
H'(0) >= 1/2, and apparently M <= 1/2 whenever that edge is absent.

THE ERROR: W is NOT <= 1 as a measure.  It carries the CEILING ATOM of mass 1.1670498 at
s = pi/2, and here that atom meets the kernel cos(t - pi/2) = sin t, which does not
vanish.  Corrected, M <= H'(0) + (1/2)(1.1670) = 1.083 -- useless against the required
1/2.  RETRACTED.

THIS DOES NOT AFFECT THE INJECTIVITY THEOREM, and I checked: there R(u) = 1 - (G+G'')(t-u)
has its atom at u = t, which is OUTSIDE [0,tau] when tau < t and is the endpoint where the
kernel sin(tau-u) VANISHES when tau = t; the face-1 atom needs u = t - pi/2 <= 0.  The
placement of the atom relative to the kernel is exactly what separates the two arguments.

### The I11 tension, explained but not removed (item 1)

The MIRROR decomposition (inner face 1 + outer face 2, reach sigma_2 = c_y/sin t) gives
Gerver 0.642614486 -- IDENTICAL to the forward one, because Gerver's path is symmetric
under t -> pi/2-t.  Both exceed |N| ~ 0.641.  So the failure is not an artefact of
orientation.

THE STRUCTURAL REASON.  Sigma's cap has H+H'' = 0 on [0,beta) and (pi-beta,pi] -- genuine
VERTICES -- because Sigma's outer phases have CONSTANT contact arcs pinned at (1,1/2).
Gerver's cap has no such vertices, and there H+H'' reaches 1.3960 near theta = pi.  So THE
VERY DEGENERACY THAT MADE SIGMA HARD FOR LOCAL ANALYSIS IS WHAT MAKES (RC) HOLD FOR IT.
The framework exploits Sigma's degeneracy rather than being general; that explains the I11
failure without removing it.

### 🟢 LEAN F22 (item 3)

  sq_add_int, sq_sub_int    (x+-y)^2 expansions with x, y as atoms
  lagrange_identity         (a^2+b^2)(c^2+s^2) - (ac+bs)^2 = (as-bc)^2
  rc_block                  c^2+s^2 = 1 and 9(a^2+b^2) <= 16  =>  9(ac+bs)^2 <= 16

rc_block is (RC) on the half-angle blocks: the bound follows from the COEFFICIENTS alone,
with no information about t, which is why (RC) for Sigma reduces to
f1^2 (4-2sqrt2) <= 16/9.  82 theorems, 14 defs, zero sorry, axioms [propext, Quot.sound].

## 🎆 Q(Sigma) = A_R* IS PROVED (structurally), AND (RC) HOLDS FOR SIGMA IN CLOSED FORM
## 🌊 BUT THE CONSTRUCTION DOES NOT RECOVER GERVER

### (RC) for Sigma, in closed form (item 1)

The surface-measure density block by block:

    H + H'' = 0                                    theta in [0,beta) and (pi-beta,pi]
            = 1/2                                  theta in (pi/2-beta,pi/2) and (pi/2,pi/2+beta)
            = (3K/4) cos(theta/2 + pi/8)           theta in [beta, pi/2-beta]
            = (3K/4) sin((theta-pi/2)/2 + pi/8)    theta in [pi/2+beta, pi-beta]

with K = f1 sqrt(4-2sqrt2) = 1.3020516916 -- the SAME K as in the W formula.  Both
non-constant blocks have amplitude (3/4)K because f2 = (1-sqrt2)f1 gives
sqrt(f1^2+f2^2) = f1 sqrt(4-2sqrt2), and phase pi/8 because -f2/f1 = sqrt2-1 = tan(pi/8).
On [beta,pi/2-beta] the argument runs over [0.5375,1.0333] inside [0,pi/2] where cosine
decreases, so

    max a.c. (H+H'') = (3K/4) cos(beta/2 + pi/8) = 0.83882534940 < 1,   margin 0.16117

matching the measured 0.838568.  Already the AMPLITUDE is below 1, so (RC) holds as soon as

    f1^2 <= 16/(9(4-2sqrt2)) = 1.5174...,   against f1^2 = 1.4470...

That criterion is STRICTLY STRONGER than the separation criterion f1^2 < (2+sqrt2)/2 =
1.7071 of the main theorem: within the family in which f1 is the free parameter,
(RC) implies M < 1/2.

### Q(Sigma) = A_R*, PROVED WITHOUT EVALUATING AN INTEGRAL

Sigma satisfies (RC), so V(Sigma) = |N(Sigma)| by the injectivity theorems.  The niches
are disjoint (M < 1/2) and C2 is rho-invariant, so |Sigma| = |C2| - |N| - |rho N| =
|C2| - 2|N|.  Hence

    Q(Sigma) = |C2| - 2V(Sigma) = |C2| - 2|N| = |Sigma| = A_R*.

The symbolic integration that timed out was never needed.  The 51-digit agreement stands
as a consistency check on the chain rather than as its proof.

HYPOTHESIS (i) IS NOW ENTIRELY PROVED: Q(Sigma) = A_R*, dQ(Sigma) = 0, d^2 Q <= 0.

### 🌊🌊 RULE I11 REGRESSION: THE CONSTRUCTION FAILS ON THE SOLVED CASE

Applying the same machinery to Gerver's rotation path:

  * Gerver satisfies the ONE-CORNER injectivity condition everywhere: alpha_1 > 0 and
    alpha_2 > 0 on 100% of [0,pi/2].
  * (RC) FAILS for Gerver: max a.c. H+H'' = 1.3960 near theta = pi, margin -0.396.
  * Gerver's FACE-2 SWEEP IS NOT INJECTIVE in this decomposition: 33002 of 158802 tested
    pairs meet interior to both segments; min(s22 - alpha_2) = -0.0944.  The face-1 sweep
    is injective.
  * Consistently V(Gerver) = 0.642614626 > |N| = 0.6406 (n=481) to 0.6412 (n=721), i.e.
    V > |N| exactly as the Reynolds proposition requires.

So (RC) and the one-corner injectivity condition are INDEPENDENT: Sigma satisfies the
first and not the second; Gerver the second and not the first.  The decomposition
N = W2 (+) W1out is therefore NOT the one Baek's argument uses.

I11 says the framework must recover the known special cases before it is trusted
elsewhere.  It does not.  This is recorded as a TENSION, not explained.  Nothing proved
above is contradicted -- the Gerver numbers satisfy every inequality the framework
asserts -- but the construction's scope is narrower than the problem, and (RC) is a
substantive restriction rather than a technicality.

### Hypothesis (iii): still open (item 2)

Over 250 random perturbations H + sum_{k<=3} c_k sin(2k theta) with |c_k| <= a/k^2 for
a = 0.02, 0.05, 0.10, every H satisfying (RC) had M <= 0.3976 against the required
M < 1/2, and the (RC)-satisfying fraction fell from 250/250 to 34/250 as a grew.  No
counterexample, no implication.

### Status

    (i)   Q(Sigma) = A_R*                    PROVED   <-- this session
          dQ(Sigma) = 0                      PROVED
          d^2 Q <= 0 on C                    PROVED
    (ii)  the three injectivity conditions   PROVED from (RC); (RC) PROVED for Sigma
    (iii) M < 1/2 for competitors            OPEN
    I11   recovery of the one-corner case    FAILS

Optimality of Sigma remains OPEN, and the I11 failure is the more serious of the two gaps.

## 🎆🎆🎆 CONCAVITY PROVED. THE CONDITIONAL THEOREM NOW RESTS ON ONE NUMERICAL IDENTITY.

### d^2 Q <= 0 IS PROVED (item 1)

On [0,beta) retain a fraction delta of -int eta'^2 and apply the completion identity to the
rest; completing the square in p = eta'(t) and discarding the negative square,

    -(1-delta)p^2 - (qT+p)^2 + (r-p)^2 <= A q^2 T^2 + B r^2,
    A = (1+kappa)/(1-delta) - 1,   B = (1+1/kappa)/(1-delta) + 1,

using (qT+r)^2 <= (1+kappa)q^2T^2 + (1+1/kappa)r^2 and T = tan t <= tan beta on [0,beta).
Poincare constants for eta(0) = eta(pi/2) = 0, each with one Dirichlet and one free end:

    P1 = (pi/2beta)^2        = 29.4135   on [0,beta]
    P2 = (pi/2(pi/2-beta))^2 =  1.5035   on [beta,pi/2]
    P3 = 1                   =  1.0000   on [pi/2,pi]

and -(eta(t)+eta'(t+pi/2))^2 <= -lambda eta'(t+pi/2)^2 + (lambda/(1-lambda)) eta(t)^2 turns
the E2 term into -lambda int_{pi/2}^{pi-beta} eta'^2 + (lambda/(1-lambda))(J1+J2), while
eta(pi/2) = 0 gives int_{pi/2}^{pi/2+beta} eta^2 <= (beta^2/2) int eta'^2, so the B r^2
remainder is absorbed once lambda >= B beta^2/2.  Collecting,

    coef J1 = A tan^2 beta - delta P1 + 1 + lambda/(1-lambda)
    coef J2 = 1 - P2 + lambda/(1-lambda)
    coef J3 = 1 - P3 = 0
    coef int_{pi/2}^{pi-beta} eta'^2 = B beta^2/2 - lambda

At delta = 1/10, kappa = 2, lambda = 0.117 these are -1.6013, -0.3710, 0, -0.005:

    (1/2) d^2 Q <= -1.6013 J1 - 0.3710 J2 + 0 J3 - 0.005 int_{pi/2}^{pi-beta} eta'^2

so d^2 Q <= 0.  STRICTNESS: equality forces eta = 0 on [0,pi/2] AND eta the first
Dirichlet-Neumann mode on [pi/2,pi]; but with eta = 0 on [0,pi/2] the E2 term contributes
-int eta'(t+pi/2)^2 < 0.  So d^2 Q < 0 for eta != 0.  The implied constant on
L^2(0,pi/2) is 0.7419, against the measured supremum 0.7285 over L^2(0,pi): the gap is the
slack in the J3 coefficient, which P3 = 1 makes sharp.

### sigma - alpha_1 = cos(t) x'(t)  (item 2, structural)

PROVED symbolically on SOL1, SOL5, SOL6 (residual 0 each), where x = (F-1)/cos t is the
face-1 line's x-intercept.  So the middle term of V is (1/2) int cos^2 t x'^2 dt, an ENERGY
OF THE INTERCEPT PATH; and it independently recovers cos^2 t x' = 1/2 - sin t on phase 1 and
(1/2)(1 - sin t) on phase 5.

### The area identity (item 2, numerical)

Since u = 2 tan beta,  A_R* = u^2 + 1 + arctan(u/2) = 1 + 4 tan^2 beta + beta.  Using the
identity above to make every integrand elementary, at 50 working digits:

    |C2| = 2.0133416126029788281721...   (six blocks, listed in the script output)
    V    = 0.1841931970887689882517...   (0.0842064 + 0.0997315 + 0.0002553)
    Q(Sigma) - (1 + 4 tan^2 beta + beta) = -2.7e-51

A SYMBOLIC evaluation of the same integrals was attempted and DID NOT TERMINATE (10 min).
So this stays HEURISTIC, but now against a closed-form target and with a phase decomposition.

### (RC) => M < 1/2 ?  NOT REFUTED, NOT PROVED (item 3)

Rule 3 falsification over H + eps sin(k theta), k = 2,4,6 and |eps| up to 0.20: every case
satisfying (RC) has M <= 0.3895 < 1/2; the cases with M >= 1/2 (k=4, eps = +-0.15, +-0.20)
all violate (RC).  No counterexample, no implication.  Hypothesis (iii) stands untouched.

### Where the conditional theorem stands now

    (i)   Q(Sigma) = A_R*     HEURISTIC, 51 digits, closed-form target
          dQ(Sigma) = 0       PROVED
          d^2 Q <= 0 on C     PROVED   <-- this session
    (ii)  the three injectivity conditions   PROVED from (RC)
    (iii) M < 1/2 for competitors            untouched

So it rests on ONE numerical identity and ONE geometric hypothesis, rather than on four
measured conditions.  Optimality of Sigma remains OPEN.

## 🟢 LEAN F21

  second_diff_mono      non-negative second difference + equal first two terms => non-decreasing
  discrete_osc_nonneg   Phi_0 = Phi_1 = 0 and second difference >= 0 => Phi_n >= 0.  The
                        DISCRETE shadow of Phi = int sin(tau-u) R(u) du >= 0, which is the
                        step F19 could not formalize for lack of integration
  garding_sum_nonpos    a sum of (non-positive coefficient) x (non-negative quantity) is <= 0

78 theorems, 14 defs, zero sorry; axioms [propext, Quot.sound], garding_sum_nonpos needing
only propext.

## 🎆🎆 (RC) NOW PROVES ALL THREE INJECTIVITY CONDITIONS, AND dQ(Sigma) = 0 IS PROVED

Two hypotheses of the conditional theorem move to PROVED this session.

### The CROSS condition follows from (RC) too (item 1)

Work in the frame at t: p = c(t) + a mu_t + b nu_t, and <p,nu_t> = G(t)-1 forces b = 0, so
p moves along l2(t) with s2 = -a.  Then <p,mu_t'> = F(t')-1 with t' = t - tau gives

    s2 = m(t-tau)/cos tau ,      s1 = -Phi(tau) - (alpha_2(t) - s2) sin tau ,

using <mu_t, nu_{t-tau}> = sin tau and n(t-tau) = Phi(tau) + alpha_2(t) sin tau.  In the
frame at t', for t = t' - tau', the mirror computation gives

    s2 = -Psi(tau') - (s1 - alpha_1(t')) sin tau' .

Both checked against a direct 2x2 linear solve: 1.1e-16 and 3.5e-17.

  tau > 0: if p is interior to the face-2 segment then 0 < s2 < alpha_2, and Phi >= 0 by
           the (RC) theorem with sin tau >= 0 since tau <= pi/2, so s1 < 0 <= alpha_1^+:
           p is BELOW the face-1 segment.
  tau'> 0: if p is interior to the face-1 segment then s1 > alpha_1^+ >= alpha_1, so
           s2 < 0: p is OUTSIDE [0, alpha_2].
  t' = t : the lines are perpendicular and meet at c(t), where s1 = s2 = 0, interior to
           neither.

So p is never interior to both.  (RC) therefore implies ALL THREE conditions, hence the
combined sweep is injective, V = |N|, and Q >= |T| on {(RC)}.  Hypothesis (ii) of the
conditional theorem is now entirely PROVED and reduces to one linear inequality.

### dQ(Sigma) = 0 is PROVED, identically in the constants (item 2)

On each phase F-1 = Re(e^{-it} z), G-1 = Im(e^{-it} z) evaluate to

  SOL1  F-1 = cos t + (1/2) sin t - 1
        G-1 = (2a1-1) sin t + (1/2) cos t - 1/2
  SOL6  F-1 = f1 cos(t/2) + f2 sin(t/2) - 1 + k cos t + (1/2) sin t,   k = 1-(4/3)a1
        G-1 = -f2 cos(t/2) + f1 sin(t/2) - 1 + (1/2) cos t - k sin t
  SOL5  F-1 = (1-(2/3)a1) cos t + (1/2) sin t - 1/2
        G-1 = ((8/3)a1-1) sin t + (1/2) cos t - 1

(each checked against the reference path to 2.2e-16).  Substituting into
alpha_1 = G-1-F', alpha_2 = F-1+G', sigma = (F-1)tan t + G-1 and into the two EL equations,
with each region's sign pattern fixed, ALL SIX RESIDUALS ARE IDENTICALLY ZERO with
a1, f1, f2 kept as FREE SYMBOLS.  No relation among the constants is needed.

CONTROL (I12): five deliberately perturbed variants of the middle-phase equation -- sign
flip on the tan term, each of the two terms dropped, alpha_1 and alpha_2 exchanged,
H+H'' replaced by H-H'' -- all return NONZERO.  So the CAS is discriminating.

STRUCTURAL CONSEQUENCE: Romik's ODE families SOL1/SOL5/SOL6 are exactly the
critical-point equations of Q.  That is why the earlier hat-basis gradient came out at
1.8e-8.

### The Garding step (item 3): the exact cancellation, and the constant

The step that makes d^2 Q <= 0 accessible is an algebraic identity.  On [0,beta), with
p = eta'(t), q = eta(t), r = eta(t+pi/2), T = tan t, the three terms of (Q2) carrying
eta'(t) combine as

    -p^2 - (qT+p)^2 + (r-p)^2  =  -(p+qT+r)^2 + 2 r^2 + 2 q T r          (complete)

so the ADDED term is absorbed exactly and the remainder carries NO derivative of eta.
Poincare constants with eta(0) = eta(pi/2) = 0: 4 on [0,pi/2]; 1 on [pi/2,pi]
(Dirichlet-Neumann, eta(pi) free); (pi/2beta)^2 = 29.4091 on [0,beta].  Retaining a
fraction delta of -int_0^beta eta'^2 before applying (complete) and splitting (qT+r)^2
with kappa, the coefficient of int_0^beta eta^2 is

    ((1+kappa)/(1-delta) - 1) tan^2 beta + 1 - delta (pi/2beta)^2 = -1.8323 < 0
    at delta = 0.1, kappa = 1,

and the r^2 remainder (coefficient 3.2222) is absorbed by the E2 term, which supplies
-1/2 int_{pi/2}^{pi-beta} eta'^2: since eta(pi/2) = 0 gives
int_{pi/2}^{pi/2+beta} eta^2 <= (beta^2/2) int eta'^2 = 0.0420 int eta'^2, the requirement
is 3.222 * 0.0420 = 0.135 <= 1/2.  OK.  So every ingredient is in place; assembling the
chain with explicit constants is NOT done.

MEASURED CONSTANT.  sup of d^2Q[eta]/||eta||_{L2}^2 over the hat space, as a SYMMETRIC
generalized eigenproblem against the exact mass matrix (Cholesky, not Mass^{-1} M -- the
latter is not symmetric and gave garbage, +12/+34/+112, on the first attempt):

    m = 32, 64, 128, 256  ->  -0.705931, -0.718783, -0.725461, -0.728459

so c = 0.7285... and it is bounded away from 0.  HEURISTIC (discretised).

### Where the conditional theorem now stands

    (i)  Q(Sigma) = A_R*        HEURISTIC (61 digits, two independent analytic routes)
         dQ(Sigma) = 0          PROVED  <-- this session
         d^2 Q <= 0 on C        HEURISTIC (Garding ingredients assembled, constant 0.7285)
    (ii) the three injectivity conditions   PROVED from (RC)  <-- this session
    (iii) M < 1/2 for competitors           conditional (the connectedness ceiling)

## 🟢 LEAN F20

  cross_excl_face2      Phi >= 0, Sin >= 0, s2 < A2, s1 = -Phi - (A2-s2) Sin  =>  s1 <= 0
  cross_excl_face1      the mirror implication
  completion_identity   -p^2 - (qT+p)^2 + (r-p)^2 = -(p+qT+r)^2 + 2r^2 + 2qTr

75 theorems, 14 defs, zero sorry; axioms [propext, Quot.sound].

## 🎆 ONE LINEAR CURVATURE CONDITION PROVES BOTH INJECTIVITY CONDITIONS

The previous section identified K' = {V = |N|} as convex but verified it only on a grid.
It is now PROVED, from a single linear condition with a geometric reading.

    (RC)  the absolutely continuous part of H + H'' is <= 1 on [0,pi], the only atoms
          being the corridor ceiling and floor facets at theta = +- pi/2.

Equivalently: THE CAP IS NOWHERE FLATTER THAN A CIRCLE OF THE CORRIDOR'S WIDTH.  H + H''
is the radius of curvature (the surface-measure density), and H + H'' <= 1 is LINEAR in H,
so (RC) cuts out a convex set.

### THEOREM.  (RC) implies (C22) and (C11) for every pair t' < t.

PROOF.  Fix t, put tau = t - t' in (0,t], n(t') = <c(t),nu_t'> - (G(t')-1), and

    Phi(tau) = n(t-tau) - alpha_2(t) sin tau,     so (C22) reads Phi >= 0.

n(t) = 0 since <c(t),nu_t> = G-1; and n'(t') = -<c(t),mu_t'> - G'(t') equals
-(F-1) - G' = -alpha_2(t) at t' = t.  So Phi(0) = Phi'(0) = 0.  Using nu'' = -nu,

    n''(t') = -<c(t),nu_t'> - G''(t') = -(n(t') + G(t') - 1) - G''(t'),

and substituting n(t-tau) = Phi(tau) + alpha_2 sin tau, THE alpha_2 TERMS CANCEL:

    Phi'' + Phi = 1 - (G+G'')(t-tau) =: R(tau).                                    (osc)

A forced harmonic oscillator with zero initial data, so

    Phi(tau) = int_0^tau sin(tau-u) R(u) du .

tau <= t <= pi/2 < pi makes sin(tau-u) >= 0 on [0,tau], and (RC) makes R >= 0 because
G(s) = H(s+pi/2).  Hence Phi >= 0.  The ceiling atom sits at u = t: outside [0,tau] when
tau < t, and at the endpoint where the kernel VANISHES when tau = t.  So it contributes
nothing.  For (C11), m(t') = <c(t),mu_t'> - (F(t')-1) and Psi = m(t-tau) + alpha_1 sin tau
give Psi'' + Psi = 1 - (F+F'')(t-tau) by the same computation with mu'' = -mu, so
Psi >= 0; multiplying by -sin tau < 0 turns that into s11 <= alpha_1.  Its atom needs
u = t - pi/2 <= 0, reachable only at t = pi/2, where sigma(pi/2) = alpha_1(pi/2) makes the
face-1 segment EMPTY.  QED

### Verification, and the I12 control is now EXACT

Sigma: max of the AC part of H+H'' = 0.838568216 at theta = pi-beta, margin +0.161432.
Atom at pi/2: mass 1.167049816 = the ceiling facet length.  (osc) checked against direct
evaluation of n(t-tau) - alpha_2 sin tau: agreement 2.4e-5, the finite-difference floor.

TWELVE perturbations, (RC) holds exactly when (C11) holds -- no exceptions:

    perturbation                max AC H+H''   (RC)    (C11)
    H_S +-0.05 bump             2.666, 1.080   FAILS   FAILS
    H_S +-0.10 bump             4.580, 1.447   FAILS   FAILS
    H_S +-0.20 bump             8.407, 2.182   FAILS   FAILS
    H_S +- 0.03 sin(2 theta)    0.888          holds   holds
    H_S +- 0.01 sin(4 theta)    0.976          holds   holds
    H_S +- 0.03 sin(4 theta)    1.267          FAILS   FAILS

The k=4 transition is captured on BOTH sides.  The bump family fails because
exp(-1/(1-z^2)) has large second derivatives, which is exactly a curvature violation.

### Consequence for the conditional theorem

Hypothesis (ii) is replaced, for the two self-intersection conditions, by (RC): one
explicit linear inequality.  The CROSS condition (l2(t) ^ l1(t') avoiding both segments)
is NOT covered and remains measured (0 of 58081 pairs at Sigma).  So the hypothesis class
becomes {(RC)} ^ {cross} ^ C, an intersection of two convex sets with one measured
condition.

## 🔥 THE FIRST VARIATION, POINTWISE

Integrating every eta' in dQ by parts and collecting the coefficient of eta(theta):

    0 < theta < pi/2 :  H+H'' = a2^+ + (sig-a1) tan th - (sig-a1)' + (a1^-)'
    pi/2 < theta < pi:  H+H'' = -(a2^+)'(s) + a1^-(s),      s = theta - pi/2

Evaluated on Sigma at 18 values of theta spanning all six regions: max residual 9.4e-6,
the finite-difference floor.  On [0,beta) both sides are 0 (the vertex interval); on
(pi/2, pi/2+beta) both sides are 1/2 (the radius-1/2 arc).  So dQ(Sigma) = 0 now has an
explicit pointwise form; proving it means substituting SOL1/SOL5/SOL6 phase by phase, and
is not done.

## 🟢 LEAN F19

  curvature_substitution   n'' = -n + 1 - (G+G'') from <c,nu_t'> = n + G - 1
  phi_ode                  the alpha_2 cancellation: Phi'' + Phi = R
  kernel_sum_nonneg        sum of products of non-negative kernel and forcing is >= 0
                           (the Riemann-sum shadow of the integral representation)
  rc_convex                a*X + b*Y <= (a+b)*D for a,b >= 0: (RC) cuts out a convex set

72 theorems, 14 defs, zero sorry.  Axioms: [propext, Quot.sound] (kernel_sum_nonneg needs
only propext).  NOT formalized: that the integral representation solves the oscillator,
and that the facet atom contributes nothing.  Both are analysis.

## 🔥🔥🔥🔥 THE REPAIR: {V = |N|} IS CUT OUT BY LINEAR INEQUALITIES, SO IT IS CONVEX

The previous section proved V >= |N| always (Reynolds), so Q = |C2| - 2V is not an upper
bound on the full domain.  That statement stands.  What is new is that the set where it
IS an upper bound is convex and contains Sigma with room around it.

### The conditions (ambi_injectivity.py)

Each sweep lies on a line: face 2 at t on l2(t) = {<p,nu_t> = G(t)-1}, face 1 on
l1(t) = {<p,mu_t> = F(t)-1}.  Two distinct lines meet in ONE point, so a double cover
forces that point into both segments.  Solving,

    s22(t,t') = [ <c(t),nu_t'> - (G(t')-1) ] / sin(t-t')   -> alpha_2(t)  as t'->t
    s11(t,t') = [ <c(t),mu_t'> - (F(t')-1) ] / sin(t'-t)   -> alpha_1(t)  as t'->t

(the numerator vanishes at t'=t with derivative -alpha_2, resp. +alpha_1).  So nearby
face-2 lines meet at the FAR end of [0,alpha_2] and nearby face-1 lines at the NEAR end
of [alpha_1^+, sigma], and the conditions point in opposite directions:

    (C22)  <c(t),nu_t'> - (G(t')-1) >= alpha_2(t) sin(t-t')     for t' < t
    (C11)  <c(t),mu_t'> - (F(t')-1) <= alpha_1(t)^+ sin(t'-t)   for t' < t
    (C21)  l2(t) ^ l1(t') not interior to both segments

CRUCIALLY: c(t) = (F-1)mu_t + (G-1)nu_t is AFFINE in H, so <c(t),nu_t'>, G(t')-1,
alpha_1(t), alpha_2(t) are all affine and sin(t-t') is a constant.  (C22) and (C11) are
LINEAR INEQUALITIES IN H and cut out a CONVEX set K'.  On K' the combined sweep is
injective, hence V = |N| and Q >= |T|.

### Sigma is in K', with interior

Grid of 401 parameters, |i-j| >= 3:

    face-2 pairs interior to BOTH segments:  0 of 158802
    face-1 pairs interior to BOTH segments:  0 of 158802
    cross pairs interior to both:            0 of  58081

The margins vanish LINEARLY as t' -> t, which is forced -- that is the envelope limit --
and are strictly positive away from the diagonal (min gap 0.000636, 0.000957, 0.001601,
0.003235, 0.006603, 0.013769 at diagonal cutoffs 2, 3, 5, 10, 20, 40 grid steps: the
growth confirms it is a diagonal artefact, not a near-violation).

K' IS NOT A POINT.  With H = H_Sigma + eps*sin(k theta) (gauge-compatible for even k), all
conditions hold with ZERO violations at k=2 for |eps| <= 3e-2 and k=4 for |eps| <= 1e-2,
BOTH SIGNS, and the two margins trade off smoothly as an interior point should.

### The failure mechanism, identified (I12 negative control did its job)

For the compactly supported bump perturbations where V - |N| was measured positive, the
FACE-2 condition keeps holding and it is the FACE-1 condition that fails: -4.7e-2 at
eps=0.05, -1.2e-1 at 0.10, -2.3e-1 at 0.20, and face-1 self-intersection counts 4456,
3154, 1904 (and 598, 10670, 17878 for the negative side).  Bump functions have large
higher derivatives, which is exactly what creates face-1 envelope self-intersections.  So
the control both fired and localised the mechanism.

### The conditional theorem, and its honest label

  THEOREM (conditional).  Assume (i) Q(Sigma) = A_R*, dQ(Sigma) = 0, d^2 Q <= 0 on
  Sigma's sign cell C; (ii) the three conditions above hold on K' ^ C; (iii) competitors
  satisfy M < 1/2.  Then |T| <= A_R* for every ambidextrous sofa T with cap data in
  K' ^ C.

C is convex (alpha_i affine in H, so each sign condition is a half-space), K' is convex,
so the intersection is convex; concave + critical gives Q(H) <= Q(Sigma) = A_R*, and (ii)
gives Q(H) >= |T|.

EFFECTIVE LABEL: HEURISTIC.  (i) is numerical (61 digits, 1.8e-8, discretised
eigenvalues), (ii) is measured on a grid, (iii) is conditional.  The theorem does NOT
assert optimality of Sigma: K' ^ C is not shown to contain every competitor, and bodies
outside K' genuinely violate Q >= |T|.  What it does is exhibit an explicit convex class
with nonempty interior around Sigma on which the one-corner architecture transfers.

## 🟢 W > 0 CERTIFIED, SO M3 IS PROVED (ambi_wpos.py)

CORRECTION FIRST.  The previous commit wrote the middle-phase expression as
"- sqrt2 cos(2u + pi/4)".  That is WRONG: the substitution t = 2u + pi/4 makes the term
-sin t = -sin(2u + pi/4), and sqrt2 cos(2u+pi/4) = cos 2u - sin 2u is a different function
(1 instead of 1/sqrt2 at u=0).  Corrected in the note and here.  The correct form is

    W(u) = (3K/4) sin u + (K/4) cos 3u + 1/2 - sin(2u + pi/4),  K = f1 sqrt(4-2sqrt2)

on |u| <= u0 = pi/8 - beta/2 = 0.247872171290063683936069617042.

CERTIFICATE.  3u0 = 0.7436 < pi so cos 3u is unimodal with max at 0 and its min over a
subinterval is at an endpoint; sin u is increasing; 2u+pi/4 in [0.2896,1.2812] subset
[0,pi/2] so sin(2u+pi/4) is increasing.  Hence on [p,q]

    W >= L(p,q) := (3K/4) sin p + (K/4) min(cos 3p, cos 3q) + 1/2 - sin(2q + pi/4).

At 40 working digits: m = 16 gives min L = -8.6e-3 (inconclusive), m = 32 gives
min L = +6.13e-3 (CERTIFIED).  Margin exceeds the arithmetic error by 37 orders of
magnitude.  Also W(u0) = (1/2)(1 - cos beta) to 1.7e-41, matching the last phase's
(1/2)(1-sin t) as C^1 gluing requires.

So x is strictly increasing on all of [0,pi/2] and M3 (S_1 = sigma) is PROVED.

## 🔴🔴 THE ARCHITECTURE DOES NOT CLOSE: V OVER-ESTIMATES THE NICHE, SO Q IS NOT AN UPPER BOUND

The decisive test, and it is negative.  For any ambidextrous sofa T with cap data H,

    |T| <= |C2| - 2|N|,   with EQUALITY for T_max = C2 \ (U u rho U),

so Q := |C2| - 2V bounds |T| if and only if V <= |N|.  But:

    PROPOSITION.  V >= |N| for every admissible H.

PROOF.  V is exactly the flux of the ADVANCING part of dQ_t (the normal-velocity lemma
plus the Jacobian computation).  Reynolds' transport theorem gives
d|N_T|/dT <= int_{advancing} v_n ds, because advance into already-swept territory is
counted by the flux but gains no area.  Integrate over [0,pi/2].  QED

Hence Q <= |C2| - 2|N| = |T_max|, so Q is BELOW the area of the very sofa it should
bound, except where V = |N| exactly.

### Measured (ambi_domination.py): Sigma is an ISOLATED zero of V - |N|

Perturb H by a smooth bump at theta = 1.0, half-width 0.45, supported where H+H'' >= 1/2
so convexity survives.  Excess V - |N|, corrected for the oracle's known O(1/n) bias:

    eps     -0.20    -0.10    -0.05     0.05     0.10     0.20
    V-|N|  5.5e-03  1.4e-04  4.2e-06  9.3e-05  8.4e-04  5.0e-03

Strictly positive on BOTH sides, growing faster than eps^2.  So Q touches the true bound
at Sigma and falls strictly below it in every direction.

### Consequence for the previous section's results

Q(Sigma) = A_R*, dQ(Sigma) = 0 and d^2 Q < 0 on Sigma's cell are all still TRUE, and
they are still the three hypotheses of Thm 7.1.5.  They just do not compose into an
optimality statement, because the fourth ingredient -- domination -- is FALSE for this V.
The previous section said domination was "not done"; it is worse than that, it is false.
Corrected in the note (Prop "V over-estimates the niche") and the README.

### The repair, and one reformulation that may help

The repair is what Baek's Ch. 3-6 does: replace the exact flux V by the flux over a
sub-family on which the sweep is PROVABLY injective, so the integral is the area of a
genuine SUBSET of N and the inequality runs the right way, with the restriction vacuous
at Sigma.  Note that injectivity is needed not to make the integral a lower bound but to
make it EQUAL the area of a subset; int|det| >= |image| always.

REFORMULATION.  p is on the face-2 line at parameter t iff
phi(t) := <p,nu_t> - (G(t)-1) = 0, and with s(p,t) := F(t)-1-<p,mu_t> one computes

    phi' = s - alpha_2 ,     s' = -phi - alpha_1 ,

i.e. with z = s + i phi,

    z' = i z - (alpha_1 + i alpha_2),     z(t) = zeta(t) + e^{it} w_0 ,

w_0 an affine coordinate for p.  So the ENTIRE face-2 sweep is one linear ODE whose
homogeneous part is an exact rotation.  The sweep is injective iff no solution meets
{phi = 0, 0 <= s <= alpha_2} twice; at every meeting phi' = s - alpha_2 <= 0, so every
crossing is DOWNWARD, and a second meeting forces an upward crossing in between at
s >= alpha_2.  The total rotation over [0,pi/2] is only pi/2, so the homogeneous part
alone cannot supply the extra crossing.  Whether the forcing zeta can is the open point,
and it is a concrete question about one linear ODE rather than about plane geometry.

## 🟢 ITEM 2 CLOSED (to one elementary inequality): THE OUTER ARM IS MONOTONE

x(t) = c_x(t) + sigma(t) sin t = (F(t)-1)/cos t -- the X-INTERCEPT of the face-1 line
(identity verified to 2.2e-16).  So cos^2 t x' = F' cos t + (F-1) sin t, and per phase:

  [0,beta)          F = cos t + (1/2) sin t          (A(t) = P constant)
                    x = 1 + (1/2)tan t - sec t,   cos^2 t x' = 1/2 - sin t > 0
                    because sin beta = 1/(4a1) = 0.285620 < 1/2, i.e. beta < pi/6. PROVED

  (pi/2-beta,pi/2]  F-1 = A cos t + (1/2) sin t - 1/2,  A = 1 - (2/3) a1
                    x = A - (1/2) tan(pi/4 - t/2),  cos^2 t x' = (1/2)(1 - sin t) > 0.
                    PROVED.  And x(pi/2) = A = 1 - (2/3)a1 = 0.416475091724845 EXACTLY
                    the right end of the corridor floor facet -- a CLOSED FORM for it.

  [beta,pi/2-beta]  with u = t/2 - pi/8 and -f2/f1 = sqrt2 - 1 = tan(pi/8) (exact, 5.6e-17)
                    cos^2 t x' = W(u) = (3K/4) sin u + (K/4) cos 3u + 1/2
                                        - sin(2u + pi/4),   K = f1 sqrt(4-2sqrt2)
                    on |u| <= pi/8 - beta/2 = 0.247867.  K = 1.302051691617.
                    W is decreasing with min W = (1/2)(1-cos beta) = 0.020828596 at the
                    RIGHT junction, matching the last phase's (1/2)(1-sin t) there.
                    Positivity of W is elementary but not written out.

All three closed forms checked against numerical differentiation to 1e-10.  Combined with
convexity of C2 and the tangency identity, this is what reduces M3 (S_1 = sigma) to
W > 0.

## 🟢 ITEM 4: THE IDENTITY AT 61 DIGITS (ambi_precision.py)

mpmath at 60 working digits, all constants from closed forms:

    V     = 0.184193197088768988251655564606289616337273660
    |C2|  = 2.013341612602978828172120476813212917868800180
    Q(Sigma) - A_R* = -1.5557538e-61          (relative 9.46e-62)
    4 a1 sin beta - 1 = -7.8e-62              (T3, as a byproduct)

The two sides share no computation, so the earlier 5e-13 agreement was not a
double-precision coincidence.  Still floating point, not an enclosure (Rule 7).

## 🟢 ITEM 3: LEAN F18

  cap_branch_sum          the two-branch expansion behind |C2| = int(H^2-H'^2) - H(0) - H(pi)
  principal_symbol_neg    -1 - s + o - f <= -1 for indicators with o <= s (E_1 inside
                          [0,pi/2]); this is why concavity is a finite question
  beta_below_pi_over_six  4*(A*S) = N*N and N < 2*A imply 2*S < N: T3 forces beta < pi/6
  phase1_increasing       0 < 1 - 2*S
  phase3_increasing       0 <= 1 - S
  facet_tangency          (CX0 - A2) + (A2 + A1 - G) = CXP + A1 given CX0 = 0, G = -CXP

68 theorems, 14 defs, zero sorry; #print axioms on all six: [propext, Quot.sound].

## 🟢🟢 Q = |C2| - 2V IS TIGHT, CRITICAL AND CONCAVE AT SIGMA (one cell), and one RETRACTION

Baek Thm 7.1.5 needs three things of an upper bound: (i) Q >= |sofa| with equality at the
candidate, (ii) nonpositive first derivative, (iii) concavity.  For the functional built
in the previous section, (i)-as-an-identity, (ii) and (iii)-on-Sigma's-cell now all hold.

### The cap is an exact quadratic form (ambi_hessian.py)

rho(x,y) = (x, 1-y) is a reflection in y = 1/2, NOT in the origin, so
h_{rho A}(u) = h_A(Ru) + u_y with R = diag(1,-1).  That is why the support function of
C2 = C ^ rho C is NOT H(|theta|):

    h_2(theta) = H(theta)                theta in [0, pi]
    h_2(theta) = H(-theta) + sin theta   theta in [-pi, 0]

(checked against the polygon at theta = -pi/2, -0.5, -2.4).  Using H(|theta|) gives
4.347 for the area against the true 2.013 -- a real bug, caught by comparing to the
polygon support function.  With the correct branches,

    |C2| = int_0^pi ( H^2 - H'^2 ) dtheta - H(0) - H(pi)                          (A)

The derivation needs only h_2 in H^1 of the CIRCLE, where <h_2'',h_2> = -int h_2'^2 with
no boundary or atom terms.  Verified: (A) = 2.013341613 against A_R* + 2V = 2.013341613,
agreeing to 9.6e-13.  (A) and V share no computation, so this is an INDEPENDENT analytic
confirmation of |Sigma| = |C2| - 2|N| with |N| = V -- the identity is now good to 1e-12,
not the 1e-8 recorded from the polygon comparison.  Equivalently

    Q(Sigma) = 1.644955218425 = A_R*   to 5e-13.

The correction -H(0)-H(pi) is LINEAR, so the Hessian is unaffected.

### The second variation (ambi_concavity.py)

Since nu_t = mu_{t+pi/2} everything is a functional of ONE function H on [0,pi].  With
d(alpha_1) = eta(t+pi/2) - eta'(t), d(alpha_2) = eta(t) + eta'(t+pi/2) and
d(sigma) = eta(t) tan t + eta(t+pi/2), the eta(t+pi/2) CANCELS in the middle term:

    d(sigma - alpha_1) = eta(t) tan t + eta'(t),

and (gauge H(0)=1 from x-translation, H(pi/2)=1 from the unit corridor -- which is also
exactly what makes sigma tan-integrable at pi/2, so eta(0)=eta(pi/2)=0)

  (1/2) d^2 Q = int_0^pi (eta^2-eta'^2) - int_{E2}(eta(t)+eta'(t+pi/2))^2
                - int_0^{pi/2}(eta tan t + eta')^2 + int_{E1}(eta(t+pi/2)-eta'(t))^2

PRINCIPAL PART IS NEGATIVE: coefficient of eta'(theta)^2 is -1 on [0,beta) and
[pi-beta,pi], -2 in between.  So the form is bounded above with finitely many
non-negative eigenvalues -- concavity is a FINITE question.

### CRITICALITY: dQ = 0 in every direction

Central differences on Q itself: ||dQ||_inf/h = 1.8e-8, ||dQ||_2/h = 4.5e-8, dim 63.
So ROMIK'S ODEs ARE THE EULER-LAGRANGE EQUATIONS OF Q.

A BUG WORTH RECORDING.  An analytic assembly of the gradient first reported nonzero
values on [0,beta) and [pi/2,pi/2+beta) and nothing elsewhere (1e-14).  That was a sign
error on d(-(1/2)(alpha_1^-)^2) = +alpha_1^- d(alpha_1), and its support is exactly where
d(alpha_1) is supported, which is why the pattern looked meaningful.  The
finite-difference cross-check on Q is what caught it.  Lesson: an analytic gradient that
vanishes on most of the domain is not thereby validated on the rest.

### CONCAVITY: yes on Sigma's cell, NO in general

    sign pattern                              m=32     m=64    m=128
    Sigma's own (E1=[0,beta), E2=[0,pi/2-b)) -0.6905  -0.7111  -0.7216   concave
    Baek injectivity (E1 empty, E2 all)      -0.8239  -0.8486  -0.8616   concave
    E1 all, E2 all                           -0.0015  -0.0004  -0.0001   marginal
    crude worst case (E2 empty, E1 all)      +1.1734  +1.2114  +1.2306   NOT
    E1 = E2 = [0.4, 1.2]                     +0.3838  +0.3964  +0.4071   NOT
    E1 = E2, three pieces                    +0.3578  +0.3853  +0.4156   NOT

(lam_max/h; a SIGN proxy only -- superseded by the mass-normalised table above.)
Sigma's cell IS convex: alpha_1, alpha_2 are affine in H so
each pointwise sign condition is a half-space.  Concave + critical on a convex set gives
that Sigma maximises Q ON THAT CELL.

### 🔴 RETRACTION

An intermediate scan over sign patterns E1 = [0,tau1], E2 = [0,tau2] found the critical
curve tau2_crit(tau1) = 0, 0.0048, 0.0153, 0.0963, 0.3107, 0.4856, 0.6957, 0.9499,
1.1365, 1.4728 at tau1 = 0, 0.2, beta, 0.5, 0.8, 1.0, 1.2, 1.4, 1.5, pi/2, hence
tau2_crit(tau1) < tau1 always, and I concluded "tau1 <= tau2 implies concave".  That is
FALSE.  The scan only tested intervals ANCHORED AT 0.  Set-theoretically E1 = E2 =
[0.4,1.2] has tau1 = tau2 and gives +0.407.  The claim is RETRACTED.  Same failure mode
as the earlier A10/A11 retraction: a family of test cases too special to see the
phenomenon.

### The boundary of C2, incidentally determined

H + H'' (the surface-measure density) is: 0 on (-beta,beta), the VERTEX P = (1,1/2);
0.836 -> 0.5 on [beta, pi/2-beta); exactly 1/2 on (pi/2-beta, pi/2+beta), a CIRCULAR ARC
OF RADIUS 1/2 centred at (1-2a_1, 1/2) = (-0.750574725, 0.5); an ATOM of mass 1.167050 at
theta = pi/2, the corridor ceiling y=1, a FACET; then symmetric; 0 on (pi-beta,pi], the
second vertex.  Plus the rho-mirror below.  The rho-image of the ceiling facet is the
floor segment [-0.750575, 0.416475] x {0}, whose left end sits directly below the arc's
centre.

### M3 (S_1 = sigma) REDUCED

C2 is CONVEX, so the face-1 segment lies in C2 as soon as its FAR ENDPOINT does.  So
S_1 = sigma reduces to a one-parameter containment: x(t) = c_x(t) + sigma(t) sin t must
lie in the floor facet.  Measured: x runs MONOTONICALLY from x(0) = 0 to
x(pi/2) = 0.416475 = the right end of the facet, min increment +1.8e-6 over 200001
samples, and

    x(pi/2) = c_x(pi/2) + alpha_1(pi/2) = [c_x(0) - alpha_2(0)] + [facet length]

is an ALGEBRAIC IDENTITY (facet length = H'(pi/2+) - H'(pi/2-) = alpha_2(0) +
alpha_1(pi/2) - (G(pi/2)-1)).  So the tangency at t = pi/2 is exact, and what remains of
M3 is monotonicity of one explicit function.

### Honest status

  * Q(Sigma) = A_R*: HEURISTIC at 5e-13, but now from TWO independent analytic routes.
  * dQ(Sigma) = 0: HEURISTIC at 1.8e-8.
  * d^2 Q < 0 on Sigma's cell: HEURISTIC (eigenvalues of a discretised form).
  * Sigma's cell is convex: PROVED.
  * Principal part of d^2 Q negative: PROVED.
  * (A): PROVED.
  * Q >= |sofa| FOR COMPETITORS: NOT DONE.  This is the whole point of Q and it is
    exactly Baek's Ch. 3-6.  Without it none of the above bounds anything.
  * Concavity on OTHER cells: FALSE (counterexamples above).
  * Therefore optimality of Sigma remains OPEN.  What is new: the functional now
    satisfies all three of Thm 7.1.5's hypotheses at Sigma on its own cell, and the
    single remaining gap is the domination inequality for competitors.

## 🟢🟢 P3c SOLVED: THE NICHE FUNCTIONAL IS TIGHT AND BUILT FROM CONVEX-LINEAR DATA

The blocker for eight sessions was that no underestimate of the niche was TIGHT: the
best one, built from the apex path, dominated but left slack 0.087 against
|Sigma| = 1.645, and the missing area sat exactly on the phases where Baek's
injectivity condition fails.  Both halves of that are now resolved.

### The reconstruction (ambi_mamikon.py)

Pushing both outer walls in until they touch the cap puts the corner at

    c(t) = (F(t)-1) mu_t + (G(t)-1) nu_t,    F = h_K(mu_t), G = h_K(nu_t),

so c is AFFINE-LINEAR in the support function, hence convex-linear on Baek's domain.
Three scalars inherit it:

    alpha_1 = -<c',mu_t> = G - 1 - F'      face-1 arm
    alpha_2 =  <c',nu_t> = F - 1 + G'      face-2 arm
    sigma   = c_y/cos t  = (F-1) tan t + G - 1    face-1 reach to the corridor floor

Baek's Def 6.1.2(3) is exactly alpha_1, alpha_2 > 0.

### The decomposition (ambi_split.py) — MEASURED EXACT

The normal velocity of the face-i line at distance s from the corner is s - alpha_1 on
face 1 and alpha_2 - s on face 2.  So the niche is created by the INNER part of face 2
and the OUTER part of face 1:

    N = W_2  (+)  W_1out       overlap 0.000000000,  N \ (W_2 u W_1out) = 0.000000000

W_2 = sweep of [c, c - alpha_2^+ mu_t];  W_1out = sweep of face 1 from c - alpha_1^+ nu_t
outward.  Both numbers are zero to the oracle's printing precision, at n_hall = 481.

### The outer arm is convex-linear too (ambi_outerarm.py)

The face-1 direction -nu_t = (sin t, -cos t) points DOWN, and the ray always leaves the
cap through the corridor floor y = 0:

    S_1(t) = c_y(t)/cos t = sigma(t)   on 1200/1201 samples, to 1e-15
                                       (the one failure is t = pi/2, cos t = 0)

That was the last non-convex-linear ingredient.

### The formula (ambi_functional.py) — TIGHT

    |N| = int_0^{pi/2} [ (1/2)(alpha_2^+)^2 + (1/2)(sigma-alpha_1)^2
                                            - (1/2)(alpha_1^-)^2 ] dt = V

Evaluated with EXACT derivatives of SOL1/SOL5/SOL6 (complex forms below) and
Gauss-Legendre per phase so no interval straddles a kink:

    V = 0.184193197089    stable in the 12th digit from 20 to 320 nodes per phase

against the polygonal measurement |W_1 u W_2| = 0.184193171.  An inscribed quad union
UNDER-measures, so the two agree to 2.6e-8 from the expected side.  Cross-check on the
cap: A_R* + 2V = 2.013341613, and the circumscribed polygonal |C2| values 2.013345504
(n=241) and 2.013342045 (n=481, 721) decrease to it, as an intersection of finitely
many half-planes must.  So V = |N| at the 1e-8 level.

    SOL1  z(t) = a1 e^{2it}            - (1 + i/2) e^{it} + (1 - a1 + i/2)
    SOL6  z(t) = (f1 - i f2) e^{3it/2} - (1 + i)   e^{it} + (1 - (4/3)a1 + i/2)
    SOL5  z(t) = a1 e^{2it}            - (1/2 + i) e^{it} + (1 - (5/3)a1 + i/2)

max err vs the reference piecewise path: 5.0e-16.

### The injectivity failure was an artefact — B2 REPAIRED

Baek's condition asks alpha_1 > 0 AND alpha_2 > 0.  For Sigma alpha_1 > 0 only on
[beta, pi/2] and alpha_2 > 0 only on [0, pi/2-beta], so the JOINT condition holds only
on the middle phase — which is what B2 measured and what result 10 reported.  But the
decomposition uses each face only on the range where its OWN arm has the right sign:
face 2 enters as alpha_2^+ (zero where alpha_2 <= 0, costing nothing) and face 1 needs
only sigma >= alpha_1^+, which holds throughout with equality only at t = pi/2
(min sigma - alpha_1 = -6.4e-8, at t = pi/2).  No joint hypothesis is used anywhere.
So B2's failure does not obstruct this construction.

### What is left: ONE term with the wrong curvature

Two of the three terms are convex quadratics in h, since x -> (1/2)(x^+)^2 and
x -> (1/2)x^2 are convex and alpha_2, sigma - alpha_1 are affine in h.  The third is
SUBTRACTED, so it contributes a CONVEX term to Q = |C2| - 2V — the wrong sign for
concavity.  It is supported exactly on the degenerate phase [0,beta), where
alpha_1 = 2 a1 sin t - 1/2 < 0, and equals in closed form

    (1/2) int (alpha_1^-)^2 dt = beta/8 - a1(1-cos beta) + a1^2(beta - sin(2beta)/2)
                               = 0.011950270059     (6.488% of V)

verified against quadrature to 2.9e-16.  Note alpha_1 < 0 <=> sin t < 1/(4a1) <=>
t < beta is exactly T3, so the support of the obstruction IS the T3 threshold.

### Honest status

  * V = |N| for Sigma: at the 1e-8 level, HEURISTIC by Rule 7 (it is an area
    measurement plus quadrature, not an enclosure).  The three geometric hypotheses
    (disjoint, injective, covering) are MEASURED, not proved.
  * Convex-linearity of alpha_1, alpha_2, sigma: PROVED (affine algebra on (C)).
  * The normal-velocity lemma: PROVED.
  * The closed form of the obstruction: PROVED.
  * Concavity of |C2| - 2V: NOT ATTEMPTED.  Needs the Hessian as a quadratic form on
    support-function perturbations.
  * Validity for COMPETITORS: NOT ATTEMPTED.  This is Baek's Ch. 3-6 half.
  * Therefore optimality of Sigma remains OPEN.  What changed is that the upper bound
    is now tight and in convex-linear data, with one explicitly computed bad term.

## AUDIT FOR FIXED-SCALE / WEAK-PROXY ARTIFACTS — one real bug found

Three artifacts in one session (coarse t-grid on the corner margin; fixed-eps sampling
in A10/A11; oscillatory-quadrature ETA) made an audit necessary.  The failure mode is
always the same shape: a claim is tested with a proxy or at a fixed scale, while the
phenomenon lives at a scale that shrinks or in a property the proxy cannot see.

### B2 (injectivity) — AUDITED CLEAN, and sharpened

Fine scan of the injectivity signs over (0, pi/2), 400 samples plus bisection:

  * exactly THREE sign-pattern transitions, no thin subintervals;
  * x'.u_t changes sign at t = 0.289653820817321, and beta = 0.289653820817321;
  * x'.v_t changes sign at t = 1.28114250597758, and pi/2 - beta = 1.28114250597758.

Agreement to 15 digits, so this is not a near-coincidence.

    T2 [PROVED].  x'(beta) . mu_beta = 0  and  x'(pi/2 - beta) . nu_{pi/2-beta} = 0.

The injectivity failure boundary IS the phase junction, exactly.  That is a sharper and
cleaner statement than "fails on the outer phases", and it gives a geometric
characterisation of beta: it is where the inner corner's velocity becomes perpendicular
to mu.

### A REAL BUG, caught by the audit

Building the pi-range cap C2 = cap_{[-pi/2,pi/2]} C_t, the first implementation used the
normals (mu_t, nu_t) on BOTH branches.  That is wrong for t < 0: the reflected
half-planes have normals R mu_s = mu_t and R nu_s = -nu_t, so the second normal flips
sign.  With the bug, |C2| = 1.901567157; corrected, |C2| = 2.013345504.

The bug survived the first symmetry check because that check compared AREAS:
|C2| and |rho C2| agreed to 2.22e-16 while the SYMMETRIC DIFFERENCE was 0.175.  Equal
areas do not imply equal sets.  Recorded as a standing lesson: symmetry must be tested
by symmetric difference, never by area.

### A second proxy failure, benign

With the normals fixed, shapely reported C2 as NOT convex.  Measuring the convexity
defect |conv(C2)| - |C2| at n = 61, 121, 241 gives -4.4e-16, +4.4e-16, -1.8e-15 --
machine epsilon, not growing with n.  So C2 IS convex, as it must be (an intersection
of half-plane pairs), and `shapely.equals(convex_hull)` was defeated by vertex noise
across 790 near-collinear vertices.  Recorded so the test is not trusted again.

### Audit verdict on the remaining live claims

  * A1, A2, A3, A3', A5, A6 -- all PROVED analytically, no sampling exposure.
  * T1, T1a -- now PROVED with a closed-form threshold; the earlier grid evidence is
    superseded and its artifacts explained.
  * P1 (the pi-range identity) -- symmetric difference EXACTLY 0, which is the strong
    test, not an area comparison.  Clean.
  * D1, T2 -- analytic / 15-digit bisection.  Clean.
  * The only remaining numerical inputs are shapely areas with known O(1/n)
    convergence, which is a different and understood error mode.

## P3 FOUNDATION ESTABLISHED

For the pi-range family, with c(-t) = rho c(t):

    |C2|            = 2.013345504      (n = 241)
    |Sigma|         = 1.645583698
    |niche ^ C2|    = 0.367761807
    |U ^ C2|        = 0.183880903
    |Sigma| = |C2| - 2 |U ^ C2|                                    (by A4/A6 + T1)

and the three structural facts P3 needs are verified:

    C2 is CONVEX                 convexity defect ~1e-15, stable in n
    C2 is rho-SYMMETRIC          symmetric difference EXACTLY 0
    Sigma subset C2              contains-test passes

So the objects Baek's Ch. 7-8 machinery consumes -- a convex cap, a niche, and the
identity expressing the body as cap minus niche -- all exist for the pi-range family,
with the niche halved by rho-symmetry.

REMAINING for P3, and this is the actual mathematics: construct an UNDERestimate
U' subset U whose area is a sum of Mamikon regions with convex-linear data, so that
|C2| - 2|U'| is a quadratic functional that is CONCAVE (Baek Thm 7.4.2) and dominates
|Sigma|.  Baek builds his N' from a core and two tails using injectivity; by T2 that
input fails precisely at Sigma's junctions, so the tails need separate treatment on
[0, beta) and (pi/2 - beta, pi/2].  Those are exactly the phases where the contact arcs
are CONSTANT (D1), which is the most tractable degeneracy available: a constant arc
contributes nothing to a Green integral.

## 🔥🔥 ONE FACT EXPLAINS ALL FOUR FAILURES: the ambidextrous problem is an omega = pi problem

After four failed transfers (direct balancing, rho-quotient, prescribed-edge,
injectivity), the right move was to reframe rather than patch again.

### The reformulation  [PROVED, verified exactly]

rho maps the hallway at angle s to the hallway at angle -s with corner rho c(s), so
intersection_{t in [-pi/2,0]} H_t = rho S, and therefore

    Sigma  =  intersection_{t in [-pi/2, pi/2]} H_t ,        c(-t) = rho c(t).     (*)

VERIFIED: the two constructions agree to 7.3e-15 with symmetric difference area
EXACTLY 0.000e+00 (n = 481).  |S| = 1.989684033, |S ^ rho S| = 1.645268432 =
|cap_{[-pi/2,pi/2]} H_t|.

So the ambidextrous constraint family is a SINGLE family spanning an angle range of
length pi, not two families of length pi/2.

### The caveat that matters

The corner path of (*) is DISCONTINUOUS at t = 0.  For Romik's path c_y(0) = 0, while
rho c(0) has height 1, so the corner jumps by 1 in y across t = 0.  Hence (*) is an
exact identity of CONSTRAINT FAMILIES, not the statement that Sigma is a monotone
sofa of rotation angle pi in Baek's sense -- his monotone sofas move continuously.

### Why this explains the four failures as ONE fact

Baek's framework is built for omega in (0, pi/2].  His Lemma 3.4.2 uses omega <= pi/2;
the parallelogram P_omega is defined for that range; and Chapter 4's main conclusion is
that a balanced maximum sofa has omega = pi/2 EXACTLY -- pi/2 is the top of his range
and the value his maximisers attain.

The ambidextrous problem sits at an angle range of pi, with a discontinuous corner
path.  Both features are outside his setting.  So:

  * B1 (balancing) failed because his identity pairs the cap boundary against ONE
    niche polyline, which is the omega <= pi/2 picture;
  * B1b (quotient) failed because cutting at y = 1/2 introduces a free edge, which is
    an artifact of forcing a pi-range problem into a pi/2-range frame;
  * B1d (prescribed edge) failed because that edge is not perturbation-stable;
  * B2 (injectivity) failed ON THE CANDIDATE, on exactly the phases [0,beta) and
    (pi/2-beta, pi/2] adjacent to the discontinuity at the ends of the half-range.

Four symptoms, one cause.  This is the most useful thing the session has produced
about the ambidextrous problem, and it is a reason to stop adapting Baek's
architecture rather than to attempt a fifth variant: the architecture is not
mis-applied, it is out of range.

### What the reformulation suggests instead

The upper-bound half of Baek's work (Ch. 7-8) does NOT use the motion; it needs only
the cap/niche structure and convexity.  So the promising direction is to build the
concave quadratic bound directly for the pi-range family, bypassing Ch. 3-6 entirely:

  * the cap is C2 = cap_{[-pi/2,pi/2]} C_t, convex, rho-symmetric;
  * the niche is U u rho U, and A1-A6 give that these are DISJOINT and congruent, so
    the niche area is 2|U| -- one niche's worth of work;
  * concavity would come from Mamikon exactly as in Thm 7.4.2, which is indifferent
    to the angle range;
  * criticality of Sigma comes from Romik's ODE1/ODE6/ODE5.

What is then MISSING is only the existence/regularity input that Ch. 3-6 supplies in
the omega <= pi/2 case -- and that would be assumed as a hypothesis, giving a
CONDITIONAL theorem.  The conditional theorem is the honest target.

## The degeneracy, stated as a positive result

Three independent methods have broken at the same place, and it is worth stating as a
structural fact about the ambidextrous problem rather than as three separate defeats.

On the outer phases [0, beta) and (pi/2 - beta, pi/2]:

  1. Sigma's contact arcs dA and rA are CONSTANT, pinned at the rho-FIXED point
     (1, 1/2) (verified to 3e-31).  A constant contact arc contributes nothing to a
     Green integral, and it is not a well-defined contact POINT: there the hallway
     touches along a segment.
  2. The second-variation route failed there: the constant arcs are what made the
     closure chords move, producing the rank-one defect -(l/2)L, and later the
     self-intersection lens.
  3. Baek's injectivity condition fails there, and only there: x'.u_t > 0 on
     [0, beta) and x'.v_t < 0 on (pi/2 - beta, pi/2], with sign changes exactly at the
     junctions.

So the degenerate phases are simultaneously: where the contact structure collapses,
where local analysis breaks, and where the injectivity hypothesis of the successful
one-corner proof is violated.  That is a coherent statement about where the difficulty
of the ambidextrous problem lives, and it is publishable content independent of
whether an optimality theorem follows.

## 💧💧 B2: BAEK'S INJECTIVITY CONDITION FAILS FOR ROMIK'S Σ ON THE OUTER PHASES

S3 turned out to DEPEND on B2, not to be independent of it.  Working through what
the conditional theorem needs: (a) |K^-| quadratic in K^- is Baek Thm 7.1.3 and holds
for any planar convex body, verbatim; (c) concavity via Mamikon Thm 7.4.2 needs only
convex-linearity, verbatim; (d) criticality of Σ comes from Romik's ODEs.  But (b),
the construction of the niche UNDERestimate N' from a core and two tails, consumes
the injectivity condition.  So B2 is on the critical path.

### The condition, and the measurement

Baek Def 6.1.2(3): for all t in (0, pi/2),  x'(t) . u_t < 0  and  x'(t) . v_t > 0,
equivalently the arm lengths f, g exceed 1 (his Thm 6.2.3).

Measured on Romik's Σ (closed forms for x1/x6/x5, dps 30):

         t         x'.u_t          x'.v_t     ok
      0.05     +0.41250773     +0.74838696    NO
      0.15     +0.23839738     +0.73091766    NO
      0.28     +0.01621879     +0.68239936    NO
    0.2897 = beta   -3.87e-05  +0.67762761    yes
      0.35     -0.05015705     +0.64671857    yes
      0.50     -0.17059301     +0.56340138    yes
      pi/4     -0.38103426     +0.38103448    yes   (f = g = 1.381034)
      1.00     -0.52099380     +0.22518967    yes
      1.20     -0.63571004     +0.06722282    yes
     1.281 = pi/2-beta  -0.677579  +1.195e-04 yes
      1.35     -0.70807665     -0.11661243    NO
      1.50     -0.74618951     -0.37616924    NO

So the condition holds EXACTLY on the middle phase (beta, pi/2 - beta) and fails on
both outer phases, with x'.u_t changing sign precisely at beta and x'.v_t precisely
at pi/2 - beta.  By the rho-symmetry A(t) = -B(pi/2 - t) the two failures are the
same failure conjugated.

Note this is not the weak form either: Baek's Remark 6.1.1 records that Romik assumes
only x'.u <= 0 and x'.v >= 0, but at t = 0.05 we have x'.u = +0.41, strongly positive,
so even the weak form fails on the outer phases.

### Why this is coherent with everything else

The outer phases [0, beta) and (pi/2 - beta, pi/2] are EXACTLY where Σ's contact arcs
dA and rA are CONSTANT, pinned at the rho-fixed point (1, 1/2) -- the degeneracy found
early in this program and responsible for the constant-arc/chord failures that killed
the second-variation route.  The same degenerate phases are where Baek's injectivity
fails.  Three independent lines of attack have now broken at the same place, which is
evidence that the degeneracy is the real content of the ambidextrous problem rather
than an artifact of any one method.

### Consequence

The conditional theorem cannot simply assume injectivity on (0, pi/2), because the
CANDIDATE does not satisfy it.  Options:

 (i) restrict the injectivity hypothesis to the middle phase and handle the outer
     phases separately, using the fact that the contact arc is constant there (so its
     contribution to the niche is degenerate and may be computable exactly);
 (ii) find the correct ambidextrous analogue of the condition -- Baek's version is
     tuned to a single hallway family, and the ambidextrous problem has two, so the
     natural condition may involve x' tested against BOTH frames;
 (iii) abandon the transfer.

Option (i) is the most promising precisely because the failure region is where the
arcs are constant, which is the most tractable possible degeneracy: a constant arc
contributes nothing to a Green integral.

## F12 formalized: the angular gap

    wedge_gap        P - t < P + t for t > 0
    wedge_gap_width  (P + t) - (P - t) = 2t

With P standing for pi, the spans [t+pi, t+3pi/2] of Q_t and [pi/2-t, pi-t] of rho Q_t
miss each other by exactly 2t at a rho-fixed apex.  This is why no single wedge pair
separates (h*(t) > 1/2 throughout) while the full family does (S1): the gap closes
only as t -> 0.  43 theorems, zero sorry.

## 🔥🔥🔥 S1 ESTABLISHED: connectedness forces M <= 1/2, at a threshold of EXACTLY 1/2

This discharges the conditional hypothesis of the quotient reduction and satisfies
the continuation condition (S1) of the stopping rule recorded last session.

### The finding

The single-t analysis (A10-A12) showed no single wedge pair forces M <= 1/2, since
h*(t) > 1/2 throughout (0, pi/2).  The FULL family does.  Deform Romik's path upward
near its maximum, c_y -> c_y + delta g with g vanishing at both ends, and compute
Sigma = S ^ rho S:

     delta         M      |Sigma|   pieces
    0.11000   0.4978381   1.5759326    1
    0.11150   0.4993381   1.5740343    1
    0.11200   0.4998381   1.5733958    1
    0.11216   0.4999981   1.5731909    1     <- connected
    0.11217   0.5000081   1.5731781    4     <- SPLIT
    0.11230   0.5001381   1.5730115   10
    0.11300   0.5008381   1.5721259   14
    0.12000   0.5078381   1.5636629    4

The transition is at M = 1/2 to SIX decimal places.

ROBUSTNESS.  Repeated with the bump peaking at t = 0.5, 0.6, 1.0 and pi/4 and widths
0.4 to 0.9: every case is connected just below M = 1/2 and split just above
(M = 0.4994 connected / M = 0.5006 split in all four).  The threshold does not depend
on the deformation, so it is a property of the geometry and not of the test family.

### The mechanism, which explains why the single-t argument had to fail

At the threshold c_y(t_0) = 1/2 the apex lies ON the symmetry axis, so
rho c(t_0) = c(t_0): the two wedges SHARE an apex.  Their angular spans are

    Q_{t_0}      :  [ t_0 + pi , t_0 + 3pi/2 ]
    rho Q_{t_0}  :  [ pi/2 - t_0 , pi - t_0 ]

leaving an angular GAP of width 2 t_0 at the shared apex.  That is exactly why a
single pair never separates (and why h*(t) > 1/2, approaching 1/2 only as t -> 0,
where the gap closes).  For c_y(t_0) > 1/2 the wedges of NEARBY t, together with
their rho-images, fill the gap and the union separates the body.

So the two computations are consistent, and the mechanism is a neighbourhood
argument rather than a pointwise one.  That is the shape a proof should take.

### Status and consequence

CONJECTURE (connectedness ceiling).  Every connected ambidextrous moving sofa
satisfies max_t c_y(t) <= 1/2.

Label HEURISTIC -- but with a threshold pinned to six decimals, robustness across
four independent deformation families, and an identified mechanism.  Granting it, the
quotient reduction is UNCONDITIONAL:

    for every ambidextrous moving sofa,  |S| = 2 ( |K^-| - |U ^ K^-| ),

a convex cap minus ONE niche, which is the shape Baek's concavity method needs.

The note is now 6 pages and states this properly: the single-t threshold h*(t), the
full-family computation, the conjecture, the mechanism, and the proposition in the
form "conditional, and unconditional granting the conjecture".

### What this does NOT do

It does not supply the existence half of Baek's architecture.  Three attempts to
transfer his balancing argument have failed (B1 direct, B1b quotient, B1d
prescribed-edge).  S1 removes a hypothesis from the REDUCTION; it says nothing about
existence.  The route to an actual optimality theorem is still (S3): check whether
Baek Ch. 7-8 yields the conditional statement.

Per the stopping rule, (S1) being established means work continues.

## A GAP IN MY OWN REDUCTION, AND WHAT CONNECTEDNESS DOES AND DOES NOT GIVE

Found while attempting B1d.  Last session's quotient reduction
|Sigma| = 2(|K^-| - |U ^ K^-|) uses M := max_t c_y(t) < 1/2, which is a property of
ROMIK'S trajectory, NOT of an arbitrary competitor.  And a competitor with
M >= 1/2 has OVERLAPPING niches, which by inclusion-exclusion makes
|U u rho U| smaller and hence |Sigma| = |C2| - |U u rho U| LARGER.  So overlap is
advantageous for area and cannot be assumed away on extremal grounds.

Attempted rescue: connectedness.  A moving sofa is connected by definition, and if
the apex sits above the axis the down-opening wedge Q_t lies above the up-opening
rho Q_t, so their union might remove a full vertical segment and cut the body.

MEASURED THRESHOLD.  For a single t, Q_t u rho Q_t removes a full vertical segment
exactly when the apex height exceeds h*(t):

        t        h*(t)      c_y(t) for Romik
      0.05     0.500500        0.038029
      0.10     0.501003        0.076557
      0.20     0.502027        0.152150
      0.30     0.503093        0.221049
      0.50     0.505463        0.327543
      pi/4     0.510000        0.387838
      1.00     0.515574        0.353399
      1.20     0.525722        0.263874
      1.35     0.544552        0.167212
      1.45     0.582381        0.092553
      1.52     0.696695        0.038640

Two readings, one positive and one negative.

POSITIVE: h*(t) > 1/2 for EVERY t in (0, pi/2).  So the wedge pair never cuts when
the apex is at or below 1/2 -- the separation threshold M < 1/2 is exactly the right
one, and Romik's trajectory clears it everywhere with room (0.3878 against h* >= 1/2).

NEGATIVE: h*(t) exceeds 1/2 strictly in the interior, and h*(t) -> 1/2 only as
t -> 0.  So a single-t connectedness argument CANNOT force M <= 1/2: a competitor
could carry c_y(t) slightly above 1/2 at interior t without being cut by that pair
alone.  My conjectured lemma "connected implies M <= 1/2" is FALSE as stated.

What survives is the pointwise constraint c_y(t) <= h*(t) for every connected
ambidextrous sofa.  Whether the FULL family of wedge pairs (rather than one t at a
time) forces M < 1/2 is open and is the natural next question; a competitor evading
the constraint must thread between all of them simultaneously.

CONSEQUENCE FOR THE CLAIM.  The quotient reduction is CONDITIONAL on M < 1/2, and
the note now says so explicitly (Proposition, conditional form).  Last session's
statement of it was too strong and has been corrected.

## B1d: the prescribed-edge class does not work either

The idea was to fix sigma_cut as a class constant.  It fails for a simple reason:
pushing an edge e(t) of the cap generally CHANGES the length of the top edge at
y = 1/2, so the class of caps with a prescribed horizontal edge is not closed under
the perturbations the balancing argument needs.  Fixing sigma_cut and perturbing are
incompatible.

That is the THIRD failed attempt to transfer the existence half of Baek's
architecture (B1 direct, B1b quotient, B1d prescribed-edge).  Per Rule 16 that is
the signal to stop iterating on this strategy rather than attempt a fourth variant.

## STOPPING RULE (agreed threshold, recorded in advance)

The deliverable is now the note: separation theorem, closed form for f1, ODE6 with
its characteristic-exponent explanation, and the conditional quotient reduction.
That is a small, correct, new contribution to an open problem.

The ambidextrous OPTIMALITY theorem requires an existence argument, and three
attempts to import Baek's have failed for three different reasons.  Continuing is
justified only by a genuinely different idea for existence, not another adaptation.
Concretely, work continues only if one of these is established:

  (S1) the full wedge family forces M < 1/2 for connected ambidextrous sofas
       (removing the conditional hypothesis), or
  (S2) an existence argument for a maximum ambidextrous sofa of the required
       regularity that does not go through balancing at all, or
  (S3) a proof that Baek's Ch. 7-8 concavity machinery yields the CONDITIONAL
       theorem as stated, which would be a real result even with the hypothesis.

If none of (S1)-(S3) is in hand after one further session, the honest outcome is to
finish the note and stop.  (S3) is the most likely to succeed and is the cheapest,
because it consumes the quotient reduction directly and needs no new existence
theory.

## B1b: THE RHO-QUOTIENT REDUCTION — the ambidextrous problem becomes a ONE-niche problem

This is the new content of this turn, and it is a consequence of the separation
theorem rather than an independent construction.

### The reduction  [PROVED]

A1--A3 give U subset {y <= M} with M = 0.3878381292... < 1/2.  So the ENTIRE lower
niche lies below the symmetry axis, and intersecting with the lower half-strip
removes rho U completely:

    Sigma^- := Sigma ^ {y <= 1/2} = K^- \ U,        K^- := C2 ^ {y <= 1/2},

with K^- convex, and by rho-symmetry

    |Sigma| = 2 |Sigma^-| = 2 ( |K^-| - |U ^ K^-| ).                       (Q)

That is Baek's shape exactly: a convex cap minus ONE niche.  The two-niche
obstruction that killed B1 is gone in the quotient.

VERIFIED (project builder, n_theta = 1441):
    |Sigma|             = 1.645059395    (A_R* = 1.644955218; the 1.04e-4 is the
                                          n_theta discretisation)
    |Sigma ^ {y<=1/2}|  = 0.822529698
    2 x that            = 1.645059395    rho-symmetry error 3.775e-15
    rho U meets {y<=1/2}?  NO, clearance 1 - M - 1/2 = 0.112161871
    U entirely below the cut?  yes, clearance 1/2 - M = 0.112161871

### What still does not close, and by exactly how much

The balancing argument in the quotient acquires a DEFECT.  The boundary dK^- now
includes the horizontal cut at y = 1/2, of outward normal angle pi/2, where the
niche polyline has tau = 0.  Since v_{pi/2} . u_0 = -1, Baek's identity becomes

    sum_{t != cut} (sigma(t) - tau(t)) (v_t . u_0)  =  + sigma_cut  >  0,

which is compatible with sigma(t) <= tau(t) for every pushable t.  So we again get
an INEQUALITY where Baek gets the equality sigma = tau, and it is the equality that
Theorem 3.4.10 (maximum cap contains its niche) consumes.

Moreover the cut cannot be pushed: rho-symmetry pins it at y = 1/2, so it is not
in the admissible perturbation family.

PROGRESS, stated precisely.  The obstruction has shrunk from an entire second niche
polyline (B1) to a SINGLE SCALAR localised at ONE angle: the cut length sigma_cut,
which is the width of Sigma at y = 1/2.  The balance condition becomes

    sigma(t) <= tau(t) for all pushable t,   with   sum_t (tau - sigma)|v_t . u_0| = sigma_cut.

That is a structured conclusion, not a dead end, and it suggests the right class to
work in: caps with a PRESCRIBED horizontal edge at y = 1/2, where sigma_cut is a
known constant of the class rather than a free quantity.

### An equivalent reformulation worth recording

Since Sigma = S ^ rho S, the ambidextrous problem is exactly

    maximise |S ^ rho S|  over one-corner moving sofas S.

Baek's theorem gives the trivial consequence A_R* <= |S| <= 2.2195..., which is far
from tight (A_R* = 1.6450), but the reformulation is clean and may be the more
natural setting for an existence argument, since the constraint set is now the
one-corner sofas, about which Baek's Ch. 2--4 says everything.

## B6 written up

ROMIK_FORMULAS.md now carries SOL6 and ODE6 explicitly, with the derivation of f1
from the junction, and the observation that the characteristic roots i/2 and 3i/2 of
ODE6 are the source of every half-integer angle in the Sigma formulas.

## F11 formalized (no axioms at all)

The identity underlying the ODE6 derivation is a statement about half-angle
trigonometric arcs, and the file's existing `Trig` coefficient machinery expresses
it directly: with `D` the formal derivative in the half-angle,

    D(D v) = -(v + 1)   for every arc with constant term -1,

which is `4 v'' = -(v + (1,1))` for SOL6's bracket.  `Trig.sol6_bracket` and
`Trig.sol6_ode` are proved by `rfl` and depend on NO axioms -- the first
declarations in the development with that property besides the N1 family.  41
theorems, zero sorry.

## Honest assessment of publishability

The reduction (Q) is new, but it is a corollary of the separation theorem rather
than a deep result, and it does not by itself prove anything about optimality.  What
exists now that is publishable is a short note: the separation theorem, the closed
form for f1, ODE6, and the quotient reduction.  That is a genuine but small
contribution to an open problem.

The ambidextrous OPTIMALITY theorem remains blocked at the existence step, and the
blocking object is now identified as sigma_cut.  Nothing in this session has
produced a result of standing comparable to Baek's, and saying otherwise would be
false.

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
