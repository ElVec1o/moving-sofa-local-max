# The ambidextrous moving sofa problem: separation, constants, and obstructions

Vico Bonfioli — <vicobonfioli@gmail.com>

[![DOI](https://zenodo.org/badge/1252674180.svg)](https://doi.org/10.5281/zenodo.20434287)

Working repository. Not a claim of a solved problem; **Status** below states exactly
what is and is not proved, and `paper/PROGRAM.md` is the full ledger, including
retractions.

## The problem

The *ambidextrous* moving sofa problem asks for the largest planar shape that can be
manoeuvred around a right-angled corner of a unit-width hallway turning **both** ways.
Romik's candidate $\Sigma$ has area

$$A_R^\ast = 1.6449552184254408\ldots$$

Its optimality is **open**. The one-corner problem was settled by Baek
([arXiv:2411.19826](https://arxiv.org/abs/2411.19826)), who proved Gerver's sofa
optimal; his hallway has a single corner and his argument does not address the
ambidextrous variant.

## Results

`paper/niche_separation/note.tex` (8pp) is the mathematical content. Labels:
**VERIFIED** = machine-checked in Lean 4, no `sorry`; **PROVED** = complete human
proof; **HEURISTIC** = computational evidence only.

| # | Statement | Label |
|---|---|---|
| 1 | **Niche ceiling.** For $t\in[0,\pi/2]$, $Q_t\subseteq\\{y\le c_y(t)\\}$ | VERIFIED |
| 2 | **Separation.** $U\subseteq\\{y\le M\\}$ and $\rho U\subseteq\\{y\ge 1-M\\}$; if $M<\tfrac12$ the two niches are disjoint | VERIFIED |
| 3 | $M=\max_t c_y(t)=\tfrac12-(\sqrt2-f_1\sqrt{4-2\sqrt2})=0.3878381292441943\ldots$ | PROVED |
| 4 | **Closed form for Romik's $f_1$**, which the literature gives only as a decimal | PROVED |
| 5 | $\lvert\Sigma\rvert=\lvert C_2\rvert-2\lvert U\cap C_2\rvert$ — a convex cap minus **one** niche | PROVED |
| 6 | **Connectedness ceiling.** $p_y>\tfrac12$ forces the sofa to omit a vertical strip of width $(2p_y-1)/(2\tan t_0)$; sharp, since $p_y\le\tfrac12$ leaves a gap at every distance | PROVED (criterion VERIFIED) |
| 7 | $4a_1\sin\beta=1$, and $w=u^4+6u^2+6$ | PROVED |
| 8 | **ODE6**, the ambidextrous phase equation $x''=2Jx'+\tfrac34(x-\kappa_6)-\tfrac14R_t(1,1)^{\mathsf T}$; its characteristic roots $i/2,3i/2$ account for every half-integer angle in the $\Sigma$ formulas | PROVED |
| 9 | $\Sigma=\bigcap_{t\in[-\pi/2,\pi/2]}H_t$ with $c(-t)=\rho c(t)$ — a single constraint family of angle range $\pi$ | PROVED |
| 10 | Baek's injectivity condition holds for $\Sigma$ **only** on $(\beta,\pi/2-\beta)$, failing exactly at the phase junctions | PROVED |
| 11 | **The corner is affine in the support function**: $c(t)=(h(\mu_t)-1)\mu_t+(h(\nu_t)-1)\nu_t$, so the two arms $\alpha_1,\alpha_2$ and the reach $\sigma$ are convex-linear | PROVED |
| 12 | **Normal velocities.** Face $i$ advances on one side of its *own* envelope point, so the niche is inner-face-2 plus outer-face-1 — and result 10's failure is an artefact of requiring both arms at once | PROVED |
| 13 | **The niche area in convex-linear data.** $\lvert N\rvert=\int_0^{\pi/2}\bigl[\tfrac12(\alpha_2^+)^2+\tfrac12(\sigma-\alpha_1)^2-\tfrac12(\alpha_1^-)^2\bigr]dt=0.184193197089\ldots$, against $0.184193171$ measured on the region from the under-measuring side | HEURISTIC ($10^{-8}$) |
| 14 | $\tfrac12\int(\alpha_1^-)^2=\tfrac\beta8-a_1(1-\cos\beta)+a_1^2(\beta-\tfrac12\sin2\beta)=0.0119502700\ldots$, supported exactly on $[0,\beta)$. Granted 13, this is the one term of the wrong curvature | PROVED (the value) |
| 15 | **The cap is an exact quadratic form**: $\lvert C_2\rvert=\int_0^\pi(H^2-H'^2)d\theta-H(0)-H(\pi)$ where $H(\theta)=h_K(\mu_\theta)$, using $h_{\rho A}(u)=h_A(Ru)+u_y$ | PROVED |
| 16 | $Q:=\lvert C_2\rvert-2V$ satisfies $Q(\Sigma)=A_R^\ast$ ($5\cdot10^{-13}$), $\delta Q(\Sigma)=0$ in every direction ($1.8\cdot10^{-8}$), and $\delta^2Q\prec0$ on $\Sigma$'s cell ($\lambda_{\max}/h\to-0.72$) — all three of Baek's Thm 7.1.5 hypotheses, at $\Sigma$ | HEURISTIC |
| 17 | The principal part of $\delta^2Q$ is negative everywhere, so concavity is a **finite** question; and $\Sigma$'s cell is convex | PROVED |
| 18 | $\delta^2Q$ is **not** negative on every cell: $E_1=E_2=[0.4,1.2]$ gives $+0.407$ | HEURISTIC |
| 19 | **$V\ge\lvert N\rvert$ always** (Reynolds: the flux counts advance into already-swept territory), so $Q\le\lvert C_2\rvert-2\lvert N\rvert=\lvert T_{\max}\rvert$ — **$Q$ is not an upper bound**, and $\Sigma$ is an isolated zero of $V-\lvert N\rvert$ | PROVED |
| 20 | $x(t)=(F(t)-1)/\cos t$ is the face-1 line's $x$-intercept and is strictly increasing; $\cos^2t\,x'=\tfrac12-\sin t$ on $[0,\beta)$ (positive since $\beta<\pi/6$) and $\tfrac12(1-\sin t)$ on the last phase | PROVED |
| 21 | $x(\pi/2)=1-\tfrac23a_1=0.4164750917\ldots$ — a closed form for the right end of the corridor floor facet | PROVED |
| 22 | $Q(\Sigma)-A_R^\ast=-1.56\cdot10^{-61}$ at 60 working digits, from two independent closed-form routes | HEURISTIC |
| 23 | $s_{22}(t,t')\to\alpha_2(t)$ and $s_{11}(t,t')\to\alpha_1(t)$ as $t'\to t$, and the resulting injectivity conditions are **linear in $H$**, so $\mathcal K'=\{V=\lvert N\rvert\}$ is **convex** | PROVED |
| 24 | $\Sigma\in\mathcal K'$ (0 of 158802 face-2, 0 of 158802 face-1, 0 of 58081 cross violations), and $\mathcal K'$ has **nonempty interior**: $H_\Sigma+\varepsilon\sin(k\theta)$ stays inside for $k=2$, $\lvert\varepsilon\rvert\le3\cdot10^{-2}$, both signs | HEURISTIC |
| 25 | **Conditional bound.** $\lvert T\rvert\le A_R^\ast$ for cap data in $\mathcal K'\cap\mathcal C$, given (i) tight/critical/concave at $\Sigma$, (ii) the conditions of 23 on $\mathcal K'\cap\mathcal C$, (iii) $M<\tfrac12$ | HEURISTIC |
| 26 | $x$ is strictly increasing on all of $[0,\pi/2]$: the middle-phase inequality $W>0$ is certified by 32 subintervals at 40 digits, $\min L=+6.1\cdot10^{-3}$ | PROVED |
| 27 | **(RC)**: the cap is nowhere flatter than a circle of the corridor's width, i.e. $(H+H'')_{\mathrm{ac}}\le1$. Linear in $H$, hence convex. **Classical**: by the dual of Blaschke's rolling theorem this says the cap slides freely inside a unit ball, up to the corridor facets; equivalently $C_2=[\text{segment}]\oplus D$ with $D$ a Minkowski summand of the unit disc. We claim its *use*, not the condition | known |
| 28 | **(RC) implies both self-intersection conditions of 23, for every pair.** The reduction is $\Phi''+\Phi=1-(H+H'')(t-\tau+\pi/2)$ with zero initial data, so $\Phi=\int_0^\tau\sin(\tau-u)R\,du\ge0$; the facet atoms sit where the kernel vanishes | PROVED |
| 29 | $\Sigma$ satisfies (RC) with margin $0.1614$; across twelve perturbations (RC) holds exactly when the conditions of 23 hold | HEURISTIC |
| 30 | The Euler–Lagrange equations of $Q$, pointwise; residual $9.4\cdot10^{-6}$ at $\Sigma$ | HEURISTIC |
| 31 | **(RC) implies the cross condition too**, so it implies all three injectivity conditions: $V=\lvert N\rvert$ and $Q\ge\lvert\text{sofa}\rvert$ on $\{(\mathrm{RC})\}$ | PROVED |
| 32 | $\delta Q(\Sigma)=0$: all six Euler–Lagrange residuals vanish **identically in $a_1,f_1,f_2$**. Romik's ODE families are exactly the critical-point equations of $Q$ | PROVED |
| 33 | $-p^2-(qT+p)^2+(r-p)^2=-(p+qT+r)^2+2r^2+2qTr$: the added term is absorbed exactly, leaving a derivative-free remainder | PROVED |
| 34 | Gårding constant $c=0.7285\ldots$ measured; the ingredients (Poincaré constants $4$, $1$, $29.41$; coefficient $-1.83$; requirement $0.135\le\tfrac12$) are all in place, the chain not assembled | HEURISTIC |
| 35 | $\delta^2Q\le0$ on $\Sigma$'s cell, with explicit constants $-1.6013,-0.3710,0,-0.005$; strict for $\eta\ne0$. So $Q$ is concave there | PROVED |
| 36 | $\sigma-\alpha_1=\cos t\,x'(t)$: the middle term of the niche formula is $\tfrac12\int\cos^2t\,x'^2$, an energy of the intercept path | PROVED |
| 37 | $A_R^\ast=1+4\tan^2\beta+\beta$, and $Q(\Sigma)$ matches it to $2.7\cdot10^{-51}$ | PROVED / HEURISTIC |
| 38 | **(RC) holds for $\Sigma$**, in closed form: $\max(H+H'')_{\mathrm{ac}}=\tfrac34f_1\sqrt{4-2\sqrt2}\cos(\tfrac\beta2+\tfrac\pi8)=0.8388\ldots<1$, and it suffices that $f_1^2\le16/(9(4-2\sqrt2))$ | PROVED |
| 39 | $Q(\Sigma)=A_R^\ast$, proved structurally: (RC) gives $V=\lvert N\rvert$, separation gives $\lvert\Sigma\rvert=\lvert C_2\rvert-2\lvert N\rvert$. No integral is evaluated | PROVED |
| 40 | **The construction does not recover Gerver.** (RC) fails there, its face-2 sweep is not injective ($33\,002$ of $158\,802$ pairs), and $V>\lvert N\rvert$ accordingly — though Gerver *does* satisfy the one-corner injectivity condition. Classically: part of Gerver's cap boundary is **flatter than the corridor is wide** (curvature radius $1.3986$), so it is not a segment $\oplus$ (summand of the unit disc); $\Sigma$'s is | PROVED |
| 41 | The mirror decomposition gives Gerver the same value, so the failure in 40 is not an orientation artefact; the reason is that $\Sigma$'s cap has vertices at both ends (from its constant contact arcs) while Gerver's does not | PROVED |
| 42 | $M\le H'(0)$, attempted for the separation hypothesis | **FALSE** (the ceiling atom breaks $W\le1$) |
| 43 | **Main theorem.** $\mathcal D=\{$gauge$\}\cap\{$(RC)$\}\cap\{c_y\le\tfrac12\}\cap\{$sign cell$\}$ is convex, contains $\Sigma$, and $\lvert T\rvert\le A_R^\ast$ for every ambidextrous sofa with cap data in $\mathcal D$ | PROVED |
| 44 | $\mathcal D$ is a **$C^2$-ball**: its radius along $\sin(2k\theta)$ scales like $k^{-2}$, so result 43 is a **$C^2$-local** statement. (RC) is always the binding constraint; $c_y\le\tfrac12$ never binds | HEURISTIC |
| 45 | **(RC) is sharp**: face-2 injectivity fails exactly as the curvature density crosses $1$ | HEURISTIC |
| 46 | **Stability.** $\lvert T\rvert\le A_R^\ast-\tfrac{371}{1000}\lVert H-H_\Sigma\rVert^2_{L^2(0,\pi/2)}$ for every ambidextrous sofa with cap data in $\mathcal D$ | PROVED |
| 47 | **Uniqueness.** $\Sigma$ is the unique ambidextrous sofa of area $A_R^\ast$ with cap data in $\mathcal D$ | PROVED |
| 48 | The separation hypothesis is **independent** of (RC): adding $\delta\sin(\theta-\pi/2)$ on $[\pi/2,\pi]$ preserves (RC) and the gauge exactly while pushing $M$ past $\tfrac12$ | PROVED |
| 49 | **Optimality of $\Sigma$** | **not proved** ($\mathcal D$ is a $C^2$-neighbourhood of $\Sigma$; (RC) is sharp and Gerver's cap violates it) |

**Attribution.** Result 7's ingredients $u^3+3u=2$ (equivalently
$4\tan^3\beta+3\tan\beta=1$) and $x^3+6x^2+9x-4=0$ are **not** new: they are the
standard cubics for $\Sigma$'s area, $y(4y^2+3)=1$ and $x^2(x+3)=8$, the latter shifted
by $x=u^2+1$. Equivalently $A_R^\ast=u^2+1+\arctan(u/2)$ with $u^3+3u=2$. We make no
priority claim on result 7; it is elementary from those cubics. See the attribution
remark in the note.

## Why optimality is not proved

Baek's argument has two halves. The **upper-bound** half (his Ch. 7–8) builds a
quadratic functional on a convex domain of convex bodies, concave by Mamikon's
theorem, so a first-order condition suffices. The **existence** half (Ch. 3–6)
supplies a maximum monotone sofa of rotation angle $\pi/2$ satisfying an injectivity
condition.

Four attempts to transfer the existence half failed, for one underlying reason
(result 9): his framework is developed for rotation angle $\omega\le\pi/2$ and his
maximisers attain $\omega=\pi/2$, whereas the ambidextrous constraint family spans
$\pi$ and its corner path is discontinuous at $t=0$.

The upper-bound half is where results 11–14 make progress. Two obstructions have been
removed and one remains.

*Removed.* No trial underestimate of the niche was tight — the best, built from the
apex path, left a slack of $0.087$ against $\lvert\Sigma\rvert=1.645$. Result 13 is
tight, so that slack is gone. And result 10's injectivity failure turns out not to
obstruct: by result 12 each face is used only on the range where its own arm has the
right sign, and no joint hypothesis is used anywhere. The reported failure came from
asking for $\alpha_1>0$ and $\alpha_2>0$ simultaneously.

*Also removed.* The third term of result 13 is **subtracted**, hence contributes a
convex term with the wrong sign for concavity, and result 14 computes it exactly. That
looked like the remaining obstruction. It is not: results 15–17 show
$Q=\lvert C_2\rvert-2V$ is in fact negative definite at $\Sigma$'s sign pattern, with
$Q(\Sigma)=A_R^\ast$ and $\delta Q(\Sigma)=0$. Since $\Sigma$'s cell is convex,
$\Sigma$ maximises $Q$ there.

*And then the obstruction moved again, decisively.* $Q$ is only relevant because
$Q\ge\lvert\text{sofa}\rvert$, and result 19 shows that inequality **fails**. $V$ is the
exact flux of the advancing wedge boundary, and by Reynolds' transport theorem a flux
over-counts advance into already-swept territory, so $V\ge\lvert N\rvert$ always. Hence
$Q\le\lvert C_2\rvert-2\lvert N\rvert$, which is the area of the maximal sofa with that
cap: $Q$ sits *below* what it should bound. Measurement confirms $\Sigma$ is an isolated
zero of $V-\lvert N\rvert$, the excess being positive on both sides and growing faster
than $\varepsilon^2$.

*And then it was partly repaired.* Result 19 stands: on the full domain $Q$ is not an
upper bound. But results 23–25 identify the set where it is one. Two lines meet in a
single point, so a double cover forces that point into both sweep segments, and the
resulting conditions turn out to be **linear** in the support function. So
$\mathcal K'=\{V=\lvert N\rvert\}$ is convex, contains $\Sigma$, and has nonempty
interior around it in low-frequency directions. On $\mathcal K'\cap\mathcal C$ the
architecture transfers and gives a conditional bound.

Results 27–28 then prove the linear inequalities of result 23, for every pair at once,
from a single condition with a geometric reading: the cap is nowhere flatter than a circle
of the corridor's width. The proof reduces each condition to a forced harmonic oscillator
with zero initial data, whose kernel is nonnegative because the rotation angle is at most
$\pi/2$. Across twelve perturbations (RC) holds exactly when the conditions hold, on both
sides of the transition.

What this is not: a proof of optimality. The cross condition of result 23 is not covered
and is still only measured; the hypothesis class is not shown to contain every competitor;
and hypothesis (i) of result 25 remains numerical, though result 30 gives it an explicit
pointwise form. By result 19 bodies violating (RC) genuinely violate
$Q\ge\lvert\text{sofa}\rvert$, so the restriction is not a technicality.

## Layout

```
paper/niche_separation/   THE PAPER (LaTeX + PDF)
paper/PROGRAM.md          full research ledger, including every retraction
lean/MovingSofa/          Lean 4 development, 89 theorems, no sorry
lean/MAPPING.md           statement-to-declaration table, with per-axiom notes
algorithm/rigorous/ambi_* computations for the paper; every number is regenerated
                          by one of these

superseded, retained only because the archived release contained them, and each
marked WITHDRAWN in its own header:
paper/manuscript.tex, paper/OFFDIAG_RIGOROUS.tex, paper/UNIQUENESS.tex,
paper/figures/, algorithm/rigorous/{gerver_*,sigma_*}.py
```

## Lean

```bash
cd lean/MovingSofa && lake build
```

Lean 4.30, **no Mathlib**. Trigonometric quantities are carried as formal symbols
under sign or Pythagorean side conditions and arithmetic is over `Int`, so the
identities stay decidable. Instantiating those symbols at actual sines and cosines is a
separate Mathlib-track task and is **not** claimed. `#print axioms` reports nothing
beyond `propext` and `Quot.sound`, except `strip_covers_iff` and `cone_nu_iff`, which
also use `Classical.choice`. That list was checked by running `#print axioms` over every
theorem in the file.

## Method note

`paper/PROGRAM.md` records failed attempts and withdrawn claims alongside the results,
deliberately. Several intermediate findings here were artifacts of testing at a fixed
scale while the phenomenon lived at a shrinking one, or of checking a proxy (equal
areas) rather than the property (equal sets). Two claims were retracted on those
grounds and one sign error was found the same way. The ledger keeps them so the same
mistakes are not repeated.

## Superseded work

An earlier line of work in this repository aimed at *local* maximality of Gerver's and
Romik's sofas via second variation, and its results are **withdrawn**. Baek's theorem
gives global optimality for Gerver, and local optimality there was already available in
Gerver (1992), Romik (2018) and Den (2024). For $\Sigma$, the reconstruction that
approach certifies does not dominate the true area at second order; details, including
the two failure modes found (chords that are not constraint boundaries, and signed
Green sums evaluated on self-intersecting curves), are in `paper/PROGRAM.md`. Those two
failure modes are of independent interest to anyone computing area bounds from boundary
integrals.

## Citation

See `CITATION.cff`.

## License

MIT — see `LICENSE`.

## Comments

Comments, corrections, and pointers to errors are welcome — please open an issue.
