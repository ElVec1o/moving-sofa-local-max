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
| 14 | The one term with the wrong curvature: $\tfrac12\int(\alpha_1^-)^2=\tfrac\beta8-a_1(1-\cos\beta)+a_1^2(\beta-\tfrac12\sin2\beta)=0.0119502700\ldots$, supported exactly on $[0,\beta)$ | PROVED |
| 15 | **Optimality of $\Sigma$** | **not proved** |

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

*Remaining.* Two of the three terms in result 13 are convex quadratics in the support
function, which is what the generalised Mamikon theorem buys, so they give a concave
upper bound. The third is **subtracted**, hence contributes a convex term with the
wrong sign for concavity. Result 14 computes it exactly; it is supported precisely on
$[0,\beta)$, the phase where $\Sigma$ degenerates, and its support is exactly the
threshold $\sin t<1/(4a_1)$ of result 7. Whether $\lvert C_2\rvert-2\lvert N\rvert$ is
nonetheless concave is a Hessian computation on support-function perturbations and is
**not attempted**. Neither is the second half of the argument — that the three
geometric hypotheses of result 13 (the two sweeps are disjoint, injective, and cover)
hold for competitors and not only for $\Sigma$. Those hypotheses are *measured* for
$\Sigma$, not proved.

## Layout

```
paper/niche_separation/   the note (LaTeX + PDF)
paper/PROGRAM.md          full research ledger, including retractions
lean/MovingSofa/          Lean 4 development, 62 theorems, no sorry
lean/MAPPING.md           statement-to-declaration table, with per-axiom notes
algorithm/                computations (ambi_*, sigma_*, gerver_*)
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
also use `Classical.choice`.

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
