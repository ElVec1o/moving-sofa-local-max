# Strict local maximality of Gerver's moving sofa

A computer-assisted argument that Joseph Gerver's 1992 candidate sofa
$c_G$ is a strict local maximum of the moving-sofa area functional on
the Sobolev space $H^2([0, \pi/2]; \mathbb{R}^2)$ of corner
trajectories, modulo translation symmetry.

## Result (summary)

> Conditional on the existence of a finite trilinear-form bound $K_3$
> for $D^3F$ at $c_G$ and on the working cross-term estimate stated
> in the proof, there exist $\delta \ge 0.0456$ and $m \ge 4.34$ such
> that for every $\eta \in H^2$ with $\|\eta\|_{H^2} \le \delta$ and
> $\eta \perp V_0$,
>
> $$F[c_G + \eta] \le F[c_G] - \frac{m}{2}\|\eta\|_{H^2}^2 + \frac{K_3}{6}\|\eta\|_{H^2}^3.$$

The result targets Open Problem 1 of Romik (2018), which asks for a
proof that Gerver's sofa is a local maximum of the area functional.

## Honest scope

This is a partial result, not a full computer-assisted proof. Three
items remain open and are flagged throughout the manuscript:

1. **Floating-point Hessian.** The finite-dimensional second-variation
   matrix is evaluated with `shapely` (floating-point polygon
   intersection), not interval arithmetic. The truncated coercivity
   constant $m_N \ge 4.6035$ is enclosed at 128-bit precision by three
   independent post-hoc methods, but the underlying Hessian entries
   are not interval-certified.

2. **Cross-term placeholder.** The coupling
   $\|Q_{NT}\|_{H^2 \to H^2}$ between low-frequency and high-frequency
   Fourier modes is bounded by a conservative numerical placeholder
   $\le 0.05$. An empirical probe gives a Frobenius estimate
   $\approx 0.022$; an analytic bound is left for follow-up work.

3. **Q_jump empirical.** The second variation decomposes as
   $Q = Q_{\text{smooth}} + Q_{\text{jump}}$. Lemma 8 characterizes
   $Q_{\text{smooth}}$ analytically (the per-arc structural identity:
   no $\|\eta''\|^2$ principal symbol). $Q_{\text{jump}}$ at the four
   contact-transition breakpoints is captured only empirically by the
   polygon Hessian computation; the empirical sum-rule excess
   $\approx 2.7\times$ at moderate $k$ is consistent with the
   shape-derivative structure but is not derived in closed form here.

## Repository layout

```
.
├── paper/
│   ├── manuscript.tex          main paper
│   ├── manuscript.pdf          compiled, 26 pages
│   ├── UNIQUENESS.tex          uniqueness appendix
│   ├── OFFDIAG_RIGOROUS.tex    off-diagonal Hilbert-inequality appendix
│   └── figures/
├── algorithm/
│   ├── moving_sofa_tools.py    L-hallway feasibility library
│   ├── sofa_*.py               candidate constructions, BVP solver, variants
│   ├── test_moving_sofa.py     reference test suite
│   └── rigorous/               certified-arithmetic experiments
│        ├── gerver_constants.py     60-digit certified Gerver constants
│        ├── gerver_arb.py           arb interval enclosures
│        ├── second_variation.py     Hessian
│        ├── phase4_full_theorem.py  truncated coercivity m_N
│        ├── F_richardson_*.py       Richardson-extrapolated F[c]
│        ├── hypV_sweep.py           eigenvalue-growth empirical sweep
│        ├── k3_*.py                 K_3 Lipschitz bounds
│        ├── sympy_lemma10_2.py      symbolic Lemma 8 cancellation
│        ├── phase1a_cross_term.py   cross-term diagnostic
│        ├── phase1b_K3_breakpoint.py  K_3 breakpoint blow-up probe
│        └── phase2a_lemma8_check.py   smooth/jump sum-rule diagnostic
└── lean/                       Lean 4 skeleton (structures only)
```

## Building the paper

```bash
cd paper
pdflatex manuscript.tex
pdflatex manuscript.tex
```

## Reproducing the numerical experiments

```bash
pip install mpmath numpy matplotlib python-flint sympy shapely
python algorithm/rigorous/gerver_constants.py
python algorithm/rigorous/phase4_full_theorem.py
python algorithm/rigorous/hypV_sweep.py
python algorithm/rigorous/phase1a_cross_term.py
python algorithm/rigorous/phase1b_K3_breakpoint.py
python algorithm/rigorous/phase2a_lemma8_check.py
```

## Citation

See `CITATION.cff`.

## License

MIT — see `LICENSE`.

## Comments

Comments, corrections, and pointers to errors are welcome — please
open an issue.
