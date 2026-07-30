# Gerver's Sofa — Exact Formulas from Romik (2018)

Primary source: **Dan Romik, "Differential equations and exact solutions in the moving sofa problem", Experimental Mathematics 27 (2018), 316–330** (arXiv:1606.08111). Section/equation numbers below refer to the arXiv v2 PDF.

## 0. Setup and conventions (Romik §2)

Hallway $L = L_{\text{horiz}}\cup L_{\text{vert}}$ with unit width. Rotation matrix and moving frame:
$$
R_t = \begin{pmatrix}\cos t & -\sin t\\ \sin t & \cos t\end{pmatrix},\qquad
\mu_t = R_t\begin{pmatrix}1\\0\end{pmatrix},\quad
\nu_t = R_t\begin{pmatrix}0\\1\end{pmatrix}.
$$
A **rotation path** is $x:[0,\pi/2]\to\mathbb{R}^2$ with $x(0)=(0,0)^\top$; it is the trajectory of the inner corner in the frame of the sofa. The associated shape $S_x$ is given by (8).

Four **contact paths** (Theorem 1, eqs. (9)–(12)):
$$
\begin{aligned}
A(t) &= x(t) + \langle x'(t),\mu_t\rangle\,\nu_t + \mu_t,\\
B(t) &= x(t) + \langle x'(t),\mu_t\rangle\,\nu_t,\\
C(t) &= x(t) - \langle x'(t),\nu_t\rangle\,\mu_t + \nu_t,\\
D(t) &= x(t) - \langle x'(t),\nu_t\rangle\,\mu_t.
\end{aligned}
$$

## 1. The six ODEs (Romik Theorem 2, eqs. ODE1–ODE6)

Each ODE governs a phase determined by which contact set $\Gamma_x(t)\subset\{x,A,B,C,D\}$ is active.

$$
\text{(ODE1) }\Gamma=\{A,C,D\}:\quad x''(t)=R_t\!\begin{pmatrix}-1\\-1/2\end{pmatrix}+\begin{pmatrix}2\sin t & -2\cos t\\ 2\cos t & 2\sin t\end{pmatrix}x'(t)
$$
$$
\text{(ODE2) }\Gamma=\{x,A,C,D\}:\quad x''(t)=R_t\!\begin{pmatrix}-1\\-1/2\end{pmatrix}+\begin{pmatrix}\sin t & -\cos t\\ \tfrac32\cos t & \tfrac32\sin t\end{pmatrix}x'(t)
$$
$$
\text{(ODE3) }\Gamma=\{x,A,C\}:\quad x''(t)=R_t\!\begin{pmatrix}-1\\-1\end{pmatrix}+\begin{pmatrix}\sin t & -\cos t\\ \cos t & \sin t\end{pmatrix}x'(t)
$$
$$
\text{(ODE4) }\Gamma=\{x,A,B,C\}:\quad x''(t)=R_t\!\begin{pmatrix}-1/2\\-1\end{pmatrix}+\begin{pmatrix}\tfrac32\sin t & -\tfrac32\cos t\\ \cos t & \sin t\end{pmatrix}x'(t)
$$
$$
\text{(ODE5) }\Gamma=\{A,B,C\}:\quad x''(t)=R_t\!\begin{pmatrix}-1/2\\-1\end{pmatrix}+\begin{pmatrix}2\sin t & -2\cos t\\ 2\cos t & 2\sin t\end{pmatrix}x'(t)
$$
**(ODE6)** is not used for Gerver's sofa. It IS the equation of the middle phase of
Romik's AMBIDEXTROUS sofa $\Sigma$, and it is not of the same shape as ODE1--ODE5
(those are $x''=R_t b+M(t)x'$ with no $x$ term). Derived from SOL6 below and
confirmed numerically to $5.6\cdot10^{-15}$:

$$
\text{(ODE6)}\quad x''(t)=2Jx'(t)+\tfrac34\bigl(x(t)-\kappa_6\bigr)-\tfrac14 R_t\begin{pmatrix}1\\1\end{pmatrix},
\qquad J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

In complex form ($J\leftrightarrow i$) the homogeneous part is
$z''-2iz'-\tfrac34 z=0$, with characteristic roots $\lambda=i/2$ and $3i/2$. This
is why SOL6 contains $\cos(t/2)$ and why $c_y(t)-\tfrac12$ contains $\sin(3t/2)$:
**the two half-integer angles throughout the $\Sigma$ formulas are the two
characteristic exponents of ODE6.**

## 2. Closed-form solutions (Romik Theorem 3, SOL1–SOL5)

$$
x_1(t)=R_t\!\begin{pmatrix}a_1\cos t+a_2\sin t-1\\ -a_2\cos t+a_1\sin t-\tfrac12\end{pmatrix}+\kappa_1
$$
$$
x_2(t)=R_t\!\begin{pmatrix}-\tfrac14 t^2+b_1 t+b_2\\ \tfrac12 t-b_1-1\end{pmatrix}+\kappa_2
$$
$$
x_3(t)=R_t\!\begin{pmatrix}c_1-t\\ c_2+t\end{pmatrix}+\kappa_3
$$
$$
x_4(t)=R_t\!\begin{pmatrix}-\tfrac12 t+d_1-1\\ -\tfrac14 t^2+d_1 t+d_2\end{pmatrix}+\kappa_4
$$
$$
x_5(t)=R_t\!\begin{pmatrix}e_1\cos t+e_2\sin t-\tfrac12\\ -e_2\cos t+e_1\sin t-1\end{pmatrix}+\kappa_5
$$
with $\kappa_j=(\kappa_{j,1},\kappa_{j,2})^\top$ and scalar constants $a_i,b_i,c_i,d_i,e_i$.

**SOL6** (missing from Romik's Theorem 3 list above, which covers SOL1--SOL5; it is
the ambidextrous solution and the middle phase of $\Sigma$):
$$
x_6(t)=R_t\!\begin{pmatrix}f_1\cos\frac t2+f_2\sin\frac t2-1\\ -f_2\cos\frac t2+f_1\sin\frac t2-1\end{pmatrix}+\kappa_6,
\qquad \kappa_6=\Bigl(1-\tfrac43 a_1,\ \tfrac12\Bigr),\quad f_2=(1-\sqrt2)f_1,
$$
with (derived from the junction $x_1(\beta)=x_6(\beta)$; Romik tabulates only the
decimal $1.202938908156911389$)
$$
f_1=\frac{\tfrac43\,a_1\cos\beta}{\cos\frac\beta2+(1-\sqrt2)\sin\frac\beta2}
   =1.202938908156911389070223\ldots
$$

$\Sigma$'s phase structure is SOL1 on $[0,\beta)$, SOL6 on $[\beta,\pi/2-\beta]$,
SOL5 on $(\pi/2-\beta,\pi/2]$.

## 3. The defining system (Romik §4, eqs. (23)–(44))

**Phase structure** (eq. 24): there exist $0<\varphi<\theta<\pi/4$ such that
$$
\Gamma_x(t)=\begin{cases}\{A,C,D\} & 0<t<\varphi\\ \{x,A,C,D\} & \varphi\le t<\theta\\ \{x,A,C\} & \theta\le t\le \pi/2-\theta\\ \{x,A,B,C\} & \pi/2-\theta<t\le\pi/2-\varphi\\ \{A,B,C\} & \pi/2-\varphi<t<\pi/2\end{cases}
$$
so $x(t)=x_j(t)$ on the $j$-th interval. There are **22 unknowns**: $\varphi,\theta$, the ten $\kappa_{j,\cdot}$, and $a_i,b_i,c_i,d_i,e_i$ ($i=1,2$).

**Constraints (linear in everything except $\varphi,\theta$):**

Symmetry (eqs. 27–31):
$$
e_1=a_1,\quad e_2=-a_2,\quad d_1=\tfrac{\pi}{4}-b_1,\quad d_2=b_2+\tfrac{\pi}{4}\!\bigl(2b_1-\tfrac{\pi}{4}\bigr),\quad c_2=c_1-\tfrac{\pi}{2}.
$$

Initial condition $A(0)=(1,0)^\top$, $x(0)=0$ (eqs. 32–34):
$$
\kappa_{1,1}=1-a_1,\quad \kappa_{1,2}=\tfrac14,\quad a_2=-\tfrac14.
$$

$C^1$-gluing at the four phase boundaries (eqs. 35–42, two are redundant):
$$
x_1(\varphi)=x_2(\varphi),\ x_1'(\varphi)=x_2'(\varphi),\ x_2(\theta)=x_3(\theta),\ x_2'(\theta)=x_3'(\theta),
$$
$$
x_3(\tfrac{\pi}{2}-\theta)=x_4(\tfrac{\pi}{2}-\theta),\ x_3'(\tfrac{\pi}{2}-\theta)=x_4'(\tfrac{\pi}{2}-\theta),\ x_4(\tfrac{\pi}{2}-\varphi)=x_5(\tfrac{\pi}{2}-\varphi).
$$

Contact-set transition (eqs. 43–44, second redundant):
$$
x_1(\varphi)=B(\pi/2-\theta),\qquad x_5(\pi/2-\varphi)=D(\theta).
$$

Total: 28 scalar equations, 6 redundant, leaving **22 independent equations in 22 unknowns**. The system is nonlinear **only in $(\varphi,\theta)$**; the other 20 unknowns are linear, so eliminating them yields a **transcendental system of two equations in $(\varphi,\theta)$** that is solved numerically.

## 4. Numerical solution (Romik Table 1)

To the precision Romik prints:

| Constant | Value | Constant | Value |
|---|---|---|---|
| $\varphi$ | $0.039177364790083641\ldots$ | $\theta$ | $0.681301509382724894\ldots$ |
| $a_1$ | $1.210322422072688751\ldots$ | $a_2$ | $-1/4$ |
| $b_1$ | $-0.527624598026784624\ldots$ | $b_2$ | $0.920258385160637622\ldots$ |
| $c_1$ | $0.626045522848465867\ldots$ | $c_2$ | $-0.944750803946430751\ldots$ |
| $d_1$ | $1.313022761424232933\ldots$ | $d_2$ | $-0.525382670414554437\ldots$ |
| $e_1$ | $1.210322422072688751\ldots$ | $e_2$ | $1/4$ |
| $\kappa_{1,1}$ | $-0.210322422072688751\ldots$ | $\kappa_{1,2}$ | $1/4$ |
| $\kappa_{2,1}$ | $-0.919179292771593322\ldots$ | $\kappa_{2,2}$ | $0.472406619750805465\ldots$ |
| $\kappa_{3,1}$ | $-0.613763229430251668\ldots$ | $\kappa_{3,2}$ | $0.889626479003221860\ldots$ |
| $\kappa_{4,1}$ | $-0.308347166088910014\ldots$ | $\kappa_{4,2}$ | $0.472406619750805465\ldots$ |
| $\kappa_{5,1}$ | $-1.017204036787814585\ldots$ | $\kappa_{5,2}$ | $1/4$ |

Note: $a_1=e_1=\kappa_{1,1}+1$, $\kappa_{4,2}=\kappa_{2,2}$, $\kappa_{5,2}=\kappa_{1,2}=1/4$ — consistent with the symmetry relations.

## 5. Area

Romik does **not** print a closed-form for $|G|$; the computation is delegated to Section 8 of the `MovingSofas.nb` package. The published value (Romik §1, p. 4 and end of §4):
$$
A^* = |G| = 2.21953166\ldots
$$
The area is computed as a finite sum of definite integrals of elementary expressions (since $S_x$ is bounded by pieces of the contact paths, each of which is algebraic in $\sin t,\cos t$, polynomials in $t$, and the constants of Table 1). No algebraic closed form is known.

## 6. Trajectory of the inner corner $c_G(\theta)$

This is exactly the rotation path $x(t)$ above, glued from $x_1,\ldots,x_5$ on the five intervals of (24). Sign convention: $t$ is the **rotation angle** of the hallway, $t\in[0,\pi/2]$; the inner corner of the hallway, expressed in the frame of the sofa, is $x(t)$. In Romik's coordinates the sofa moves from $L_{\text{horiz}}$ (positive-$x$ half) into $L_{\text{vert}}$ (positive-$y$ half).

The trajectory satisfies the ODE system of §1 piecewise, with $x(0)=(0,0)^\top$, $A(0)=(1,0)^\top$, and the gluing/symmetry conditions of §3.

## Cross-references

- Companion Mathematica package: `MovingSofas.nb` on https://www.math.ucdavis.edu/~romik/movingsofa/ — Section 6 (numerical FindRoot), Section 7 (symbolic reduction to 2 equations in $\varphi,\theta$), Section 8 (high-precision area).
- Baek (2024), arXiv:2411.19826, cites $|G|=2.2195\ldots$ as Gerver's lower bound and proves it equals $\alpha_{\max}$.
- Original: J. L. Gerver, *Geom. Dedicata* **42** (1992), 267–283.
