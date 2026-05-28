"""
gerver_constants.py
===================

Phase 1 of the rigorous local-maximality of Gerver project.

Encodes the exact transcendental system of Romik (2018) defining
Gerver's analytic moving sofa, solves it to >= 50 decimal digits in
mpmath, and computes Gerver's area A* to matching precision.

The 22-unknown system from Romik §4 is reduced via explicit
substitutions (symmetry identities + initial conditions) to a
13x13 nonlinear system whose only transcendental dependence is on
(phi, theta). It is then solved by multivariate Newton (mpmath
findroot) starting from the published 18-digit values of Romik's
Table 1.

The area A* is obtained by direct integration of the boundary of
Gerver's region S_x. Since S_x is bounded by pieces of the four
contact paths A(t), B(t), C(t), D(t) (each algebraic in
sin t, cos t and the 22 constants), the area integral can be done
piecewise with mpmath.quad.
"""

from __future__ import annotations

import mpmath as mp


# ---------------------------------------------------------------------
# Rotation matrix and its derivative
# ---------------------------------------------------------------------

def _Rt(t):
    """R_t = [[cos t, -sin t],[sin t, cos t]]"""
    c, s = mp.cos(t), mp.sin(t)
    return (c, -s, s, c)  # row-major 2x2


def _Rt_deriv(t):
    """d/dt R_t = [[-sin t, -cos t],[sin t? wait], cos t, -sin t]]
    Actually: R_t' = [[-sin t, -cos t],[ cos t, -sin t]]"""
    c, s = mp.cos(t), mp.sin(t)
    return (-s, -c, c, -s)


def _matvec2(M, v):
    a, b, c, d = M
    x, y = v
    return (a * x + b * y, c * x + d * y)


# ---------------------------------------------------------------------
# Closed-form solutions x_j(t) and their derivatives (Romik Thm 3)
# ---------------------------------------------------------------------
#
# x_j(t) = R_t * v_j(t) + kappa_j
# x_j'(t) = R_t' * v_j(t) + R_t * v_j'(t)
#

def _v1(t, a1, a2):
    c, s = mp.cos(t), mp.sin(t)
    return (a1 * c + a2 * s - 1, -a2 * c + a1 * s - mp.mpf('0.5'))


def _v1p(t, a1, a2):
    c, s = mp.cos(t), mp.sin(t)
    return (-a1 * s + a2 * c, a2 * s + a1 * c)


def _v2(t, b1, b2):
    return (-mp.mpf('0.25') * t * t + b1 * t + b2,
            mp.mpf('0.5') * t - b1 - 1)


def _v2p(t, b1, b2):
    return (-mp.mpf('0.5') * t + b1, mp.mpf('0.5'))


def _v3(t, c1, c2):
    return (c1 - t, c2 + t)


def _v3p(t, c1, c2):
    return (mp.mpf(-1), mp.mpf(1))


def _v4(t, d1, d2):
    return (-mp.mpf('0.5') * t + d1 - 1,
            -mp.mpf('0.25') * t * t + d1 * t + d2)


def _v4p(t, d1, d2):
    return (-mp.mpf('0.5'), -mp.mpf('0.5') * t + d1)


def _v5(t, e1, e2):
    c, s = mp.cos(t), mp.sin(t)
    return (e1 * c + e2 * s - mp.mpf('0.5'),
            -e2 * c + e1 * s - 1)


def _v5p(t, e1, e2):
    c, s = mp.cos(t), mp.sin(t)
    return (-e1 * s + e2 * c, e2 * s + e1 * c)


def _xj(t, vj_fun, vjp_fun, params, kappa):
    """Return (x_j(t), x_j'(t)) as 2-tuples."""
    v = vj_fun(t, *params)
    vp = vjp_fun(t, *params)
    R = _Rt(t)
    Rp = _Rt_deriv(t)
    Rv = _matvec2(R, v)
    Rpv = _matvec2(Rp, v)
    Rvp = _matvec2(R, vp)
    x = (Rv[0] + kappa[0], Rv[1] + kappa[1])
    xp = (Rpv[0] + Rvp[0], Rpv[1] + Rvp[1])
    return x, xp


# ---------------------------------------------------------------------
# Contact paths B(t), D(t) (needed for contact-transition equations)
# ---------------------------------------------------------------------
#
# B(t) = x(t) + <x'(t), mu_t> nu_t,
# D(t) = x(t) - <x'(t), nu_t> mu_t.
#
# mu_t = R_t (1,0)^T = (cos t, sin t)
# nu_t = R_t (0,1)^T = (-sin t, cos t)
#

def _B_of(x, xp, t):
    c, s = mp.cos(t), mp.sin(t)
    # <x', mu_t>
    dot = xp[0] * c + xp[1] * s
    # nu_t
    return (x[0] + dot * (-s), x[1] + dot * c)


def _D_of(x, xp, t):
    c, s = mp.cos(t), mp.sin(t)
    # <x', nu_t>
    dot = xp[0] * (-s) + xp[1] * c
    # subtract dot * mu_t
    return (x[0] - dot * c, x[1] - dot * s)


# ---------------------------------------------------------------------
# Apply Romik's explicit substitutions to compress the unknown vector
# ---------------------------------------------------------------------

def _expand(U):
    """Unpack the 13 free unknowns + derive the remaining 9 via
    Romik's symmetry / initial-condition identities.

    Free unknowns (vector U, length 13):
        phi, theta, a1, b1, b2, c1,
        k21, k22, k31, k32, k41, k42, k51

    Derived:
        a2     = -1/4
        e1     = a1
        e2     = 1/4
        d1     = pi/4 - b1
        d2     = b2 + (pi/4)*(2*b1 - pi/4)
        c2     = c1 - pi/2
        k11    = 1 - a1
        k12    = 1/4
        k52    = 1/4
    """
    (phi, theta, a1, b1, b2, c1,
     k21, k22, k31, k32, k41, k42, k51) = U
    quarter = mp.mpf('0.25')
    half = mp.mpf('0.5')
    pi4 = mp.pi / 4
    pi2 = mp.pi / 2
    a2 = -quarter
    e1 = a1
    e2 = quarter
    d1 = pi4 - b1
    d2 = b2 + pi4 * (2 * b1 - pi4)
    c2 = c1 - pi2
    k11 = 1 - a1
    k12 = quarter
    k52 = quarter
    return dict(
        phi=phi, theta=theta,
        a1=a1, a2=a2, b1=b1, b2=b2, c1=c1, c2=c2,
        d1=d1, d2=d2, e1=e1, e2=e2,
        k11=k11, k12=k12, k21=k21, k22=k22,
        k31=k31, k32=k32, k41=k41, k42=k42,
        k51=k51, k52=k52,
    )


# ---------------------------------------------------------------------
# Residual vector F(U): length 13
# ---------------------------------------------------------------------

def _residual_vec(U):
    p = _expand(U)
    phi = p['phi']; theta = p['theta']
    pi2 = mp.pi / 2
    t1 = phi
    t2 = theta
    t3 = pi2 - theta
    t4 = pi2 - phi

    k1 = (p['k11'], p['k12'])
    k2 = (p['k21'], p['k22'])
    k3 = (p['k31'], p['k32'])
    k4 = (p['k41'], p['k42'])
    k5 = (p['k51'], p['k52'])

    par1 = (p['a1'], p['a2'])
    par2 = (p['b1'], p['b2'])
    par3 = (p['c1'], p['c2'])
    par4 = (p['d1'], p['d2'])
    par5 = (p['e1'], p['e2'])

    x1_phi, x1p_phi = _xj(t1, _v1, _v1p, par1, k1)
    x2_phi, x2p_phi = _xj(t1, _v2, _v2p, par2, k2)

    x2_th, x2p_th = _xj(t2, _v2, _v2p, par2, k2)
    x3_th, x3p_th = _xj(t2, _v3, _v3p, par3, k3)

    x3_t3, x3p_t3 = _xj(t3, _v3, _v3p, par3, k3)
    x4_t3, x4p_t3 = _xj(t3, _v4, _v4p, par4, k4)

    x4_t4, x4p_t4 = _xj(t4, _v4, _v4p, par4, k4)
    x5_t4, x5p_t4 = _xj(t4, _v5, _v5p, par5, k5)

    # Contact transition: x1(phi) = B(pi/2 - theta) where B is evaluated
    # along the active piece x_4 (since pi/2 - theta is in phase 4).
    B_t3 = _B_of(x4_t3, x4p_t3, t3)

    res = []
    # 1-2: x1(phi) = x2(phi)
    res.append(x1_phi[0] - x2_phi[0])
    res.append(x1_phi[1] - x2_phi[1])
    # 3-4: x1'(phi) = x2'(phi)
    res.append(x1p_phi[0] - x2p_phi[0])
    res.append(x1p_phi[1] - x2p_phi[1])
    # 5-6: x2(theta) = x3(theta)
    res.append(x2_th[0] - x3_th[0])
    res.append(x2_th[1] - x3_th[1])
    # 7: x2'(theta) = x3'(theta), first component (second is dependent)
    res.append(x2p_th[0] - x3p_th[0])
    # 8-9: x3(pi/2 - theta) = x4(pi/2 - theta)
    res.append(x3_t3[0] - x4_t3[0])
    res.append(x3_t3[1] - x4_t3[1])
    # 10: x3'(pi/2 - theta) = x4'(pi/2 - theta), first component
    res.append(x3p_t3[0] - x4p_t3[0])
    # 11-12: x4(pi/2 - phi) = x5(pi/2 - phi)
    res.append(x4_t4[0] - x5_t4[0])
    res.append(x4_t4[1] - x5_t4[1])
    # 13: contact transition x1(phi) = B(pi/2 - theta), first component
    res.append(x1_phi[0] - B_t3[0])
    return res


def _residual_for_findroot(*U):
    """mpmath findroot calls f(*args). Wrap _residual_vec accordingly."""
    return tuple(_residual_vec(U))


# ---------------------------------------------------------------------
# High-precision solve
# ---------------------------------------------------------------------

# Romik Table 1 (18-digit seeds)
SEED = dict(
    phi   = mp.mpf("0.039177364790083641"),
    theta = mp.mpf("0.681301509382724894"),
    a1    = mp.mpf("1.210322422072688751"),
    b1    = mp.mpf("-0.527624598026784624"),
    b2    = mp.mpf("0.920258385160637622"),
    c1    = mp.mpf("0.626045522848465867"),
    k21   = mp.mpf("-0.919179292771593322"),
    k22   = mp.mpf("0.472406619750805465"),
    k31   = mp.mpf("-0.613763229430251668"),
    k32   = mp.mpf("0.889626479003221860"),
    k41   = mp.mpf("-0.308347166088910014"),
    k42   = mp.mpf("0.472406619750805465"),
    k51   = mp.mpf("-1.017204036787814585"),
)


def _seed_vec():
    return (SEED['phi'], SEED['theta'], SEED['a1'], SEED['b1'], SEED['b2'],
            SEED['c1'], SEED['k21'], SEED['k22'], SEED['k31'], SEED['k32'],
            SEED['k41'], SEED['k42'], SEED['k51'])


def solve_gerver_constants(working_dps: int = 60, verbose: bool = False):
    """Solve the 13x13 system to `working_dps` decimal digits."""
    old_dps = mp.mp.dps
    mp.mp.dps = working_dps + 20
    try:
        U0 = _seed_vec()
        # Re-cast seeds in current dps
        U0 = tuple(mp.mpf(str(u)) for u in U0)
        sol = mp.findroot(
            _residual_for_findroot, U0,
            tol=mp.mpf(10) ** (-working_dps - 5),
            solver="mnewton",
            maxsteps=200,
        )
        U = tuple(mp.mpf(sol[i]) for i in range(13))
        residuals = _residual_vec(U)
        residual_norm = max(abs(r) for r in residuals)
        if verbose:
            print(f"  Newton converged at working_dps={working_dps}")
            print(f"  ||F||_inf = {mp.nstr(residual_norm, 5)}")
        if residual_norm > mp.mpf(10) ** (-working_dps):
            raise RuntimeError(
                f"residual {residual_norm} exceeds tolerance 1e-{working_dps}"
            )
        return _expand(U), residual_norm
    finally:
        mp.mp.dps = old_dps


# ---------------------------------------------------------------------
# Cross-checks
# ---------------------------------------------------------------------

def check_identities(p, tol=None):
    """Verify symmetry identities consistent with Table 1 footnotes."""
    if tol is None:
        tol = mp.mpf(10) ** (-(mp.mp.dps - 10))
    checks = {
        'k42 - k22': p['k42'] - p['k22'],   # expect 0
        'a1 + k11 - 1': p['a1'] + p['k11'] - 1,  # expect 0
        'e1 - a1': p['e1'] - p['a1'],
        'e2 - 1/4': p['e2'] - mp.mpf('0.25'),
        'a2 + 1/4': p['a2'] + mp.mpf('0.25'),
        'k12 - 1/4': p['k12'] - mp.mpf('0.25'),
        'k52 - 1/4': p['k52'] - mp.mpf('0.25'),
        'c2 - (c1 - pi/2)': p['c2'] - (p['c1'] - mp.pi / 2),
    }
    return checks


# ---------------------------------------------------------------------
# Area A* by direct integration of the boundary
# ---------------------------------------------------------------------
#
# We compute |S_x| via Green's theorem applied to the rotation path x(t).
#
# A clean formula: by Romik §2, S_x is the intersection over t of
# rotated halfplanes; equivalently, the area equals
#
#    |S_x| = (1/2) * integral_0^{pi/2} || A(t) - B(t) ||^2 ... no.
#
# The cleanest approach: compute the four contact paths
#   A(t), B(t), C(t), D(t)
# Then S_x is bounded by these.  Using Romik's eq. (6)–(7) the area is
#
#    |S_x| = integral_0^{pi/2} (length-cross-section in mu_t direction) dt
#
# A simpler direct formula uses that the *top* boundary of S_x in the
# mu_t / nu_t frame at angle t is the segment from B(t) to A(t)
# (length 1), and the *bottom* is from D(t) to C(t).  The width-1
# pieces glue into S_x.  The signed area can be obtained by the
# Stokes/Green integral applied to the boundary curve formed by the
# contact paths.
#
# We use a direct approach: parameterise the upper boundary of the
# sofa by C(t) (the "outer" contact) and the lower boundary by D(t)
# and B(t), and integrate via Green's theorem in the lab frame.
#
# Easier: shift to "frame of the sofa" where the four contact points
# are simply the corners of the moving hallway. In that frame the
# four points trace the boundary of S_x. The area is then
#
#    |S_x| = (1/2) |closed-curve integral of x dy - y dx|
#
# over the boundary of S_x as traced by A, B, C, D as t runs 0..pi/2.

def _area_by_green(p, integrator_dps=None):
    """Area of Gerver's region S_x via Green's theorem on the boundary.

    The boundary of S_x is formed by pieces of the four contact paths
    A(t), B(t), C(t), D(t) for t in [0, pi/2], joined at endpoints.

    For Gerver's sofa the boundary, traversed counter-clockwise, is:
        - C(t),  t : 0 -> pi/2   (top side)
        - A(t),  t : pi/2 -> 0   (bottom side -- traversed reversed)
        - straight segments closing the ends? In fact A(0) = (1,0) and
          C(0) = (1,1) connect by a vertical unit segment; similarly
          at t=pi/2 by symmetry.

    Concretely we follow Romik's standard formulation: the area equals
        int_0^{pi/2} <A(t) - D(t), nu_t> dt
    but this is for the unit hallway intersected with the cross-section.
    Cleanest verified formula (matches numerical evaluation): the area
    of S_x can be computed via Green on the closed boundary, but for
    a numerically robust test we instead use the *cross-sectional*
    formula:

        |S_x|  =  int_0^{pi/2}  L(t)  dt

    where L(t) is the length of the intersection of S_x with the line
    through x(t) in direction mu_t. By construction of S_x this
    length is 1 (the hallway is width 1). That gives area pi/2, which
    is WRONG for S_x (it gives the swept hallway area, not the sofa).

    So we use direct boundary-Green integration as the only honest
    route, set up below.
    """
    raise NotImplementedError("use _area_green_direct instead")


def _xt_xtp(t, p):
    """Return the active piece x(t), x'(t) at parameter t in [0, pi/2]."""
    phi = p['phi']; theta = p['theta']
    pi2 = mp.pi / 2
    if t <= phi:
        return _xj(t, _v1, _v1p, (p['a1'], p['a2']),
                   (p['k11'], p['k12']))
    elif t <= theta:
        return _xj(t, _v2, _v2p, (p['b1'], p['b2']),
                   (p['k21'], p['k22']))
    elif t <= pi2 - theta:
        return _xj(t, _v3, _v3p, (p['c1'], p['c2']),
                   (p['k31'], p['k32']))
    elif t <= pi2 - phi:
        return _xj(t, _v4, _v4p, (p['d1'], p['d2']),
                   (p['k41'], p['k42']))
    else:
        return _xj(t, _v5, _v5p, (p['e1'], p['e2']),
                   (p['k51'], p['k52']))


def _Ct(t, p):
    x, xp = _xt_xtp(t, p)
    c, s = mp.cos(t), mp.sin(t)
    # <x', nu_t>
    dot = xp[0] * (-s) + xp[1] * c
    # C = x - dot * mu_t + nu_t
    return (x[0] - dot * c + (-s), x[1] - dot * s + c)


def _At(t, p):
    x, xp = _xt_xtp(t, p)
    c, s = mp.cos(t), mp.sin(t)
    dot = xp[0] * c + xp[1] * s
    # A = x + dot * nu_t + mu_t
    return (x[0] + dot * (-s) + c, x[1] + dot * c + s)


def _Bt(t, p):
    x, xp = _xt_xtp(t, p)
    c, s = mp.cos(t), mp.sin(t)
    dot = xp[0] * c + xp[1] * s
    return (x[0] + dot * (-s), x[1] + dot * c)


def _Dt(t, p):
    x, xp = _xt_xtp(t, p)
    c, s = mp.cos(t), mp.sin(t)
    dot = xp[0] * (-s) + xp[1] * c
    return (x[0] - dot * c, x[1] - dot * s)


# ---------------------------------------------------------------------
# Analytic derivatives of contact paths
# ---------------------------------------------------------------------
#
# A(t) = x(t) + <x',mu_t> nu_t + mu_t
# B(t) = x(t) + <x',mu_t> nu_t
# C(t) = x(t) - <x',nu_t> mu_t + nu_t
# D(t) = x(t) - <x',nu_t> mu_t
#
# For Romik's solutions, x_j(t) = R_t v_j(t) + kappa_j. Differentiation
# gives x_j'' = R_t'' v_j + 2 R_t' v_j' + R_t v_j''. We compute these
# components symbolically below to obtain analytic derivatives of
# A, B, C, D, avoiding finite differences.

def _v1pp(t, a1, a2):
    c, s = mp.cos(t), mp.sin(t)
    # v_1 = (a1 c + a2 s - 1, -a2 c + a1 s - 1/2)
    # v_1'  = (-a1 s + a2 c,  a2 s + a1 c)
    # v_1'' = (-a1 c - a2 s,  a2 c - a1 s)
    return (-a1 * c - a2 * s, a2 * c - a1 * s)


def _v2pp(t, b1, b2):
    return (-mp.mpf('0.5'), mp.mpf(0))


def _v3pp(t, c1, c2):
    return (mp.mpf(0), mp.mpf(0))


def _v4pp(t, d1, d2):
    return (mp.mpf(0), -mp.mpf('0.5'))


def _v5pp(t, e1, e2):
    c, s = mp.cos(t), mp.sin(t)
    # v_5 = (e1 c + e2 s - 1/2, -e2 c + e1 s - 1)
    # v_5'  = (-e1 s + e2 c,  e2 s + e1 c)
    # v_5'' = (-e1 c - e2 s,  e2 c - e1 s)
    return (-e1 * c - e2 * s, e2 * c - e1 * s)


def _Rt_dd(t):
    """R_t'' = -R_t"""
    c, s = mp.cos(t), mp.sin(t)
    return (-c, s, -s, -c)


def _xj_full(t, vj, vjp, vjpp, params, kappa):
    """Return (x_j(t), x_j'(t), x_j''(t))."""
    v = vj(t, *params)
    vp = vjp(t, *params)
    vpp = vjpp(t, *params)
    R = _Rt(t); Rp = _Rt_deriv(t); Rpp = _Rt_dd(t)
    Rv = _matvec2(R, v); Rpv = _matvec2(Rp, v); Rppv = _matvec2(Rpp, v)
    Rvp = _matvec2(R, vp); Rpvp = _matvec2(Rp, vp)
    Rvpp = _matvec2(R, vpp)
    x = (Rv[0] + kappa[0], Rv[1] + kappa[1])
    xp = (Rpv[0] + Rvp[0], Rpv[1] + Rvp[1])
    xpp = (Rppv[0] + 2 * Rpvp[0] + Rvpp[0],
           Rppv[1] + 2 * Rpvp[1] + Rvpp[1])
    return x, xp, xpp


def _xt_full(t, p):
    """Return x(t), x'(t), x''(t) using the active phase."""
    phi = p['phi']; theta = p['theta']
    pi2 = mp.pi / 2
    if t <= phi:
        return _xj_full(t, _v1, _v1p, _v1pp, (p['a1'], p['a2']),
                        (p['k11'], p['k12']))
    elif t <= theta:
        return _xj_full(t, _v2, _v2p, _v2pp, (p['b1'], p['b2']),
                        (p['k21'], p['k22']))
    elif t <= pi2 - theta:
        return _xj_full(t, _v3, _v3p, _v3pp, (p['c1'], p['c2']),
                        (p['k31'], p['k32']))
    elif t <= pi2 - phi:
        return _xj_full(t, _v4, _v4p, _v4pp, (p['d1'], p['d2']),
                        (p['k41'], p['k42']))
    else:
        return _xj_full(t, _v5, _v5p, _v5pp, (p['e1'], p['e2']),
                        (p['k51'], p['k52']))


def _contact_with_deriv(t, p, which):
    """Analytic value and derivative of contact path A/B/C/D at t."""
    x, xp, xpp = _xt_full(t, p)
    c, s = mp.cos(t), mp.sin(t)
    mu = (c, s);   mup = (-s, c)
    nu = (-s, c);  nup = (-c, -s)
    if which == 'B':
        # B = x + <x',mu> nu
        d  = xp[0] * mu[0] + xp[1] * mu[1]
        dp = xpp[0] * mu[0] + xpp[1] * mu[1] + xp[0] * mup[0] + xp[1] * mup[1]
        val = (x[0] + d * nu[0], x[1] + d * nu[1])
        dval = (xp[0] + dp * nu[0] + d * nup[0],
                xp[1] + dp * nu[1] + d * nup[1])
    elif which == 'A':
        # A = x + <x',mu> nu + mu
        d  = xp[0] * mu[0] + xp[1] * mu[1]
        dp = xpp[0] * mu[0] + xpp[1] * mu[1] + xp[0] * mup[0] + xp[1] * mup[1]
        val = (x[0] + d * nu[0] + mu[0], x[1] + d * nu[1] + mu[1])
        dval = (xp[0] + dp * nu[0] + d * nup[0] + mup[0],
                xp[1] + dp * nu[1] + d * nup[1] + mup[1])
    elif which == 'D':
        # D = x - <x',nu> mu
        d  = xp[0] * nu[0] + xp[1] * nu[1]
        dp = xpp[0] * nu[0] + xpp[1] * nu[1] + xp[0] * nup[0] + xp[1] * nup[1]
        val = (x[0] - d * mu[0], x[1] - d * mu[1])
        dval = (xp[0] - dp * mu[0] - d * mup[0],
                xp[1] - dp * mu[1] - d * mup[1])
    elif which == 'C':
        # C = x - <x',nu> mu + nu
        d  = xp[0] * nu[0] + xp[1] * nu[1]
        dp = xpp[0] * nu[0] + xpp[1] * nu[1] + xp[0] * nup[0] + xp[1] * nup[1]
        val = (x[0] - d * mu[0] + nu[0], x[1] - d * mu[1] + nu[1])
        dval = (xp[0] - dp * mu[0] - d * mup[0] + nup[0],
                xp[1] - dp * mu[1] - d * mup[1] + nup[1])
    else:
        raise ValueError(which)
    return val, dval


def _xprime_full(t, p):
    """Return x(t), x'(t) as a tuple-of-tuples (for the inner-corner
    trajectory; used as a boundary arc of S_x for t in [phi, pi/2-phi])."""
    x, xp, _ = _xt_full(t, p)
    return x, xp


def gerver_area(p):
    """Compute |S_x| via Green's theorem on the CCW boundary of S_x.

    The boundary of S_x for Gerver's sofa, traversed CCW, is built from
    five arcs joined by straight segments at y = 0 or y = 1:

      arc 1: A(t),       t :         0   ->   pi/2     [upper-right]
      seg : straight from A(pi/2) to C(0)              [top at y = 1]
      arc 2: C(t),       t :         0   ->   pi/2     [upper-left]
      seg : straight from C(pi/2) to D(0)              [bottom-left at y=0]
      arc 3: D(t),       t :         0   ->   theta    [left side of notch, ascending]
      arc 4: x(t),       t :       phi   ->   pi/2-phi [the inner corner trajectory]
             traversed in reverse (since x(phi) joins to where D ends?
             NO -- x(phi) joins B(pi/2 - theta) by the contact eq.,
             and x(pi/2-phi) joins D(theta).)

             Concretely the CCW order of the notch boundary is
             (left to right of the open notch mouth, sofa above):
                D(t)  for t : 0 -> theta   ends at D(theta)
                x(t)  for t : pi/2-phi -> phi  (reverse), from
                                D(theta)-equivalent down to B(pi/2-theta)
                B(t)  for t : pi/2-theta -> pi/2 ends at B(pi/2)
             Wait -- but x(pi/2-phi) and D(theta) are not the same point
             in general.  Check: x(pi/2-phi) = (-1.2246, 0.05519);
             D(theta) = (-1.2246, 0.05519).  YES they coincide (this is
             exactly the contact transition x5(pi/2-phi)=D(theta) which is
             eq. 44 in Romik).  Similarly x(phi)=B(pi/2-theta) (eq. 43).

             So the CCW boundary of the notch is:
                ... straight (-2.23,0) -> D(0)=(-1.42, 0)
                D(t),  t : 0 -> theta            ends at D(theta) = x(pi/2-phi)
                x(t),  t : pi/2 - phi -> phi     (reversed) ends at x(phi) = B(pi/2-theta)
                B(t),  t : pi/2-theta -> pi/2    ends at B(pi/2) = (0.19, 0)
                straight (0.19,0) -> A(0)=(1, 0)

      seg : straight from B(pi/2) to A(0)              [right bottom at y=0]

    Area = (1/2) * sum int(x dy - y dx) over all arcs and segments,
    with signs adjusted for reverse traversal.
    """
    pi2 = mp.pi / 2
    half = mp.mpf('0.5')

    def integrand(P, t):
        v, dv = _contact_with_deriv(t, p, P)
        return v[0] * dv[1] - v[1] * dv[0]

    def x_integrand(t):
        x, xp, _ = _xt_full(t, p)
        return x[0] * xp[1] - x[1] * xp[0]

    nodes_full = [0, p['phi'], p['theta'], pi2 - p['theta'],
                  pi2 - p['phi'], pi2]
    nodes_D = [0, p['phi'], p['theta']]
    nodes_B = [pi2 - p['theta'], pi2 - p['phi'], pi2]
    nodes_x = [p['phi'], p['theta'], pi2 - p['theta'], pi2 - p['phi']]

    # CCW: A(t), 0->pi/2 (upper-right arc, sofa interior on left)
    IA = mp.quad(lambda t: integrand('A', t), nodes_full)
    # Then top edge straight from A(pi/2) to C(0).
    # Then C(t), 0->pi/2 (upper-left arc)
    IC = mp.quad(lambda t: integrand('C', t), nodes_full)
    # Then bottom-left straight from C(pi/2) to D(0).
    # Then D(t), 0->theta (notch left side going up)
    ID = mp.quad(lambda t: integrand('D', t), nodes_D)
    # Then x(t) reversed: t from pi/2-phi to phi.
    # Reversal flips the sign of the integrand integration:
    #   int_{pi/2-phi}^{phi} f(t) dt = - int_{phi}^{pi/2-phi} f(t) dt
    Ix = -mp.quad(x_integrand, nodes_x)
    # Then B(t), pi/2-theta -> pi/2  (notch right side going down)
    IB = mp.quad(lambda t: integrand('B', t), nodes_B)
    # Then bottom-right straight from B(pi/2) to A(0).

    # Endpoints for the straight segments
    A_pi2 = _contact_with_deriv(pi2, p, 'A')[0]
    C_0   = _contact_with_deriv(mp.mpf(0), p, 'C')[0]
    C_pi2 = _contact_with_deriv(pi2, p, 'C')[0]
    D_0   = _contact_with_deriv(mp.mpf(0), p, 'D')[0]
    B_pi2 = _contact_with_deriv(pi2, p, 'B')[0]
    A_0   = _contact_with_deriv(mp.mpf(0), p, 'A')[0]

    def seg(P0, P1):
        return half * (P0[0] * P1[1] - P1[0] * P0[1])

    S = half * (IA + IC + ID + Ix + IB)
    S += seg(A_pi2, C_0)     # top
    S += seg(C_pi2, D_0)     # bottom-left straight (both at y=0, contributes 0)
    S += seg(B_pi2, A_0)     # bottom-right straight (both at y=0, contributes 0)
    return S
