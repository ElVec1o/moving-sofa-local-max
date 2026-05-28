"""
algorithm.rigorous — validated-arithmetic infrastructure for the
rigorous local-maximality program.

Subpackage layout:
  gerver_constants.py    — Gerver's transcendental constants in mpmath
  gerver_trajectory.py   — Gerver's corner trajectory c_G(theta), high precision
  gerver_arb.py          — Ball-arithmetic (arb) certified enclosures
  second_variation.py    — δ²F at c_G as a Sobolev-bounded operator (Phase 2)
  symmetry_quotient.py   — modding out the rigid-motion zero modes (Phase 3)
  tail_bound.py          — operator-norm bounds on the Fourier tail (Phase 4)
"""
