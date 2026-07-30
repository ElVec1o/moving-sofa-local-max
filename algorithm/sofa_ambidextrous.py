"""
sofa_ambidextrous.py  (compatibility shim)
==========================================

The ambidextrous-hallway geometry lives in ``sofa_ambidextrous_v2.py``
(the corrected formulation: mirror across y = 1/2, the corridor
centerline, rather than across y = 0).

Several modules -- notably ``sofa_romik2017_reference.py`` -- still
import the historical names

    from sofa_ambidextrous import HALLWAY_L, HALLWAY_R

This shim re-exports those names from the v2 module so those imports
resolve.  Note: in the modules that drive the certified Hessian /
coercivity computations (``romik_hessian.py``), these two objects are
imported transitively but are referenced only inside the *diagnostic*
``__main__`` block of ``sofa_romik2017_reference.py``; the core
trajectory and area routines build their own hallway polygon.  This
shim therefore has no effect on any certified numeric output.
"""

from __future__ import annotations

from sofa_ambidextrous_v2 import (
    HALLWAY_L,
    HALLWAY_R_CORRECT as HALLWAY_R,
)

__all__ = ["HALLWAY_L", "HALLWAY_R"]
