"""Thin LAPACK front-end for the Rust assembler (sigma_struct.rs)."""
import subprocess, sys, os, math
import numpy as np
K = int(sys.argv[1]); nq = sys.argv[2] if len(sys.argv) > 2 else "0"
env = dict(os.environ, DUMP="1")
out = subprocess.run(["./sigma_struct", str(K), nq], capture_output=True,
                     text=True, env=env).stdout.split("\n")
n = int(out[0])
Q = np.array([[float(x) for x in out[1+i].split()] for i in range(n)])
Q = 0.5*(Q+Q.T)
ks = np.array([k for c in (0, 1) for k in range(1, K+1)], float)
for name, g in (("L^2", np.full(n, math.pi/4)),
                ("H^1", math.pi/4*(1+4*ks*ks))):
    S = np.diag(1/np.sqrt(g))
    ev = np.linalg.eigvalsh(S@Q@S)
    tag = f"NEG DEF m={-ev.max():.6f}" if ev.max() < 0 else "NOT neg def"
    print(f"  K={K:3d}  {name}: max={ev.max():+.6f} min={ev.min():+.4f}  {tag}")
