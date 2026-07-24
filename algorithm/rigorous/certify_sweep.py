"""(F3) FULL CERTIFIED SWEEP: every entry of the K=16 frozen block by rigorous
interval quadrature. Checkpointed (JSON per row); resume by re-running.
Then re-runs the minor certification with the CERTIFIED ball matrix.
Run: python3 certify_sweep.py"""
import json, os, time
import numpy as np
from certify_entries import entry
HERE = os.path.dirname(os.path.abspath(__file__))
modes = [(c, k) for c in ('x', 'y') for k in range(1, 17)]
n = len(modes)
ck = os.path.join(HERE, "certified_K16.json")
data = {}
if os.path.exists(ck):
    data = json.load(open(ck))
t0 = time.time(); todo = [(i, j) for i in range(n) for j in range(i, n)
                          if f"{i},{j}" not in data]
print(f"{len(todo)} entries to certify")
for m_, (i, j) in enumerate(todo):
    e = entry(modes[i], modes[j])
    data[f"{i},{j}"] = [float(e.mid()), float(e.rad())]
    if (m_ + 1) % 8 == 0 or m_ == len(todo) - 1:
        json.dump(data, open(ck, "w"))
        el = time.time() - t0
        frac = (m_ + 1) / len(todo)
        print(f"{m_+1}/{len(todo)}  elapsed {el/60:.1f}m  "
              f"ETA {el/frac*(1-frac)/60:.1f}m", flush=True)
json.dump(data, open(ck, "w"))
# certified minor test
from flint import arb, arb_mat, ctx
ctx.prec = 256
import math
G = np.diag([math.pi/4*(1+4*k*k) for c in range(2) for k in range(1, 17)])
s = 1/np.sqrt(np.diag(G))
A = arb_mat(n, n)
maxrad = 0.0
for key, (mid, rad) in data.items():
    i, j = map(int, key.split(","))
    b = (arb(mid) + arb(0, rad)) * arb(s[i]) * arb(s[j])
    A[i, j] = b; A[j, i] = b
    maxrad = max(maxrad, rad)
ok = True
for m_ in range(1, n+1):
    sub = arb_mat(m_, m_)
    for i in range(m_):
        for j in range(m_):
            sub[i, j] = A[i, j]
    d = sub.det()
    lo, hi = float(d.mid()-abs(d.rad())), float(d.mid()+abs(d.rad()))
    if (m_ % 2 == 0 and not lo > 0) or (m_ % 2 == 1 and not hi < 0):
        ok = False; print(f"minor {m_} NOT certified"); break
print(f"max entry radius = {maxrad:.2e}")
print("FULLY CERTIFIED negative definiteness of the K=16 frozen block"
      if ok else "certification incomplete")
print("SWEEPDONE")
