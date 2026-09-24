#!/usr/bin/env python3
"""
Minimal security audit for the current Exp252 Kangaroo-style comparison mask:
    V = R * (A*d + B)
with zeta > A > B > 0 and R in {+1,-1}.

This is NOT a correctness test.  It tests whether the value opened to the
comparison party can be simulated independently of secret d.
"""
import secrets

def one(zeta, d):
    A = 2 + secrets.randbelow(zeta - 2)
    B = 1 + secrets.randbelow(A - 1)
    R = -1 if secrets.randbits(1) else 1
    return R * (A * d + B)

def audit(zeta, samples=10000):
    d0 = 0
    d1 = zeta - 1
    v0 = [one(zeta, d0) for _ in range(samples)]
    v1 = [one(zeta, d1) for _ in range(samples)]

    # Perfect distinguisher on the admissible domain:
    # d=0 => |V|=B<zeta.
    # d=zeta-1 and A>=2 => |V|>=2(zeta-1)+1>zeta.
    fp = sum(abs(v) >= zeta for v in v0)
    fn = sum(abs(v) < zeta for v in v1)
    return {
        "zeta": zeta,
        "samples_each": samples,
        "d0": d0,
        "d1": d1,
        "d0_abs_max": max(abs(v) for v in v0),
        "d1_abs_min": min(abs(v) for v in v1),
        "false_positive": fp,
        "false_negative": fn,
        "accuracy": 1.0 - (fp + fn) / (2 * samples),
    }

if __name__ == "__main__":
    for name, zeta in [("probe64", 1 << 31), ("certificate56", 1 << 26)]:
        r = audit(zeta)
        print(name, r)
        assert r["false_positive"] == 0
        assert r["false_negative"] == 0
        assert r["accuracy"] == 1.0
