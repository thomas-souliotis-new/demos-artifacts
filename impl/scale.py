"""Scale experiment for the P-DEMOS prototype.

Two kinds of runs:

* full     -- the complete protocol (Setup, Cast, Tally, Verify, both parts of every
              ballot, all membership proofs) for small n, via pdemos.run();
* tally    -- the part of the protocol whose cost grows with the electorate on the
              tally side: every voter's cast part is committed on P-256, the
              commitments are routed by rank and combined homomorphically, the m
              rank tallies are opened and checked, and the result is decoded and
              compared with the ground truth. Ballot proofs and audit parts are
              per-ballot costs that do not change with n; their cost is reported
              by the full runs and extrapolates linearly.

Rankings are drawn from a simple utility model (candidate means plus Gaussian
noise), so the results look like a real election rather than uniform noise.

Usage:  python3 scale.py                         # full n=10,1000; tally n=10^6, m=5
        python3 scale.py --full 10 --tally 100000 --m 5 --workers 8
"""

import argparse
import json
import os
import random
import secrets
import time
from concurrent.futures import ProcessPoolExecutor

from Crypto.PublicKey import ECC

from pdemos import G, Q, Ck, run, smul

MEANS = [0.62, 0.55, 0.50, 0.38, 0.30, 0.25, 0.20, 0.15, 0.10, 0.05]  # candidate popularity


def sample_ranking(rng, m):
    util = [MEANS[j % len(MEANS)] + rng.gauss(0, 0.25) for j in range(m)]
    return sorted(range(m), key=lambda j: -util[j])  # ranking[i] = candidate at rank i


def _point(p):
    return None if p is None else (int(p.x), int(p.y))


def tally_chunk(args):
    """Commit the cast part of `count` ballots and aggregate them per rank."""
    count, m, x, hxy, seed = args
    h = ECC.EccPoint(hxy[0], hxy[1], curve="p256")
    rng = random.Random(seed)
    acc = [[None, None] for _ in range(m)]
    rsum = [0] * m
    counts = [[0] * m for _ in range(m)]
    for _ in range(count):
        ranking = sample_ranking(rng, m)
        # the m commitments of the cast part, E_j = Com(x^j; r_j), one per candidate
        part = []
        for j in range(m):
            r = 1 + secrets.randbelow(Q - 1)
            part.append((smul(G, r), smul(G, x ** j) + smul(h, r), r))
        # routing: the commitment of the candidate ranked i goes to tally i
        for i, j in enumerate(ranking):
            c1, c2, r = part[j]
            acc[i][0] = c1 if acc[i][0] is None else acc[i][0] + c1
            acc[i][1] = c2 if acc[i][1] is None else acc[i][1] + c2
            rsum[i] = (rsum[i] + r) % Q
            counts[i][j] += 1
    return [(_point(a), _point(b)) for a, b in acc], rsum, counts


def tally_run(n, m, workers):
    x = max(n, m) + 1                      # matrix mode
    assert x ** m <= Q, "x^m must not exceed the group order"
    ck = Ck()
    hxy = (int(ck.h.x), int(ck.h.y))
    chunk = max(1, n // (workers * 8))
    jobs, left, k = [], n, 0
    while left:
        c = min(chunk, left)
        jobs.append((c, m, x, hxy, 1_000_003 * k + 7))
        left -= c
        k += 1
    t0 = time.perf_counter()
    acc = [[None, None] for _ in range(m)]
    rsum = [0] * m
    counts = [[0] * m for _ in range(m)]
    with ProcessPoolExecutor(max_workers=workers) as ex:
        for part_acc, part_r, part_counts in ex.map(tally_chunk, jobs):
            for i in range(m):
                for s in (0, 1):
                    if part_acc[i][s] is not None:
                        p = ECC.EccPoint(*part_acc[i][s], curve="p256")
                        acc[i][s] = p if acc[i][s] is None else acc[i][s] + p
                rsum[i] = (rsum[i] + part_r[i]) % Q
                for j in range(m):
                    counts[i][j] += part_counts[i][j]
    t1 = time.perf_counter()
    # open and verify each rank tally, then decode
    ok = True
    decoded = []
    for i in range(m):
        T = sum(counts[i][j] * x ** j for j in range(m))  # the EA's opening value
        ok &= ck.check((acc[i][0], acc[i][1]), T, rsum[i])
        decoded.append([(T // x ** j) % x for j in range(m)])
    t2 = time.perf_counter()
    w = [m - 1 - i for i in range(m)]                     # Borda
    scores = [sum(w[i] * decoded[i][j] for i in range(m)) for j in range(m)]
    return {
        "n": n, "m": m, "x": x, "workers": workers,
        "commit_and_aggregate_s": round(t1 - t0, 1), "open_verify_decode_s": round(t2 - t1, 3),
        "openings_valid": ok, "decoded_equals_truth": decoded == counts,
        "first_preferences": decoded[0], "borda_scores": scores,
        "winner": "P%d" % (1 + max(range(m), key=lambda j: scores[j])),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", default="10,1000")
    ap.add_argument("--tally", default="1000000")
    ap.add_argument("--m", type=int, default=5)
    ap.add_argument("--workers", type=int, default=os.cpu_count())
    ap.add_argument("--out", default="scale_results.json")
    a = ap.parse_args()
    results = {"full": [], "tally": []}
    for n in [int(v) for v in a.full.split(",") if v]:
        t = time.perf_counter()
        r = run(n, a.m)
        results["full"].append({
            "n": n, "m": a.m, "verify_ok": r["ok"], "correct": r["correct"],
            "setup_ms_per_ballot": round(1000 * r["setup"], 1), "tally_ms_per_ballot": round(1000 * r["tally"], 2),
            "verify_ms_per_ballot": round(1000 * r["verify"], 1), "wall_s": round(time.perf_counter() - t, 1)})
        print("full ", results["full"][-1], flush=True)
    for n in [int(v) for v in a.tally.split(",") if v]:
        results["tally"].append(tally_run(n, a.m, a.workers))
        print("tally", results["tally"][-1], flush=True)
    json.dump(results, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
