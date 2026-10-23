"""Correctness tests and micro-benchmarks for the P-DEMOS prototype.

Run:  python3 impl/test_and_bench.py
"""

import platform
import sys

from pdemos import Election, run


def test_correctness():
    for score_mode in (False, True):
        for m in (2, 3, 5):
            r = run(12, m, score_mode=score_mode)
            assert r["ok"], r["msg"]
            assert r["correct"], "decoded Borda scores differ from ground truth"
    print("[ok] honest elections verify and decode correctly (matrix and score modes)")


def test_paper_example():
    # Section 6 example: n=4, m=3, rankings chosen to give the matrix in Table 2.
    rankings = [[2, 0, 1], [0, 1, 2], [0, 1, 2], [2, 1, 0]]
    r = run(4, 3, seed_rankings=rankings)
    el = r["el"]
    assert el.x == 5
    mat = el.decode()
    assert [V for V, _ in el.result_open] == [52, 16, 56], el.result_open
    assert mat == [[2, 0, 2], [1, 3, 0], [1, 1, 2]], mat
    r = run(4, 3, score_mode=True, seed_rankings=rankings)
    assert r["el"].x == 9 and r["el"].result_open[0][0] == 356
    assert r["el"].decode() == [[5, 3, 4]]
    print("[ok] paper example: matrix T = (52, 16, 56); score mode T = 356 -> (5, 3, 4)")


def test_mapping_attack():
    # EA swaps two values on part 0 of ballot 0. Universal checks still pass
    # (it is still a permutation); the voter detects it iff part 0 is audited.
    detected = undetected = 0
    for _ in range(40):
        r = run(3, 3, cheat=(0,))
        assert r["ok"], r["msg"]
        el, a = r["el"], r["coins"][0]
        if el.voter_check(0, a):
            assert a == 0  # cheated part was cast
            undetected += 1
        else:
            assert a == 1  # cheated part was audited
            detected += 1
    print(f"[ok] mapping attack detected {detected}/40 times (expected ~1/2)")


def test_non_permutation_rejected():
    el = Election(2, 3)
    el.setup()
    # EA replaces a cast commitment with another valid-looking value x^0
    # (a duplicate) - the permutation check must fail.
    part = el.bb[0]["parts"][0]
    s = el.sec[0][0]
    p0, p1 = s["pi"][0], s["pi"][1]
    part["E"][p1] = el.ck.com(el.X[0], s["r"][p1])
    votes = [el.cast(0, [0, 1, 2], 0), el.cast(1, [2, 1, 0], 1)]
    el.tally(votes)
    ok, msg = el.verify_universal()
    assert not ok and "permutation" in msg, msg
    print("[ok] duplicated score (non-permutation) rejected by universal verification")


def test_tampered_tally_and_record_rejected():
    r = run(5, 3)
    el = r["el"]
    V, R = el.result_open[0]
    el.result_open[0] = (V + 1, R)  # EA claims one extra vote
    ok, msg = el.verify_universal()
    assert not ok and "tally" in msg, msg
    el.result_open[0] = (V, R)
    # (I2): the BB records a different order of codes than the voter submitted
    v0 = dict(el.votes[0])
    submitted = dict(v0)
    el.votes[0] = dict(v0, codes=list(reversed(v0["codes"])))
    assert not el.voter_check(0, v0["a"], submitted=submitted)
    print("[ok] tampered tally opening and re-ordered recorded vote are rejected")


def bench():
    print()
    print(f"Benchmark ({platform.machine()}, Python {sys.version.split()[0]}, NIST P-256)")
    print("| m | n | x (matrix) | setup/ballot [s] | tally/ballot [s] | verify/ballot [s] | BB group elems/ballot |")
    print("|---|---|---|---|---|---|---|")
    n = 10
    for m in (3, 5, 8, 10):
        r = run(n, m)
        assert r["ok"] and r["correct"]
        # per part: m U + m E (2 elems each) + m*m first-move pairs (2 elems each)
        elems = 2 * (2 * m * 2 + m * m * 2)
        print(f"| {m} | {n} | {r['el'].x} | {r['setup']:.3f} | {r['tally']:.3f} | {r['verify']:.3f} | {elems} |")


if __name__ == "__main__":
    test_correctness()
    test_paper_example()
    test_mapping_attack()
    test_non_permutation_rejected()
    test_tampered_tally_and_record_rejected()
    if "--no-bench" not in sys.argv:
        bench()
