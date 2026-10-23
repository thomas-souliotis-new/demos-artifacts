# P-DEMOS artifact

This is the companion artifact for the paper **"P-DEMOS: End-to-End Verifiable Positional Voting in the Standard Model"** by Thomas Souliotis (School of ECE, National Technical University of Athens).

P-DEMOS extends the DEMOS-1 e-voting system to positional scoring rules such as the Borda count. Its verifiability holds in the standard model, with no random oracles and no trusted setup. This artifact contains:

| Folder | What it is | Paper sections |
|---|---|---|
| [`impl/`](impl/) | Python reference prototype of the full protocol (Setup, Cast, Tally in matrix and score mode, Result, Verify) on NIST P-256, with a test suite and micro-benchmarks | Sect. 7 (worked example), Sect. 8 (evaluation) |
| [`formal/`](formal/) | Lean 4 + mathlib proofs of the arithmetic lemmas, of correctness, and of E2E verifiability and its margin corollary against unbounded adversaries, in a model of the protocol and of the game `G_e2e` | Lemma 1, Thm. 1, Thm. 2 (with Lemma `amplified`), Cor. `margin` |
| [`easycrypt/`](easycrypt/) | EasyCrypt proofs of the computational arguments: Lemma 2 for every m, and the core of the Theorem 3 reduction for a fixed small instance | Lemma 2, Thm. 3 (Appendix C) |

What is machine-checked:

* **Lean** checks perfect binding of lifted ElGamal, completeness and special soundness of the Chaum–Pedersen and CDS proofs, Theorem 1 end to end for an honest run, Theorem 2 end to end (the bound on the winning probability of every adaptive, unbounded adversary in `G_e2e`), and Corollary `margin` end to end in the variant of the game where the adversary wins by changing the winner. The modelling conventions are listed in [`formal/README.md`](formal/README.md).
* **EasyCrypt** checks the DDH reduction of Lemma 2 for every `m`, and the core of the Theorem 3 reduction for `n = m = 2` under the simplifications listed in [`easycrypt/README.md`](easycrypt/README.md).
* **On paper only:** the general (adaptive, any `n`, `m`) form of Theorem 3, and the asymptotic complexity-leveraging step. These are in the article's appendices. That the Lean and EasyCrypt models match the protocol description is checked by reading.

## 1. Python prototype (`impl/`)

**Requirements:** Python ≥ 3.9 and [PyCryptodome](https://pypi.org/project/pycryptodome/).

```bash
cd impl
python3 -m pip install -r requirements.txt
python3 test_and_bench.py            # tests + benchmark table (about 20 s)
python3 test_and_bench.py --no-bench # tests only
```

`scale.py` runs the protocol at election scale (about 10 minutes on a 14-core laptop):

```bash
python3 scale.py                       # full protocol for n = 10 and 1,000; tally for n = 10, 1,000 and 1,000,000
python3 scale.py --full 10 --tally 100000 --m 5 --workers 8
```

For each $n$, the tally run commits every voter's cast part on P-256, routes and aggregates the commitments by rank, opens and checks the rank tallies, and compares the decoded result with the ground truth. The results of our run are in `scale_results.json`.

The test suite checks that:
1. Honest elections verify and decode to the correct Borda scores in both result modes.
2. The worked example of the paper is reproduced: matrix tallies `T = (52, 16, 56)`, and score-mode tally `T = 356 → (5, 3, 4)`.
3. A mapping attack by the Election Authority is caught by voters in about half of the runs.
4. A ballot with a duplicated score fails the sum (permutation) check.
5. A tampered tally opening, or a vote recorded in a different order, is rejected.

`pdemos.py` is a proof of concept for correctness and cost measurement. It derives the verifier challenge directly from the voters' coins, and does not implement DEMOS-1's randomness extractor or challenge amplification. It is **not** production voting software.

## 2. Lean proofs (`formal/`)

**Requirements:** [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) and the mathlib version are pinned.

```bash
cd formal
lake exe cache get   # downloads prebuilt mathlib (~5 GB, into .lake/)
lake build           # succeeds with no `sorry`
```

See [`formal/README.md`](formal/README.md) for the mapping from each paper statement to its Lean theorem.

## 3. EasyCrypt proofs (`easycrypt/`)

**Requirements:** EasyCrypt (pinned commit), Why3, and the SMT provers Alt-Ergo 2.6, Z3 4.12 and CVC5 1.0. See [`easycrypt/README.md`](easycrypt/README.md#how-to-run) for exact installation steps on macOS.

```bash
cd easycrypt
./check.sh   # checks every file and fails on any `admit` (about 25 s)
```

[`easycrypt/README.md`](easycrypt/README.md) maps each paper statement to its EasyCrypt lemma and lists every modelling simplification.

## Citation

If you use this artifact, please cite the paper (see [`CITATION.cff`](CITATION.cff)).

## License

MIT. See [`LICENSE`](LICENSE).
