# EasyCrypt proofs for P-DEMOS

This folder machine-checks the computational parts of the P-DEMOS security
proofs in [EasyCrypt](https://github.com/EasyCrypt/easycrypt). The arithmetic
lemmas are checked separately in Lean ([`../formal/`](../formal/)).

All four files check with no `admit` (`./check.sh`, about 25 s). Every
statement about DDH is an **exact equation for an explicit distinguisher**,
against the DDH games `DDH0`/`DDH1` of the EasyCrypt standard library. The
asymptotic step ("hence negligible", subexponential DDH, complexity
leveraging) stays on paper.

| Paper | What is machine-checked | EasyCrypt | File |
|---|---|---|---|
| Lemma 2 (product-opening hiding), `zkp.tex`; Appendix A | For every `m ≥ 2`: `Pr[A(D_0)] − Pr[A(D_1)] = 2(m−1)·Adv_DDH(Ravg(BP(A)))` | `product_hiding`, `product_hiding_abs` | `ProductHiding.eca` |
| Lemma 2 is not vacuous | instance `m = 3`, `X = {1, x, x²}` | clone `PH3` | `ProductHidingM3.ec` |
| Theorem 3 (privacy and receipt-freeness), `security.tex`; Appendix C | For `n = 2`, `m = 2`, matrix mode, `φ = 1`: `κ0·(Pr[G_priv = 1] − 1/2) = 2·Adv_DDH(D(A))` with `κ0 = 1/648`, i.e. `|ε| = 1296·Adv_DDH` | `privacy`, `privacy_abs` | `Privacy.eca` |
| The Σ-protocol abstraction of Theorem 3 is consistent | trivial instance discharging all its axioms | clone `P22` | `PrivacyInst.ec` |

## Lemma 2 (`ProductHiding.eca`)

`ProductHiding.eca` is an abstract theory with parameters `n = m − 1 > 0`, the
encoding set `X` (a list `xs` of length `m`), and two permutations `sigma0`,
`sigma1` of `X` (`perm_eq sigma0 xs`, `perm_eq sigma1 xs`). Game `D(A).main(b)`
samples `x ← Z_q`, `r_1..r_m ← Z_q`, and gives the adversary
`(h = g^x, (Com_h(σ_b(p); r_p))_p, R = Σ r_p)`, where
`Com_h(v; r) = (g^r, g^v · h^r)`. For every adversary `A` whose `guess`
terminates (`islossless A.guess`):

```
Pr[D(A).main(false)] - Pr[D(A).main(true)]
  = 2(m-1) * (Pr[DDH0(Ravg(BP(A))).main()] - Pr[DDH1(Ravg(BP(A))).main()])
```

The proof has two steps.

1. **`D_MCPA`, the paper's reduction.** `D_b` is *perfectly* equivalent to the
   `(m−1)`-message IND-CPA game against `BP(A)`. `BP(A)` samples `R`, sets
   `c_m = Com(S;R) ⊙ (⊙_{p<m} c_p)^{-1}` and runs `A`. The coupling maps
   `(r_1..r_m)` to `(r_1..r_{m−1}, R = Σ r_p)`. This step is exactly as in
   Appendix A.
2. **`mcpa_ddh`, the hybrid.** Hybrid `k` replaces the first `k` ciphertexts
   by uniform pairs `(g^r, g^u)`. Hop `k → k+1` embeds a DDH triple at
   position `k`, with `h = g^x`. Each world `b` walks `m − 1` hops to the
   all-uniform game, which does not depend on `b`. `Ravg` picks one of the
   `2(m−1)` hops uniformly at random (stdlib theory `Means`).

### Finding: the constant in Lemma 2

The paper stated "a DDH distinguisher with advantage at least `ε/(m−1)`". The
machine-checked bound is `ε/(2(m−1))`. Step 1 (the IND-CPA adversary has the
same advantage) is exactly right. In the hybrid, however, one IND-CPA hop
between two fixed messages costs two DDH hops (real → uniform → real), so the
loss is `2(m−1)`, not `m−1`. The paper already uses this factor 2 in the proof
of Theorem 3. `zkp.tex` and Appendix A were corrected on this branch. Lemma 2
is used only as a remark in the privacy proof, so no other statement changes.

## Theorem 3 (`Privacy.eca`)

### The model

`Privacy.eca` defines the privacy game `GPriv` for two ballots and two
candidates, as follows.

* **Setup.** The EA samples `ck = h = g^x`. For every ballot `ℓ` and part
  `a`, it samples a permutation `π` (a bit) and randomness `r`. It posts, by
  position `p`, the commitments `E_p = Com_h(x^{π(p)}; r_p)`, the first
  messages of the membership proofs, and `R = Σ_p r_p`.
* **Corruption and choices.** The adversary first names the corrupted voters.
  After Setup it receives the corrupted voters' paper ballots. It then
  submits, for every honest voter, a pair of rankings `(ω⁰, ω¹)`, and for
  every corrupted voter a coin and a ranking.
* **Cast.** An honest voter flips her coin and casts `ω^b`. `ψ` maps each rank
  to a position of the cast part.
* **Tally.** For each ballot: the coin, `ψ`, the opened audit part
  (permutation and randomness), and the membership-proof responses of the
  cast part for the challenge extracted from the coins. Then the two rank
  aggregates `(T_i, R̂_i)`.
* **Views.** For `b = 0` the honest voter's real paper ballot; for `b = 1` the
  simulator `S`, which rewrites the cast part so that the `i`-th code of `ψ`
  sits next to `ω⁰(i)`.
* **Output.** The side conditions (at most `φ = 1` corruption, equal honest
  results for `b = 0, 1`) are checked; otherwise the output is a uniform bit.

The reduction `B` is the one of Appendix C. It guesses the coins, the carrier
`ℓ*`, the carrier's ranking `ω*` and the result `N*`. It embeds the challenge
`C = Com_h(β; ρ)` as `E = Com(u; s) ⊙ C^{v−u}`, with neutral values
`c = S·2^{-1}` and carrier values `t_i = T*_i − (n_c−1)c`. It simulates the
embedded parts' proofs with the special HVZK simulator, opens `R = Σ s` and
the aggregates to `T*`, and outputs `b* = b` on `Cont` and a uniform bit
otherwise. `Cont` includes the artificial coin with probability
`2^{-(φ−k)}(n−φ)/(n−k)`. `D(A)` is the standard IND-CPA-to-DDH wrapper of `B`.

### What is proved

* **(a) β = 1, perfect simulation on Cont** (`B1_RealG`, `RealG_G2`,
  `RealG2_E`). With `β = 1`, every embedded part is distributed exactly like
  an honest part. `partE_H` gives this per part: the shift
  `s ↦ s + ρ(v−u)`, plus the HVZK coin bijection. `R` and the aggregate
  randomness coincide with the real ones whenever the guesses are right
  (`routed_zero`: the routed `v − u` cancel at every rank). `Cont` is then
  rewritten as "G_priv, followed by guesses sampled independently at the
  end". `guess_pr` proves these guesses succeed with probability exactly
  `κ0 = 1/648` for every corruption pattern with at most one corrupted voter.
  Together (`cpa1`): `Pr[CPA(β=1)] = 1/2 + κ0·(Pr[G_priv = 1] − 1/2)`.
* **(b) β = 0, independence of b** (`B0_B0E`, `B0E_B0L`, `B0L_swap`). With
  `β = 0`, the embedded commitments are re-parametrised as `Com(u; s')`
  (`partE_E0`). `R = Σ s'` does not depend on `π`, so the permutations of the
  honest voters' embedded parts can be sampled *after* the adversary's
  choices. The carrier's values are re-parametrised by `τ = π ∘ ω*`. Then
  `π ↦ π ∘ ω⁰ ∘ (ω¹)^{-1}` couples the runs with `b` and `¬b`. `Cont`
  coincides in the two runs, and on `Cont` so does the adversary's entire view.
  Hence (`cpa0`): `Pr[CPA(β=0)] = 1/2`.
* **Conclusion** (`privacy`, `privacy_abs`).
  `κ0·(Pr[G_priv = 1] − 1/2) = 2·(Pr[DDH0(D(A))] − Pr[DDH1(D(A))])`. This is
  the paper's `ε ≤ 2·Adv_DDH/κ0`, as an equality, with `κ0` exactly the
  paper's `(n−φ)/n · 2^{-φ} · 1/m! · 1/|T|` for `n = m = 2`, `φ = 1`,
  `|T| = 3^4`.

No error was found in the argument of Appendix C for this instance.

### Simplifications (Theorem 3) — read before citing

1. **Fixed instance:** `n = 2` ballots, `m = 2` candidates, **matrix mode
   only**, `φ = 1`. Score mode, larger `n` and `m`, and `m ≥ 3`
   (positional rules proper) are not covered. Rankings of two candidates are
   modelled as a bit.
2. **Non-adaptive corruption and scheduling.** The adversary fixes the
   corrupted set before Setup. It makes all voting choices in one round,
   after seeing `Pub` and the corrupted ballots, and receives the honest
   views together with the tally. The paper's game is adaptive.
3. **Vote codes are identified with the BB positions they point to.** A paper
   ballot is then its permutation, and `ψ` is a map from ranks to positions.
   The code commitments `U` are omitted, since the codes are effectively
   public. This only strengthens the adversary.
4. **Σ-protocol:** one instance (`κ = 1`). The challenge is an abstract
   function of the two coins. The membership proof is an **abstract
   functionality** with perfect special HVZK *in coin-bijection form*: for a
   true statement, the simulator's coins are a bijective re-parametrisation
   of the prover's coins, and under it the transcripts coincide. This is
   stronger than distributional HVZK. The disjunctive Chaum–Pedersen
   protocol satisfies it, but this is not formalised.
   `PrivacyInst.ec` only shows that the axioms are consistent.
5. **No abstention:** every voter casts.
6. **Invalid guessed result.** When `N*` is not a possible result, `B`
   continues with neutral carrier values instead of aborting. `Cont` then
   fails, so `B` still outputs a uniform bit, as in the paper.
7. **Hypotheses of the final theorem:** the adversary's three procedures
   terminate (`islossless`), and `2 ≠ 0` in `Z_q` (needed for
   `c = S·m^{-1}`; the paper's parameters give `q ≥ 9`).
8. **Not formalised:** running time and PPT-ness, the subexponential-DDH
   assumption, and the complexity-leveraging step
   `ε ≤ 2^{L+1}·2^{-λ^c}`.

### Modelling choices (Lemma 2)

* The group is the abstract prime-order cyclic group of the stdlib
  (`DiffieHellman.ec`). The key `h = g^x` is honestly generated. The
  adversary also sees `h`, and its `guess` terminates.
* Running time is not formalised. `Ravg(BP(A))` makes one uniform choice,
  `O(m)` group operations and one call to `A`.

## How to run

**Toolchain** (tested on macOS 26 / Apple Silicon, October 2026):

| Component | Version | Source |
|---|---|---|
| opam | 2.6.1 | Homebrew |
| OCaml | 5.4.1 | opam switch `easycrypt` (OCaml 5.0–5.3 trigger an EasyCrypt GC warning) |
| EasyCrypt | git `859766e50e936fb9e420fb6fb1ad8824ffb8d83e` (`r2026.10`) | `opam pin` |
| Why3 | 1.8.2 | opam (dependency of EasyCrypt) |
| Alt-Ergo | 2.6.0 | opam |
| Z3 | 4.12.6 | official GitHub release binary |
| CVC5 | 1.0.8 | official GitHub release binary |

```bash
brew install opam gmp pkg-config zlib
opam init --bare -n
opam switch create easycrypt ocaml-base-compiler.5.4.1
eval $(opam env --switch=easycrypt)
opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git#859766e50e936fb9e420fb6fb1ad8824ffb8d83e
opam install alt-ergo.2.6.0 easycrypt
# put z3 (4.12.6) and cvc5 (1.0.8) on PATH, then:
easycrypt why3config
```

On macOS with Xcode 15 and Command Line Tools 26, the `bitwuzla-cxx`
dependency fails to compile, because the selected clang is older than the SDK
headers. Building with `DEVELOPER_DIR=/Library/Developer/CommandLineTools`
fixes this.

**Checking:**

```bash
cd artifact/easycrypt
./check.sh            # fails on any `admit`, then compiles every file in FILES
```

`easycrypt.project` pins the provers (`Alt-Ergo@2.6`, `Z3@4.12`, `CVC5@1.0`).
The whole development checks in about 25 s on an Apple M3 Max.
