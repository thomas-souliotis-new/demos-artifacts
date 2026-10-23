# Machine-checked proofs for P-DEMOS

This is a Lean 4 + mathlib formalisation of the correctness theorem and of the
verifiability side of the P-DEMOS security analysis. It covers:

* the arithmetic lemmas: the Encoding Lemma, tally decoding and the per-ballot
  score bound;
* the information-theoretic building blocks of Theorem 2: perfect binding of
  lifted ElGamal, and completeness and special soundness of the Chaum–Pedersen
  and CDS proofs;
* a model of the protocol (`Pub`, paper ballots, `ψ`, Tally, the checks
  (U1)–(U6) and (I1)–(I2), `Result`, `f`, `δ`) and of the honest run;
  **Theorem 1 end to end**;
* the game `G_e2e` as a probabilistic program over mathlib's `PMF`, with an
  adaptive, unbounded adversary and the extractor of Appendix B;
  **Theorem 2 end to end**, by a reduction of the game to Steps 1–4 and to the
  fair-coin bound;
* the variant `G_margin` of the game, in which the adversary wins by changing the
  winner; **Corollary `margin` end to end**.

## Status

| Paper statement | Status | Main Lean theorem |
|---|---|---|
| Lemma 1 (Encoding Lemma) | ✅ end to end | `encoding_lemma` |
| Theorem 1 (Correctness) | ✅ end to end, in the protocol model below | `correctness` |
| Lemma `amplified` (soundness of the amplified proofs) | ✅ end to end, inside the proof of Theorem 2 | `win_bad_hits`, `prob_exists_succeeds_le` |
| Theorem 2 (E2E verifiability) | ✅ end to end, in the game model below | `e2e_verifiability`, `e2e_verifiability_rand` |
| Corollary `margin` | ✅ end to end, in the game model below | `margin_verifiability`, `margin_verifiability_rand` |
| Lemma 2, Theorem 3 | not in Lean; see `../easycrypt` | — |

## What is proved

### Arithmetic lemmas

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (Encoding Lemma), `zkp.tex` | `encoding_lemma` (permutation form), `encoding_lemma_count` (each power occurs exactly once) | `PDemos/Encoding.lean` |
| "From integers to ℤ_q", `zkp.tex` | `sum_lt_pow`, `sum_eq_S_of_modEq` | `PDemos/Encoding.lean` |
| Theorem 1 (Correctness), decoding, matrix mode, `security.tex` | `rankTally_eq`, `posMatrix_le`, `rankTally_lt`, `rankTally_digit` | `PDemos/Tally.lean` |
| Theorem 1 (Correctness), decoding, score mode | `scoreTally_eq`, `scoreVec_le`, `scoreTally_lt`, `scoreTally_digit` | `PDemos/Tally.lean` |
| Per-ballot bound `Δ = w₁ − wₘ` (Corollary 1) | `score_sub_le` (one ballot, one candidate), `scoreVec_sub_le_single`, `scoreVec_sub_le` (profiles differing in `k` ballots differ by at most `k·Δ`), `score_pair_le` (one ballot, two candidates) | `PDemos/ScoreBound.lean` |
| Base-`x` digits (shared core) | `digitSum_lt`, `digitSum_digit`, `digitSum_injective` | `PDemos/Digits.lean` |

### Building blocks (`background.tex`, Section 2)

| Paper | Lean | File |
|---|---|---|
| Completeness of Chaum–Pedersen; simulated transcripts accept | `cp_complete`, `cp_sim_accept` | `PDemos/Completeness.lean` |
| Completeness of the CDS OR-proof and of its `κ`-fold amplification | `cds_complete`, `amp_complete` | `PDemos/Completeness.lean` |
| Lifted ElGamal `Com(v;r) = (g^r, g^v h^r)` | `Com`, `CommitsTo` | `PDemos/ElGamal.lean` |
| Homomorphism | `com_mul`, `com_pow`, `com_inv`, `com_div`, `com_prod`, `CommitsTo.mul`, `CommitsTo.prod`, `CommitsTo.pow` | `PDemos/ElGamal.lean` |
| Perfect binding, for every key `h` | `com_injective`, `committed_value_unique` | `PDemos/ElGamal.lean` |
| "Every posted commitment has a unique committed value" (Appendix B) | `exists_com`, `existsUnique_committed` | `PDemos/ElGamal.lean` |
| Chaum–Pedersen special soundness, witness `r = (z−z')/(e−e')` | `cp_special_soundness`, `cp_extract_commitment` | `PDemos/Sigma.lean` |
| CDS OR-proof special soundness | `cds_special_soundness` | `PDemos/Sigma.lean` |

### Theorem 2: the step lemmas (`appendix.tex`, Appendix B)

| Paper | Lean | File |
|---|---|---|
| Lemma `amplified`, Claim: for `v ∉ 𝒳`, at most one challenge admits accepting responses | `cds_challenge_unique`, `cds_challenge_unique_of_value` | `PDemos/Sigma.lean` |
| Lemma `amplified`: `κ` parallel instances; challenge derivation from the coins is injective, so acceptance fixes `c⃗*` | `amplified_challenge_unique`, `challenge_injective`, `amplified_coins_unique` | `PDemos/Sigma.lean` |
| Lemma `amplified`: honest coins hit `c⃗*` with probability ≤ `2^{-θ}`; union bound over ≤ `2nm` commitments | `prob_succeeds_le`, `prob_exists_succeeds_le` | `PDemos/Coins.lean` |
| Soundness of the validity check (Appendix A) and Step 1: every cast part encodes a ranking | `part_encodes_permutation`, `cast_part_ranking` | `PDemos/Verifiability.lean` |
| Step 2: tallied as recorded, `Result(info) = f(⟨σ_t⟩)`, both modes | `matrix_result_eq`, `score_result_eq`, `sum_weight_posMatrix` (`sc_w(f_mat) = f_sc`) | `PDemos/Verifiability.lean` |
| Step 3: `δ(Result, f(ω)) ≤ w₁ · U`, with `U = ∑_t ([σ_t ≠ ω_t] + y_t − 1)` | `deviation_le`, `extractor_truncation` | `PDemos/Verifiability.lean` |
| Step 4: a consistent cast part makes its tag faithful | `faithful_of_consistent` | `PDemos/Verifiability.lean` |
| Step 4: `δ ≥ d` forces `U ≥ ⌈d/w₁⌉`; `Pr[(2) ∧ U ≥ k] ≤ 2^{-k}` | `units_of_deviation`, `prob_succeeds_le` | `PDemos/Verifiability.lean`, `PDemos/Coins.lean` |
| Final bound `ε_e2e = 2^{-⌈d/w₁⌉} + 2nm · 2^{-θ}` | `e2e_error_bound` | `PDemos/Coins.lean` |

### Theorem 1 end to end (`newProtocol.tex`, `security.tex`)

| Paper | Lean | File |
|---|---|---|
| Data on `BB`, paper ballots, `ψ`, receipts `α` | `PartPub`, `Pub`, `PaperBallot`, `Psi`, `Tau`, `Info`, `Receipt` | `PDemos/Protocol.lean` |
| Checks (U2)–(U6), (I1)–(I2); `Verify` | `U2` … `U6`, `Universal`, `I1`, `I2`, `Verify` | `PDemos/Protocol.lean` |
| `Result` (Algorithm 1), `f_mat`, `f_sc`, `sc_w`, `δ` | `Result`, `decode`, `elect`, `profile`, `scw`, `dist`; `scw_elect` (`sc_w ∘ f = ` score vector) | `PDemos/Protocol.lean` |
| Honest Setup, Cast, Tally | `SetupRand`, `setup`, `paperBallot`, `castPsi`, `receipt`, `tally`, `honestInfo` | `PDemos/Correctness.lean` |
| **Theorem 1**: every check passes and `Result(info) = f(ω)`, both modes, for every choice of the honest randomness and coins | `correctness` | `PDemos/Correctness.lean` |

The decoding reuses `matrix_result_eq` and `score_result_eq` (and through them
`PDemos/Tally.lean`) on the cast ballots, listed by `enum`.

### Theorem 2 end to end (`security.tex`, `appendix.tex`)

| Paper | Lean | File |
|---|---|---|
| Adversary of `G_e2e` (the `EA` and the corrupted voters) | `Adversary` | `PDemos/Game.lean` |
| Fresh fair coins for the honest voters, drawn lazily | `honestCoins`; `honestCoins_eq` (same as `n` pre-drawn coins read by `runCoins`) | `PDemos/Game.lean` |
| Extractor `𝓔` of Appendix B | `cval`, `extractOne`, `extractTags`, `extractor` | `PDemos/Game.lean` |
| Winning condition (1)–(3), the game | `Win`, `gameE2E`, `gameE2ERand`; `gameE2E_apply_true` | `PDemos/Game.lean` |
| From the honest coins to the strategies of `Coins.lean` | `hits_spec`, `normStrat`, `succeeds_normStrat` | `PDemos/Game.lean` |
| Lemma `amplified`: on `Z`, every honest coin hits a bit of `c⃗*`, for one of `2nm` commitments | `Bad`, `cstar`, `baseZ`, `win_bad_hits` | `PDemos/E2E.lean` |
| (U3)+(I1): every honest voter's audit part is consistent | `Consistent`, `voter_audit` | `PDemos/E2E.lean` |
| Step 1 on `BB`; `𝓔 ≠ ⊥` | `step1_bb`, `extractor_eq` | `PDemos/E2E.lean` |
| Step 2 on `BB` | `scw_result_eq` | `PDemos/E2E.lean` |
| Step 3 on the game's multisets: any functional `φ` of the counted rankings with values in `[lo, hi]`, `lo ≤ 0 ≤ hi`, moves by at most `(hi − lo)·U`; for one candidate's score, `U ≥ ⌈d/w₁⌉` | `msVal`, `win_good_val`, `win_good_units` | `PDemos/E2E.lean` |
| Step 4: consistent cast part ⇒ faithful (with the routing of (U4)); the coins that must hit | `faithful_of_routing`, `base4`, `win_good_hits`, `win_count` | `PDemos/E2E.lean` |
| **Theorem 2**: `Pr[G_e2e = 1] ≤ 2^{-⌈d/w₁⌉} + 2nm·2^{-θ}` | `e2e_verifiability` (deterministic adversaries), `e2e_verifiability_rand` (randomised adversaries) | `PDemos/E2E.lean` |

### Corollary `margin` end to end (`security.tex`, `appendix.tex`)

`G_margin` is `G_e2e` with condition (3a) replaced by "the winner changes". The
proof is that of Theorem 2; only Step 3 changes.

| Paper | Lean | File |
|---|---|---|
| "The winner changes": in `f` of the honest and the extracted choices, `c` leads every other candidate by at least `M`; in `Result(info)` some `c' ≠ c` scores at least as much as `c` | `WinnerChanged` | `PDemos/Margin.lean` |
| Winning condition (1), (2), (3a) "the winner changes", (3b) `𝓔 = ⊥`; the game | `WinMargin`, `gameMargin`, `gameMarginRand`; `gameMargin_apply_true`; `WinMargin.win` (a win in `G_margin` is a win in `G_e2e` with `d = 0`, so Lemma `amplified` and Step 4 apply unchanged) | `PDemos/Margin.lean` |
| One unit moves a pairwise difference `s_c − s_{c'}` by at most `2Δ`, `Δ = w₁ − wₘ`; so `U ≥ ⌈M/(2Δ)⌉` | `score_pair_le` (`φ = score_c − score_{c'}` lies in `[−Δ, Δ]`), `win_good_val`, `win_margin_units` | `PDemos/ScoreBound.lean`, `PDemos/Margin.lean` |
| **Corollary `margin`**: `Pr[G_margin = 1] ≤ 2^{-⌈M/(2Δ)⌉} + 2nm·2^{-θ}` | `margin_verifiability` (deterministic adversaries), `margin_verifiability_rand` (randomised adversaries) | `PDemos/Margin.lean` |

### The model, and how it differs from the paper

The statements above are about the following model. Each point is either a
convention that loses nothing, or a place where the Lean adversary is *stronger*
than the paper's.

1. **Group.** `G` is any commutative group of prime order `q`, `g ≠ 1` any
   generator, and the key `h` is arbitrary (chosen by the adversary in
   `G_e2e`). No concrete curve is modelled. Vote codes are elements of `ℤ_q`.
2. **Tags are `BB` slots.** (U1) asks for exactly `n` ballots with distinct tags
   and at most one cast ballot per tag. We identify the tags with their ranks
   `0, …, n-1`, so `BB` is indexed by `Fin n` and (U1) holds by construction.
   The coin string is ordered by tag, as in the paper.
3. **Parameters.** `n, m, κ, x, β, w` and the mode are fixed in advance and
   universally quantified, with the paper's conditions `x > m`, `x^m ≤ q`,
   `n·W < x`, `n ≤ κβ`, `2^β ≤ q`, antitone weights, and `θ ≥ 1`. In the paper
   the adversary chooses the candidates, weights and mode; a bound for every
   choice covers that.
4. **Adversary.** A deterministic adversary is a tuple of functions of the
   honest coins drawn so far: whether to run another honest voter, which paper
   ballot it holds, which ranking it votes, and finally the whole `BB` after
   Setup (cast ballots, openings, responses, aggregates). This is fully adaptive.
   It hands out paper ballots *when* it schedules a voter rather than all at
   Setup, which only helps it. Corrupted voters act only through what the
   adversary posts. A randomised adversary is a `PMF` over deterministic ones,
   and `e2e_verifiability_rand` proves the bound for it by averaging, so no
   restriction to deterministic adversaries remains.
5. **Voter identities.** Honest voters are identified by the order in which
   they are run. `f` is symmetric, so the argument of `f` is a multiset: the
   honest rankings, plus the extracted choices truncated to the `n - |𝒱_succ|`
   other voters (the rest abstain).
6. **Lazy coins.** The game draws a fresh fair coin per scheduled honest voter
   (`honestCoins`); `honestCoins_eq` proves that this is the distribution of `n`
   pre-drawn coins read in order, which is what `Coins.lean` bounds.
7. **Honest submissions.** An honest voter always submits the codes of her part
   in her order. The paper ignores a submission whose codes are not distinct; in
   the model such a ballot part is simply *inconsistent* (`Consistent` requires
   distinct printed codes), which costs the adversary a coin as in Step 4.
8. **Winner and margin (`G_margin`).** The paper's corollary does not fix how
   ties are broken. The Lean game reads the winner on the score vector `sc_w`
   in both modes. It counts a tie in `Result(info)` as a change of winner, and
   it reads "true margin `M`" as "the true winner leads every other candidate
   by at least `M`". Both choices can only make the adversary win more often.
   The bound is monotone in `M`. If `Δ = 0`, then `⌈M/(2Δ)⌉` is read as `0`
   and the bound is trivial. In that case all candidates always tie, so the
   winner is never unique.
9. **Not modelled.** The optional opening of unused ballots (also excluded from
   Theorem 3), the network, and how `BB` is implemented. `BB` is the single
   `Info` that every verifier reads.

### What stays on paper

* **Lemma 2 (product-opening hiding) and Theorem 3 (privacy and
  receipt-freeness).** They are computational: they reduce to DDH and use
  complexity leveraging. They are in `../easycrypt`, not in Lean.
* **That the model matches the protocol description.** The definitions in
  `PDemos/Protocol.lean`, `PDemos/Correctness.lean` and `PDemos/Game.lean` are
  read against `newProtocol.tex` and `security.tex` by hand. The points where
  they differ are listed above.

### How the coin bound is modelled

`coins N : PMF (List Bool)` draws `N` independent fair coins in order, using
mathlib's `PMF` monad. An unbounded adversary can be taken to be deterministic.
Its behaviour before each honest coin is then a function of the coins drawn so
far: a `Strategy : List Bool → Option Bool`, which leaves the next coin free or
names its target bit. `prob_succeeds_le` states that, for every strategy, the
probability that at least `k` coins are targeted and all of them hit is at most
`2^{-k}`. This covers both uses in the paper. In Lemma `amplified`, every honest
coin is targeted at a bit of the fixed string `c⃗*`. In Step 4, the unit coins
are targeted adaptively: for a clashed tag, the target is the first holder's
coin. `PDemos/Game.lean` turns the game's honest coins into such strategies
(`normStrat`, `succeeds_normStrat`), so the game's winning probability is bounded
by `e2e_error_bound`.

## Conventions that differ from the paper

* Indices are 0-based. Candidate `P_j`, encoded as `x^{j-1}`, is `j-1 : Fin m`,
  encoded as `x ^ (j-1)`. Ranks are `Fin m` too, so `w₁` is `w 0`.
* A ranking is `ω : Equiv.Perm (Fin m)`, where `ω i` is the candidate at rank `i`.
  A profile of `n` cast ballots is `Fin n → Equiv.Perm (Fin m)`. In Step 3, the
  profiles are multisets of rankings, and abstentions are simply absent.
* The weights are `w : Fin m → ℕ` with `Antitone w`. `Δ = w₁ − wₘ` is
  `weightRange w hm`, which takes values in `ℤ`.
* Score mode assumes `w i ≤ W` for all `i` and `n * W < x`. The paper's choice
  `x = max{n·W, m} + 1` satisfies this.
* The group is any commutative group `G` with `Nat.card G = q` prime, and the
  generator is any `g ≠ 1`. The key `h : G` is arbitrary. Exponents are in
  `ZMod q`, and `x ^ₘ a` stands for `x ^ a.val`. The values of `𝒳` are the
  residues of the natural numbers `x ^ j`.
* The coin string is cut into `κ` blocks of `β` bits with `n ≤ κβ` and
  `2^β ≤ q`, and the last block is padded with zeros. The paper's "fewer than
  `⌊log₂ q⌋` bits" implies `2^β ≤ q`.

## Building

```bash
cd formal
lake exe cache get   # downloads prebuilt mathlib (~5 GB in .lake/, gitignored)
lake build
```

The toolchain is pinned in `lean-toolchain` to Lean v4.35.0, and mathlib is pinned
to the matching tag in `lakefile.toml` and `lake-manifest.json`. The build succeeds
with no `sorry`. Every theorem depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). You can confirm this with
`#print axioms`, for example:

```lean
import PDemos
#print axioms PDemos.correctness
#print axioms PDemos.e2e_verifiability
#print axioms PDemos.e2e_verifiability_rand
#print axioms PDemos.margin_verifiability
```
