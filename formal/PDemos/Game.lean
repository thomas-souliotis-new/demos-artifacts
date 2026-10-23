import PDemos.Protocol
import PDemos.Coins

/-!
# The game `G_e2e` (`security.tex`, Section 4.3) as a probabilistic program

The adversary `𝒜` plays the `EA` and all corrupted voters, and is computationally
unbounded. We model it as follows.

* **Setup.** `𝒜` posts `Pub` (`pub`).
* **Scheduling.** Before each honest voter, `𝒜` sees the honest coins drawn so far
  (a `List Bool`, oldest first). From them it decides whether to run another
  honest voter (`more`), which paper ballot that voter holds (`ballot`; the same
  tag may be handed to several voters) and which ranking it chooses (`rank`). The
  challenger then draws a fresh fair coin. There are at most `n` honest voters.
* **Final `BB`.** From all honest coins, `𝒜` posts the cast ballots and the Tally
  (`post`). Corrupted voters act only through what `𝒜` posts.

Everything `𝒜` sees is a function of the honest coins, because the receipts of
honest voters are computed from their paper ballots, rankings and coins. So a
deterministic adversary is exactly such a tuple of functions. A randomised
adversary is a distribution `μ` over them (`gameE2ERand`); its winning
probability is an average, so the bound for deterministic adversaries carries over
(`PDemos.e2e_verifiability_rand`).

`honestCoins` draws the coins lazily, one fresh coin per scheduled honest voter.
`honestCoins_eq` shows that this is the same distribution as drawing `n` coins up
front (`PDemos.coins`) and reading them while `𝒜` keeps scheduling (`runCoins`).

The extractor `𝓔` is that of Appendix B. It reads committed values through
`cval`, which is well defined by perfect binding.
-/

namespace PDemos

open Finset

variable {G : Type*} [CommGroup G] {q n m κ : ℕ}

/-- A deterministic adversary in `G_e2e` (see the module docstring). -/
structure Adversary (G : Type*) (q n m κ : ℕ) where
  pub : Pub G q n m κ
  more : List Bool → Bool
  ballot : List Bool → PaperBallot q n m
  rank : List Bool → Equiv.Perm (Fin m)
  post : List Bool → Tau q n m κ

/-! ### Drawing the honest coins -/

/-- Draw a fresh fair coin for each honest voter that `𝒜` schedules, at most `k`
more; `acc` holds the coins drawn so far. -/
noncomputable def honestCoins (more : List Bool → Bool) : ℕ → List Bool → PMF (List Bool)
  | 0, acc => PMF.pure acc
  | k + 1, acc =>
    if more acc then fairCoin.bind fun b => honestCoins more k (acc ++ [b]) else PMF.pure acc

/-- Read pre-drawn coins while `𝒜` keeps scheduling honest voters. -/
def runCoins (more : List Bool → Bool) : List Bool → List Bool → List Bool
  | acc, [] => acc
  | acc, b :: c => if more acc then runCoins more (acc ++ [b]) c else acc

lemma runCoins_of_not {more : List Bool → Bool} {acc : List Bool} (h : more acc = false)
    (c : List Bool) : runCoins more acc c = acc := by
  cases c <;> simp [runCoins, h]

/-- **Lazy and eager sampling agree.** -/
theorem honestCoins_eq (more : List Bool → Bool) :
    ∀ k acc, honestCoins more k acc = (coins k).map (runCoins more acc) := by
  intro k
  induction k with
  | zero => intro acc; simp [honestCoins, coins, PMF.pure_map, runCoins]
  | succ k ih =>
    intro acc
    by_cases h : more acc
    · simp only [honestCoins, h, ite_true, coins, PMF.map_bind, PMF.map_comp, ih]
      congr 1
      funext b
      congr 1
      funext c
      simp [runCoins, h]
    · have h' : more acc = false := by simpa using h
      simp only [honestCoins, h', Bool.false_eq_true, ite_false]
      rw [show runCoins more acc = Function.const _ acc from funext (runCoins_of_not h'),
        PMF.map_const]

/-- What `runCoins` returns: a prefix of the pre-drawn coins, read while `more`
holds, and stopped only where `more` fails. -/
lemma runCoins_spec (more : List Bool → Bool) :
    ∀ c acc : List Bool, ∃ K ≤ c.length, runCoins more acc c = acc ++ c.take K ∧
      (∀ i < K, more (acc ++ c.take i) = true) ∧
      (K < c.length → more (acc ++ c.take K) = false) := by
  intro c
  induction c with
  | nil => intro acc; exact ⟨0, le_rfl, by simp [runCoins], by simp, by simp⟩
  | cons b c ih =>
    intro acc
    by_cases h : more acc
    · obtain ⟨K, hK, hrun, hmore, hstop⟩ := ih (acc ++ [b])
      refine ⟨K + 1, by simpa using hK, ?_, ?_, ?_⟩
      · simp [runCoins, h, hrun]
      · intro i hi
        cases i with
        | zero => simpa using h
        | succ i => simpa using hmore i (by omega)
      · intro hlt
        simpa using hstop (by simp at hlt; omega)
    · have h' : more acc = false := by simpa using h
      exact ⟨0, Nat.zero_le _, by simp [runCoins_of_not h'], by simp, by simpa using h'⟩

/-! ### Strategies read off the game -/

/-- Read hits along the coins: if every targeted coin hits, `hits` counts the
targeted coins. -/
lemma hits_spec (T : Strategy) (cs : List Bool)
    (hc : ∀ i (hi : i < cs.length) t, T (cs.take i) = some t → cs[i] = t) :
    hits T cs = some ((List.range cs.length).countP fun i => (T (cs.take i)).isSome) := by
  induction cs generalizing T with
  | nil => simp [hits]
  | cons b cs ih =>
    have ih' := ih (fun l => T (b :: l)) (fun i hi t ht => by
      have := hc (i + 1) (by simp; omega) t (by simpa using ht)
      rwa [List.getElem_cons_succ] at this)
    have hcount : (List.range (b :: cs).length).countP (fun i => (T ((b :: cs).take i)).isSome)
        = (if (T []).isSome then 1 else 0)
          + (List.range cs.length).countP fun i => (T (b :: cs.take i)).isSome := by
      rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map]
      simp only [List.take_zero]
      rw [add_comm]
      congr 1
    rw [hcount]
    cases hT : T [] with
    | none => simp [hits, hT, ih']
    | some t =>
      have hb : b = t := hc 0 (by simp) t (by simpa using hT)
      subst hb
      simp [hits, hT, ih', add_comm]

/-- Run a base strategy only while `𝒜` keeps scheduling honest voters: past the
last honest voter, no coin is targeted. -/
def normStrat (more : List Bool → Bool) (base : List Bool → Option Bool) : Strategy :=
  fun p => if ∀ i ≤ p.length, more (p.take i) = true then base p else none

/-- To show that `normStrat more base` succeeds on the pre-drawn coins, it suffices
to look at the honest coins `runCoins more [] cs`: every coin that `base` targets
hits, and at least `k` coins are targeted. -/
theorem succeeds_normStrat (more : List Bool → Bool) (base : List Bool → Option Bool)
    (cs : List Bool) (k : ℕ)
    (hhit : ∀ i (hi : i < (runCoins more [] cs).length) t,
      base ((runCoins more [] cs).take i) = some t → (runCoins more [] cs)[i] = t)
    (hk : k ≤ (List.range (runCoins more [] cs).length).countP
      fun i => (base ((runCoins more [] cs).take i)).isSome) :
    Succeeds (normStrat more base) k cs := by
  obtain ⟨K, hK, hrun, hmore, hstop⟩ := runCoins_spec more cs []
  simp only [List.nil_append] at hrun hmore hstop
  have hlen : (cs.take K).length = K := by simp [hK]
  simp only [hrun, hlen] at hhit hk
  -- before `K` the strategy is `base`, from `K` on it is `none`
  have hbefore : ∀ i < K, normStrat more base (cs.take i) = base (cs.take i) := by
    intro i hi
    simp only [normStrat]
    rw [ite_eq_left]
    intro i' hi'
    rw [List.take_take, min_eq_left (by simp at hi'; omega)]
    exact hmore i' (by simp at hi'; omega)
  have hafter : ∀ i, K ≤ i → i < cs.length → normStrat more base (cs.take i) = none := by
    intro i hi hic
    simp only [normStrat]
    rw [ite_eq_right]
    push Not
    refine ⟨K, by simp; omega, ?_⟩
    rw [List.take_take, min_eq_left hi]
    simpa using hstop (by omega)
  have htake : ∀ i < K, (cs.take K).take i = cs.take i := fun i hi => by
    rw [List.take_take, min_eq_left hi.le]
  refine ⟨_, hits_spec _ cs fun i hi t ht => ?_, ?_⟩
  · by_cases hiK : i < K
    · rw [hbefore i hiK, ← htake i hiK] at ht
      have := hhit i hiK t ht
      simpa [List.getElem_take] using this
    · rw [hafter i (by omega) hi] at ht
      exact absurd ht (by simp)
  · refine hk.trans ?_
    calc (List.range K).countP (fun i => (base ((cs.take K).take i)).isSome)
        = (List.range K).countP (fun i => (normStrat more base (cs.take i)).isSome) :=
          List.countP_congr fun i hi => by
            rw [List.mem_range] at hi
            rw [htake i hi, hbefore i hi]
      _ ≤ (List.range cs.length).countP (fun i => (normStrat more base (cs.take i)).isSome) :=
          (List.range_sublist.2 hK).countP_le

/-! ### The honest voters of a run -/

namespace Adversary

variable (A : Adversary G q n m κ) (h : List Bool)

/-- The final `BB` after the honest coins `h`. -/
def info : Info G q n m κ := ⟨A.pub, A.post h⟩

/-- Paper ballot and ranking of the `i`-th honest voter; its coin is `h[i]`. -/
def ballotOf (i : Fin h.length) : PaperBallot q n m := A.ballot (h.take i)
def rankOf (i : Fin h.length) : Equiv.Perm (Fin m) := A.rank (h.take i)

/-- The receipt `α` of the `i`-th honest voter, computed by the challenger. -/
def receipt (i : Fin h.length) : Receipt q n m :=
  ⟨(A.ballotOf h i).tag, h[i], (A.ballotOf h i).code (!h[i]),
    ⟨h[i], fun r => (A.ballotOf h i).code h[i] (A.rankOf h i r)⟩⟩

/-- The honest voters' rankings. -/
def honestRanks : Multiset (Equiv.Perm (Fin m)) := (univ : Finset (Fin h.length)).val.map (A.rankOf h)

end Adversary

/-! ### The extractor `𝓔` (Appendix B) -/

section Extractor

open Classical in
/-- The value committed in `c` (unique by perfect binding). -/
noncomputable def cval (g key : G) (c : G × G) : ZMod q :=
  if hc : ∃ v, CommitsTo g key c v then hc.choose else 0

variable (P : Params G m) (I : Info G q n m κ)

open Classical in
/-- The choice extracted from the cast ballot of tag `t`: the ranking `σ` whose
encodings are committed at ranks `0, …, m-1`, if there is one. -/
noncomputable def extractOne (t : Fin n) : Option (Equiv.Perm (Fin m)) :=
  if hσ : ∃ σ : Equiv.Perm (Fin m), ∀ i, cval P.g I.pub.key (I.routed t i) = encX q P.x (σ i)
  then some hσ.choose else none

open Classical in
/-- The cast tags that no honest receipt holds, in tag order. -/
noncomputable def extractTags (αs : List (Receipt q n m)) : List (Fin n) :=
  ((univ : Finset (Fin n)).filter fun t => (I.tau.psi t).isSome ∧ t ∉ αs.map Receipt.tag).sort
    (· ≤ ·)

/-- `𝓔(info, {α})`: one extracted choice per cast ballot outside the honest
receipts, ordered by tag, or `⊥` if one of them encodes no ranking. -/
noncomputable def extractor (αs : List (Receipt q n m)) : Option (List (Equiv.Perm (Fin m))) :=
  if (extractTags I αs).all fun t => (extractOne P I t).isSome then
    some ((extractTags I αs).filterMap (extractOne P I))
  else none

end Extractor

/-! ### The game -/

variable (P : Params G m) (θ d : ℕ)

/-- `G_e2e` outputs `1` on the honest coins `h` iff (1) `|𝒱_succ| ≥ θ`, (2) every
honest voter verifies, and (3) either `𝓔` outputs `⊥`, or the result deviates
from `f` of the honest choices and the extracted ones by at least `d`. The
extracted choices are assigned to the `n - |𝒱_succ|` other voters in order; the
surplus is discarded and voters left without a choice abstain. -/
def Win (A : Adversary G q n m κ) (h : List Bool) : Prop :=
  θ ≤ h.length ∧ (∀ i, Verify P (A.info h) (A.receipt h i)) ∧
    match extractor P (A.info h) (List.ofFn (A.receipt h)) with
    | none => True
    | some ε => d ≤ dist P.w (Result P (A.info h))
        (elect P.w P.mode (A.honestRanks h + ↑(ε.take (n - h.length))))

open Classical in
/-- **The game `G_e2e`** against a deterministic adversary, as a distribution on
its output bit. -/
noncomputable def gameE2E (A : Adversary G q n m κ) : PMF Bool :=
  (honestCoins A.more n []).map fun h => decide (Win P θ d A h)

/-- `G_e2e` against a randomised adversary `μ`. -/
noncomputable def gameE2ERand (μ : PMF (Adversary G q n m κ)) : PMF Bool :=
  μ.bind (gameE2E P θ d)

/-- `Pr[G_e2e = 1]`, as a probability over `n` pre-drawn fair coins. -/
theorem gameE2E_apply_true (A : Adversary G q n m κ) :
    gameE2E P θ d A true = (coins n).toOuterMeasure {c | Win P θ d A (runCoins A.more [] c)} := by
  classical
  rw [← PMF.toOuterMeasure_apply_singleton, gameE2E, PMF.toOuterMeasure_map_apply,
    honestCoins_eq, PMF.toOuterMeasure_map_apply]
  congr 1
  ext c
  simp

end PDemos
