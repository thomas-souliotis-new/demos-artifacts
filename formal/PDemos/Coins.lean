import Mathlib

/-!
# Fair coins against adaptive targets (`appendix.tex`, Lemma `amplified` and Step 4)

Both probabilistic arguments in the proof of Theorem 2 rest on one fact: honest
voters' fair coins, drawn one after another, must each hit a target bit that is
fixed before the coin is drawn. We model the honest coins in drawing order as
`coins N : PMF (List Bool)`, `N` independent fair coins built with mathlib's `PMF`
monad. An unbounded adversary may be taken to be deterministic, so its behaviour
is a function of the coins drawn so far. A `Strategy` is such a function. Before
each coin it either leaves the coin free (`none`) or names the target bit that the
coin must hit (`some t`). The adversary chooses which coins to target, how many,
and what the targets are, adaptively.

`Succeeds T k c` says that, along the coins `c`, every targeted coin hit its
target and at least `k` coins were targeted.

* `prob_succeeds_le`: `Pr[Succeeds T k] ≤ 2^{-k}` for every strategy `T`.
* `prob_exists_succeeds_le`: the union bound over a finite family of strategies.
* `e2e_error_bound`: the final addition in the proof of Theorem 2.

How the game is mapped to strategies is argued in the paper:

* **Lemma `amplified`**: for a posted commitment `E*` outside `𝒳`, every honest
  coin is targeted at the bit of `c⃗*` (`PDemos.amplified_coins_unique`) at the
  position of the voter's tag, so `k = |𝒱_succ| ≥ θ`. There is one strategy per
  posted commitment, at most `2nm` in all.
* **Step 4**: the targeted coins are those of the honest holders of a tag with
  exactly one inconsistent part (target: the coin that casts it) and of every
  later holder of a clashed tag (target: the first holder's coin). Condition (2)
  forces all of them to hit, and `U ≥ k` gives at least `k` of them
  (`PDemos.faithful_of_consistent`, `PDemos.units_of_deviation`).
-/

namespace PDemos

open scoped ENNReal
open MeasureTheory

/-- A fair coin. -/
noncomputable def fairCoin : PMF Bool :=
  PMF.ofFintype (fun _ => 2⁻¹) (by rw [Fintype.sum_bool, ENNReal.inv_two_add_inv_two])

/-- `N` independent fair coins, drawn in order. -/
noncomputable def coins : ℕ → PMF (List Bool)
  | 0 => PMF.pure []
  | N + 1 => fairCoin.bind fun b => (coins N).map (b :: ·)

/-- An adaptive targeting strategy. Given the coins drawn so far (oldest first),
it leaves the next coin free (`none`) or fixes its target (`some t`). -/
abbrev Strategy := List Bool → Option Bool

/-- Run a strategy along the coins `c`: `some u` if every targeted coin hit its
target and `u` coins were targeted, `none` as soon as a targeted coin misses. -/
def hits (T : Strategy) : List Bool → Option ℕ
  | [] => some 0
  | b :: c =>
    match T [] with
    | none => hits (fun l => T (b :: l)) c
    | some t => if b = t then (hits (fun l => T (b :: l)) c).map (· + 1) else none

/-- Every targeted coin hit its target, and at least `k` coins were targeted. -/
def Succeeds (T : Strategy) (k : ℕ) (c : List Bool) : Prop :=
  ∃ u, hits T c = some u ∧ k ≤ u

lemma succeeds_nil {T : Strategy} {k : ℕ} : Succeeds T k [] ↔ k = 0 := by
  simp [Succeeds, hits]

lemma succeeds_zero {T : Strategy} {b : Bool} {c : List Bool} (hT : T [] = none) {k : ℕ} :
    Succeeds T k (b :: c) ↔ Succeeds (fun l => T (b :: l)) k c := by
  simp [Succeeds, hits, hT]

lemma succeeds_succ {T : Strategy} {b t : Bool} {c : List Bool} (hT : T [] = some t) {k : ℕ} :
    Succeeds T (k + 1) (b :: c) ↔ b = t ∧ Succeeds (fun l => T (b :: l)) k c := by
  simp only [Succeeds, hits, hT]
  rcases eq_or_ne b t with rfl | hb
  · simp only [ite_true, Option.map_eq_some_iff, true_and]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, hk⟩
      exact ⟨u, hu, by omega⟩
    · rintro ⟨u, hu, hk⟩
      exact ⟨u + 1, ⟨u, hu, rfl⟩, by omega⟩
  · simp [hb]

/-- Splitting off the first coin. -/
lemma coins_succ_apply (N : ℕ) (s : Set (List Bool)) :
    (coins (N + 1)).toOuterMeasure s
      = 2⁻¹ * (coins N).toOuterMeasure {c | false :: c ∈ s}
        + 2⁻¹ * (coins N).toOuterMeasure {c | true :: c ∈ s} := by
  rw [coins, PMF.toOuterMeasure_bind_apply, tsum_fintype, Fintype.sum_bool, add_comm]
  simp only [fairCoin, PMF.ofFintype_apply, PMF.toOuterMeasure_map_apply]
  rfl

/-- **Fair coins against adaptive targets.** Whatever the strategy, the probability
that at least `k` coins are targeted and every targeted coin hits is at most
`2^{-k}`. -/
theorem prob_succeeds_le (N : ℕ) :
    ∀ (T : Strategy) (k : ℕ), (coins N).toOuterMeasure {c | Succeeds T k c} ≤ 2⁻¹ ^ k := by
  induction N with
  | zero =>
    intro T k
    rw [coins, PMF.toOuterMeasure_pure_apply]
    split_ifs with h
    · rw [Set.mem_ofPred_eq, succeeds_nil] at h
      simp [h]
    · exact zero_le
  | succ N ih =>
    intro T k
    rw [coins_succ_apply]
    cases hT : T [] with
    | none =>
      -- a free coin: both halves are bounded by the induction hypothesis
      simp only [Set.mem_ofPred_eq, succeeds_zero hT]
      calc 2⁻¹ * (coins N).toOuterMeasure {c | Succeeds (fun l => T (false :: l)) k c}
            + 2⁻¹ * (coins N).toOuterMeasure {c | Succeeds (fun l => T (true :: l)) k c}
          ≤ 2⁻¹ * 2⁻¹ ^ k + 2⁻¹ * 2⁻¹ ^ k := by gcongr <;> exact ih _ k
        _ = 2⁻¹ ^ k := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    | some t =>
      cases k with
      | zero =>
        rw [← coins_succ_apply, pow_zero]
        exact (measure_mono (Set.subset_univ _)).trans_eq
          ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _))
      | succ k =>
        -- a targeted coin: only the half where it hits survives
        simp only [Set.mem_ofPred_eq, succeeds_succ hT]
        have hb : ∀ b, (coins N).toOuterMeasure
            {c | b = t ∧ Succeeds (fun l => T (b :: l)) k c} ≤ if b = t then 2⁻¹ ^ k else 0 := by
          intro b
          split_ifs with h
          · exact (measure_mono fun c hc => hc.2).trans (ih _ k)
          · simp [h]
        calc _ ≤ (2⁻¹ : ℝ≥0∞) * (if false = t then 2⁻¹ ^ k else 0)
              + 2⁻¹ * (if true = t then 2⁻¹ ^ k else 0) := by gcongr <;> exact hb _
          _ = 2⁻¹ ^ (k + 1) := by cases t <;> simp [pow_succ']

/-- **Union bound** over a finite family of strategies, as in Lemma `amplified`
(one strategy per posted commitment outside `𝒳`). -/
theorem prob_exists_succeeds_le {ι : Type*} (I : Finset ι) (T : ι → Strategy) (N k : ℕ) :
    (coins N).toOuterMeasure {c | ∃ i ∈ I, Succeeds (T i) k c} ≤ I.card * 2⁻¹ ^ k := by
  have hset : {c | ∃ i ∈ I, Succeeds (T i) k c} = ⋃ i ∈ I, {c | Succeeds (T i) k c} := by
    ext c; simp
  rw [hset]
  calc _ ≤ ∑ i ∈ I, (coins N).toOuterMeasure {c | Succeeds (T i) k c} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ I, (2⁻¹ : ℝ≥0∞) ^ k := Finset.sum_le_sum fun i _ => prob_succeeds_le N (T i) k
    _ = I.card * 2⁻¹ ^ k := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Theorem 2, final step.** Let `Win` be the event that the game outputs `1`, `Z`
the event of Lemma `amplified`, and `A` the event `Win ∧ ¬Z`. If `Z` forces one of
at most `M` strategies to hit `θ` targets, and `A` forces a strategy to hit `k`
targets, then `Pr[Win] ≤ 2^{-k} + M · 2^{-θ}`. With `k = ⌈d / w₁⌉` and `M = 2nm`
this is the bound `ε_e2e` of Theorem 2. -/
theorem e2e_error_bound {ι : Type*} (N : ℕ) (Win Z A : List Bool → Prop)
    (hWin : ∀ c, Win c → Z c ∨ A c) (I : Finset ι) (T : ι → Strategy) (θ : ℕ)
    (hZ : ∀ c, Z c → ∃ i ∈ I, Succeeds (T i) θ c) (T' : Strategy) (k : ℕ)
    (hA : ∀ c, A c → Succeeds T' k c) :
    (coins N).toOuterMeasure {c | Win c} ≤ 2⁻¹ ^ k + I.card * 2⁻¹ ^ θ := by
  calc (coins N).toOuterMeasure {c | Win c}
      ≤ (coins N).toOuterMeasure ({c | Succeeds T' k c} ∪ {c | ∃ i ∈ I, Succeeds (T i) θ c}) :=
        measure_mono fun c hc => (hWin c hc).elim (fun hz => Or.inr (hZ c hz))
          (fun ha => Or.inl (hA c ha))
    _ ≤ _ := (measure_union_le _ _).trans
        (add_le_add (prob_succeeds_le N T' k) (prob_exists_succeeds_le I T N θ))

/-- `2⁻¹ ^ k` is `2^{-k}`. -/
lemma inv_two_pow (k : ℕ) : (2⁻¹ : ℝ≥0∞) ^ k = (2 ^ k)⁻¹ := ENNReal.inv_pow.symm

end PDemos
