import PDemos.E2E
import PDemos.ScoreBound

/-!
# Corollary `margin`, end to end (`security.tex`, `appendix.tex`)

Let `M` be the true margin between the winner and the runner-up, and
`Δ = w₁ - wₘ` (`weightRange`). An adversary that changes the winner without
detection wins with probability at most

  `2^{-⌈M/(2Δ)⌉} + 2nm · 2^{-θ}`  (`margin_verifiability`).

The game `G_margin` is `G_e2e` with condition (3a) replaced by "the winner
changes" (`WinnerChanged`): in the true result, `f` of the honest and the
extracted choices, some candidate `c` leads every other candidate by at least `M`,
and in `Result(info)` some other candidate scores at least as much as `c`. A tie
in `Result(info)` counts as a change, and "winner" is read on the score vector
`sc_w`, in both modes.

The proof is that of Theorem 2 with one change in Step 3. `win_good_val` bounds
how far the result moves any functional `φ` of the counted rankings with values in
`[lo, hi]`, `lo ≤ 0 ≤ hi`: by `(hi - lo) · U`. For `φ = score_c - score_{c'}`,
`score_pair_le` gives `[-Δ, Δ]`, so one unit moves the difference `s_c - s_{c'}`
by at most `2Δ`. Changing the winner moves it by at least `M`, hence
`U ≥ ⌈M/(2Δ)⌉` (`win_margin_units`), and Step 4 and Lemma `amplified` apply as
before.
-/

namespace PDemos

open Finset
open scoped ENNReal

variable {G : Type*} [CommGroup G] {q n m κ : ℕ}

/-- **The winner changes.** In the true result `R₀`, candidate `c` leads every
other candidate by at least `M`; in the posted result `R`, some other candidate
scores at least as much as `c`. -/
def WinnerChanged (w : Fin m → ℕ) (M : ℕ) (R R₀ : Outcome m) : Prop :=
  ∃ c, (∀ c', c' ≠ c → scw w R₀ c' + M ≤ scw w R₀ c) ∧ ∃ c', c' ≠ c ∧ scw w R c ≤ scw w R c'

/-! ### The game `G_margin` -/

variable (P : Params G m) (θ M : ℕ)

/-- `G_margin` outputs `1` on the honest coins `h` iff (1) `|𝒱_succ| ≥ θ`, (2) every
honest voter verifies, and (3) either `𝓔` outputs `⊥`, or the winner of
`Result(info)` differs from the winner of `f` of the honest and the extracted
choices, which leads by at least `M`. Conditions (1), (2), (3b) and the use of the
extracted choices are those of `Win`. -/
def WinMargin (A : Adversary G q n m κ) (h : List Bool) : Prop :=
  θ ≤ h.length ∧ (∀ i, Verify P (A.info h) (A.receipt h i)) ∧
    match extractor P (A.info h) (List.ofFn (A.receipt h)) with
    | none => True
    | some ε => WinnerChanged P.w M (Result P (A.info h))
        (elect P.w P.mode (A.honestRanks h + ↑(ε.take (n - h.length))))

open Classical in
/-- **The game `G_margin`** against a deterministic adversary. -/
noncomputable def gameMargin (A : Adversary G q n m κ) : PMF Bool :=
  (honestCoins A.more n []).map fun h => decide (WinMargin P θ M A h)

/-- `G_margin` against a randomised adversary `μ`. -/
noncomputable def gameMarginRand (μ : PMF (Adversary G q n m κ)) : PMF Bool :=
  μ.bind (gameMargin P θ M)

/-- `Pr[G_margin = 1]`, as a probability over `n` pre-drawn fair coins. -/
theorem gameMargin_apply_true (A : Adversary G q n m κ) :
    gameMargin P θ M A true
      = (coins n).toOuterMeasure {c | WinMargin P θ M A (runCoins A.more [] c)} := by
  classical
  rw [← PMF.toOuterMeasure_apply_singleton, gameMargin, PMF.toOuterMeasure_map_apply,
    honestCoins_eq, PMF.toOuterMeasure_map_apply]
  congr 1
  ext c
  simp

variable {P θ M} {A : Adversary G q n m κ} {h : List Bool}

/-- A win in `G_margin` meets conditions (1) and (2) of `G_e2e`, so it is a win in
`G_e2e` with deviation `0`. -/
lemma WinMargin.win (hwin : WinMargin P θ M A h) : Win P θ 0 A h := by
  unfold Win
  refine ⟨hwin.1, hwin.2.1, ?_⟩
  split <;> simp

/-! ### Step 3 for a pairwise score difference -/

/-- **Steps 1–3 for Corollary `margin`.** If `G_margin` is won and `¬Z`, changing
the winner costs at least `⌈M / (2Δ)⌉` units: later holders of a tag, and first
holders whose cast part is inconsistent. -/
theorem win_margin_units [Fact q.Prime] (hq : Nat.card G = q) (hg : P.g ≠ 1) (hm : 0 < m)
    (hw : Antitone P.w) (hx : m < P.x) (hxq : P.x ^ m ≤ q) (hnx : n * P.W hm < P.x)
    (hθ : 1 ≤ θ) (hwin : WinMargin P θ M A h) (hgood : ¬ Bad P (A.info h)) :
    ⌈(M : ℚ) / (2 * weightRange P.w hm)⌉₊ ≤ (later A h).card + (badFirsts P A h).card := by
  obtain ⟨σ, hres, ε, hext, hval⟩ := win_good_val hq hg hm hw hx hxq hnx hθ hwin.win hgood
  have h3 : WinnerChanged P.w M (Result P (A.info h))
      (elect P.w P.mode (A.honestRanks h + ↑(ε.take (n - h.length)))) := by
    have := hwin.2.2
    rwa [hext] at this
  obtain ⟨c, hlead, c', hne, hflip⟩ := h3
  set Ms := A.honestRanks h + ↑(ε.take (n - h.length))
  set Δ := weightRange P.w hm with hΔ
  set U := (later A h).card + (badFirsts P A h).card
  have hΔ0 : 0 ≤ Δ := weightRange_nonneg hw hm
  -- one unit moves `s_c - s_{c'}` by at most `2Δ`
  have hpair := hval (fun τ => (score P.w τ c : ℤ) - score P.w τ c') (-Δ) Δ (by linarith) hΔ0
    fun τ => abs_le.1 (score_pair_le hw hm τ c c')
  rw [msVal_sub, msVal_score, msVal_score, sum_sub_distrib] at hpair
  -- the true result leads by `M`, the posted one does not
  have hs : (msScore P.w Ms c' : ℤ) + M ≤ msScore P.w Ms c := by
    have := hlead c' hne
    rw [scw_elect, scw_elect] at this
    exact_mod_cast this
  have hr : (∑ t ∈ (A.info h).castSet, score P.w (σ t) c : ℕ)
      ≤ ∑ t ∈ (A.info h).castSet, score P.w (σ t) c' := by
    rw [← hres, ← hres]; exact hflip
  have hr' : (∑ t ∈ (A.info h).castSet, (score P.w (σ t) c : ℤ))
      ≤ ∑ t ∈ (A.info h).castSet, (score P.w (σ t) c' : ℤ) := by exact_mod_cast hr
  have key : (M : ℤ) ≤ 2 * Δ * U := by
    rw [abs_le] at hpair
    linarith [hpair.1]
  rw [Nat.ceil_le]
  rcases hΔ0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hpos' : (0 : ℚ) < 2 * (Δ : ℚ) := by exact_mod_cast (by linarith : (0 : ℤ) < 2 * Δ)
    rw [div_le_iff₀ hpos']
    have : ((M : ℤ) : ℚ) ≤ ((2 * Δ * U : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this
    linarith

/-! ### Corollary `margin` -/

/-- **Corollary `margin`.** For every adversary `𝒜` of `G_margin` (a deterministic,
adaptive, computationally unbounded `EA` that also plays the corrupted voters),
with the extractor `𝓔` of Appendix B and `Δ = w₁ - wₘ`,

  `Pr[G_margin = 1] ≤ 2^{-⌈M/(2Δ)⌉} + 2nm · 2^{-θ}`.

The hypotheses are those of `e2e_verifiability`. -/
theorem margin_verifiability [Fact q.Prime] (hq : Nat.card G = q) (P : Params G m)
    (hg : P.g ≠ 1) (hm : 0 < m) (hw : Antitone P.w) (hx : m < P.x) (hxq : P.x ^ m ≤ q)
    (hnx : n * P.W hm < P.x) (hn : n ≤ κ * P.β) (hβ : 2 ^ P.β ≤ q) (θ M : ℕ) (hθ : 1 ≤ θ)
    (A : Adversary G q n m κ) :
    gameMargin P θ M A true
      ≤ 2⁻¹ ^ ⌈(M : ℚ) / (2 * weightRange P.w hm)⌉₊ + 2 * n * m * 2⁻¹ ^ θ := by
  rw [gameMargin_apply_true]
  have hbound := e2e_error_bound n (fun c => WinMargin P θ M A (runCoins A.more [] c))
    (fun c => WinMargin P θ M A (runCoins A.more [] c) ∧ Bad P (A.info (runCoins A.more [] c)))
    (fun c => WinMargin P θ M A (runCoins A.more [] c) ∧ ¬ Bad P (A.info (runCoins A.more [] c)))
    (fun c hc => by
      by_cases hb : Bad P (A.info (runCoins A.more [] c))
      exacts [Or.inl ⟨hc, hb⟩, Or.inr ⟨hc, hb⟩])
    (univ : Finset (Fin n × Bool × Fin m)) (fun j => normStrat A.more (baseZ P A j)) θ
    (fun c hc => by
      obtain ⟨j, hj1, hj2⟩ := win_bad_hits hq hn hβ hθ hc.1.win hc.2
      exact ⟨j, mem_univ _, succeeds_normStrat _ _ c θ hj1 hj2⟩)
    (normStrat A.more (base4 P A)) ⌈(M : ℚ) / (2 * weightRange P.w hm)⌉₊
    (fun c hc => succeeds_normStrat _ _ c _ (win_good_hits hx hxq hc.1.win)
      ((win_margin_units hq hg hm hw hx hxq hnx hθ hc.1 hc.2).trans
        (win_count hx hxq hc.1.win)))
  refine hbound.trans_eq ?_
  congr 1
  rw [card_univ]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  push_cast
  ring

/-- **Corollary `margin` for randomised adversaries.** -/
theorem margin_verifiability_rand [Fact q.Prime] (hq : Nat.card G = q) (P : Params G m)
    (hg : P.g ≠ 1) (hm : 0 < m) (hw : Antitone P.w) (hx : m < P.x) (hxq : P.x ^ m ≤ q)
    (hnx : n * P.W hm < P.x) (hn : n ≤ κ * P.β) (hβ : 2 ^ P.β ≤ q) (θ M : ℕ) (hθ : 1 ≤ θ)
    (μ : PMF (Adversary G q n m κ)) :
    gameMarginRand P θ M μ true
      ≤ 2⁻¹ ^ ⌈(M : ℚ) / (2 * weightRange P.w hm)⌉₊ + 2 * n * m * 2⁻¹ ^ θ := by
  rw [gameMarginRand, PMF.bind_apply]
  calc ∑' A, μ A * gameMargin P θ M A true
      ≤ ∑' A, μ A * (2⁻¹ ^ ⌈(M : ℚ) / (2 * weightRange P.w hm)⌉₊ + 2 * n * m * 2⁻¹ ^ θ) :=
        ENNReal.tsum_le_tsum fun A => by
          gcongr
          exact margin_verifiability hq P hg hm hw hx hxq hnx hn hβ θ M hθ A
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end PDemos
