import PDemos.Tally

/-!
# Per-ballot score bound (`security.tex`, Theorem 2 and Corollary `margin`)

With weights `w₁ ≥ ⋯ ≥ wₘ ≥ 0` (here `w : Fin m → ℕ` antitone, 0-indexed) and
`Δ = w₁ - wₘ`, replacing one ballot's ranking by any other ranking changes every
candidate's positional score by at most `Δ`. Consequently, profiles that differ
in at most `k` ballots have scores within `k · Δ` of each other. Corollary
`margin` uses this bound per unit of attack.
-/

namespace PDemos

open Finset

variable {n m : ℕ}

/-- The weight range `Δ = w₁ - wₘ` (as an integer). -/
def weightRange (w : Fin m → ℕ) (hm : 0 < m) : ℤ :=
  (w ⟨0, hm⟩ : ℤ) - w ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩

/-- **Per-ballot bound.** For any two rankings `σ, τ` and any candidate `c`,
`|score_c(σ) - score_c(τ)| ≤ w₁ - wₘ`. -/
theorem score_sub_le {w : Fin m → ℕ} (hw : Antitone w) (hm : 0 < m)
    (σ τ : Equiv.Perm (Fin m)) (c : Fin m) :
    |(score w σ c : ℤ) - score w τ c| ≤ weightRange w hm := by
  have hbounds : ∀ a : Fin m,
      w ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩ ≤ w a ∧ w a ≤ w ⟨0, hm⟩ := fun a =>
    ⟨hw (Fin.mk_le_mk.2 (by omega) : a ≤ ⟨m - 1, _⟩ ), hw (Fin.mk_le_mk.2 (Nat.zero_le _))⟩
  obtain ⟨h1, h2⟩ := hbounds (σ.symm c)
  obtain ⟨h3, h4⟩ := hbounds (τ.symm c)
  unfold score weightRange
  rw [abs_le]
  constructor <;> omega

lemma weightRange_nonneg {w : Fin m → ℕ} (hw : Antitone w) (hm : 0 < m) :
    0 ≤ weightRange w hm := by
  have : w ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩ ≤ w ⟨0, hm⟩ := hw (Fin.mk_le_mk.2 (Nat.zero_le _))
  unfold weightRange
  omega

/-- **Per-ballot pairwise bound.** One ranking gives any two candidates `c, c'`
scores within `Δ` of each other: `|score_c(σ) - score_{c'}(σ)| ≤ w₁ - wₘ`. So a
ballot that is added, dropped or replaced moves the difference `s_c - s_{c'}` by
at most `Δ`, `Δ` or `2Δ` (Corollary `margin`). -/
theorem score_pair_le {w : Fin m → ℕ} (hw : Antitone w) (hm : 0 < m)
    (σ : Equiv.Perm (Fin m)) (c c' : Fin m) :
    |(score w σ c : ℤ) - score w σ c'| ≤ weightRange w hm := by
  have hbounds : ∀ a : Fin m,
      w ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩ ≤ w a ∧ w a ≤ w ⟨0, hm⟩ := fun a =>
    ⟨hw (Fin.mk_le_mk.2 (by omega) : a ≤ ⟨m - 1, _⟩ ), hw (Fin.mk_le_mk.2 (Nat.zero_le _))⟩
  obtain ⟨h1, h2⟩ := hbounds (σ.symm c)
  obtain ⟨h3, h4⟩ := hbounds (σ.symm c')
  unfold score weightRange
  rw [abs_le]
  constructor <;> omega

/-- **Profile bound.** If `ω` and `ω'` agree on every ballot outside `D`, then every
candidate's total score differs by at most `|D| · Δ`. -/
theorem scoreVec_sub_le {w : Fin m → ℕ} (hw : Antitone w) (hm : 0 < m)
    (ω ω' : Fin n → Equiv.Perm (Fin m)) (D : Finset (Fin n))
    (hD : ∀ l ∉ D, ω l = ω' l) (c : Fin m) :
    |(scoreVec w ω c : ℤ) - scoreVec w ω' c| ≤ D.card * weightRange w hm := by
  unfold scoreVec
  push_cast
  rw [← sum_sub_distrib,
    ← sum_subset (subset_univ D) (fun l _ hl => by rw [hD l hl, sub_self])]
  calc |∑ l ∈ D, ((score w (ω l) c : ℤ) - score w (ω' l) c)|
      ≤ ∑ l ∈ D, |(score w (ω l) c : ℤ) - score w (ω' l) c| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l ∈ D, weightRange w hm := sum_le_sum fun l _ => score_sub_le hw hm _ _ c
    _ = D.card * weightRange w hm := by rw [sum_const, nsmul_eq_mul]

/-- **Single ballot.** Replacing the ranking of one ballot `l₀` changes every
candidate's total score by at most `Δ`. -/
theorem scoreVec_sub_le_single {w : Fin m → ℕ} (hw : Antitone w) (hm : 0 < m)
    (ω ω' : Fin n → Equiv.Perm (Fin m)) (l₀ : Fin n) (hD : ∀ l ≠ l₀, ω l = ω' l)
    (c : Fin m) :
    |(scoreVec w ω c : ℤ) - scoreVec w ω' c| ≤ weightRange w hm := by
  have := scoreVec_sub_le hw hm ω ω' {l₀} (fun l hl => hD l (by simpa using hl)) c
  simpa using this

end PDemos
