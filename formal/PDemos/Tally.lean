import PDemos.Digits

/-!
# Decoding the tallies (`security.tex`, Theorem 1)

A ranking is a permutation `ω : Fin m ≃ Fin m`, where `ω i` is the candidate at
rank `i` (ranks and candidates are 0-indexed). A profile of `n` cast ballots is
`ω : Fin n → Equiv.Perm (Fin m)`.

* **Matrix mode.** Rank `i` aggregates `Tᵢ = ∑ₗ x^{ωₗ(i)}`. We show
  `Tᵢ = ∑ⱼ N i j * xʲ`, where `N i j` counts the ballots that put candidate `j` at
  rank `i`, so `N i j ≤ n`. If `n < x`, then `Tᵢ < x^m` and the base-`x` digits of
  `Tᵢ` are exactly `N i 0, …, N i (m-1)`.
* **Score mode.** `T = ∑ₗ ∑ᵢ wᵢ x^{ωₗ(i)} = ∑ⱼ sⱼ xʲ`, where `sⱼ` is the positional
  score of candidate `j`. If `wᵢ ≤ W` for all `i` and `n * W < x`, then `T < x^m`
  and the base-`x` digits of `T` are exactly the scores.
-/

namespace PDemos

open Finset

variable {n m : ℕ}

/-- Points that ranking `σ` gives to candidate `c`: the weight of `c`'s rank. -/
def score (w : Fin m → ℕ) (σ : Equiv.Perm (Fin m)) (c : Fin m) : ℕ := w (σ.symm c)

/-- Total positional score of candidate `c` in profile `ω`. -/
def scoreVec (w : Fin m → ℕ) (ω : Fin n → Equiv.Perm (Fin m)) (c : Fin m) : ℕ :=
  ∑ l, score w (ω l) c

/-- `N i j`: number of ballots that place candidate `j` at rank `i`. -/
def posMatrix (ω : Fin n → Equiv.Perm (Fin m)) (i j : Fin m) : ℕ := #{l | ω l i = j}

/-- Matrix-mode aggregate of rank `i`: the sum of the encodings cast at rank `i`. -/
def rankTally (x : ℕ) (ω : Fin n → Equiv.Perm (Fin m)) (i : Fin m) : ℕ :=
  ∑ l, x ^ (ω l i : ℕ)

/-- Score-mode aggregate: every ballot contributes `wᵢ · x^{ωₗ(i)}` for each rank `i`. -/
def scoreTally (x : ℕ) (w : Fin m → ℕ) (ω : Fin n → Equiv.Perm (Fin m)) : ℕ :=
  ∑ l, ∑ i, w i * x ^ (ω l i : ℕ)

/-! ### Matrix mode -/

theorem rankTally_eq (x : ℕ) (ω : Fin n → Equiv.Perm (Fin m)) (i : Fin m) :
    rankTally x ω i = digitSum x (posMatrix ω i) :=
  sum_pow_eq_digitSum x (fun l => ω l i)

theorem posMatrix_le (ω : Fin n → Equiv.Perm (Fin m)) (i j : Fin m) :
    posMatrix ω i j ≤ n :=
  (card_le_univ _).trans (Fintype.card_fin n).le

theorem rankTally_lt {x : ℕ} (hx : n < x) (ω : Fin n → Equiv.Perm (Fin m)) (i : Fin m) :
    rankTally x ω i < x ^ m := by
  rw [rankTally_eq]
  exact digitSum_lt _ fun j => lt_of_le_of_lt (posMatrix_le ω i j) hx

/-- **Matrix-mode decoding.** If `n < x`, the `j`-th base-`x` digit of `Tᵢ` is `N i j`. -/
theorem rankTally_digit {x : ℕ} (hx : n < x) (ω : Fin n → Equiv.Perm (Fin m))
    (i j : Fin m) :
    rankTally x ω i / x ^ (j : ℕ) % x = posMatrix ω i j := by
  rw [rankTally_eq]
  exact digitSum_digit _ (fun j => lt_of_le_of_lt (posMatrix_le ω i j) hx) j

/-! ### Score mode -/

theorem scoreTally_eq (x : ℕ) (w : Fin m → ℕ) (ω : Fin n → Equiv.Perm (Fin m)) :
    scoreTally x w ω = digitSum x (scoreVec w ω) := by
  unfold scoreTally digitSum scoreVec score
  simp_rw [sum_mul]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  -- reindex ranks by candidates: `i = (ω l).symm j`
  rw [← Equiv.sum_comp (ω l) (fun j => w ((ω l).symm j) * x ^ (j : ℕ))]
  simp

theorem scoreVec_le {W : ℕ} (w : Fin m → ℕ) (hW : ∀ i, w i ≤ W)
    (ω : Fin n → Equiv.Perm (Fin m)) (c : Fin m) :
    scoreVec w ω c ≤ n * W := by
  calc scoreVec w ω c ≤ ∑ _l : Fin n, W := sum_le_sum fun l _ => hW _
    _ = n * W := by simp

theorem scoreTally_lt {x W : ℕ} (w : Fin m → ℕ) (hW : ∀ i, w i ≤ W) (hx : n * W < x)
    (ω : Fin n → Equiv.Perm (Fin m)) :
    scoreTally x w ω < x ^ m := by
  rw [scoreTally_eq]
  exact digitSum_lt _ fun c => lt_of_le_of_lt (scoreVec_le w hW ω c) hx

/-- **Score-mode decoding.** If every weight is at most `W` and `n * W < x`, the
`c`-th base-`x` digit of `T` is the score of candidate `c`. -/
theorem scoreTally_digit {x W : ℕ} (w : Fin m → ℕ) (hW : ∀ i, w i ≤ W) (hx : n * W < x)
    (ω : Fin n → Equiv.Perm (Fin m)) (c : Fin m) :
    scoreTally x w ω / x ^ (c : ℕ) % x = scoreVec w ω c := by
  rw [scoreTally_eq]
  exact digitSum_digit _ (fun c => lt_of_le_of_lt (scoreVec_le w hW ω c) hx) c

end PDemos
