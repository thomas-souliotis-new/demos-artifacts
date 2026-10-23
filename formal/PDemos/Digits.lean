import Mathlib

/-!
# Base-`x` digits of `∑ N j * x ^ j`

The arithmetic core shared by the Encoding Lemma (`zkp.tex`, Lemma 1) and the
decoding step of the Correctness theorem (`security.tex`, Theorem 1).

Candidates are 0-indexed here: the paper's `P_j` with encoding `x^{j-1}`
corresponds to `j - 1 : Fin m` with encoding `x ^ (j - 1)`.
-/

namespace PDemos

open Finset

/-- The integer whose base-`x` digits are `N 0, …, N (m-1)` (least significant first). -/
def digitSum (x : ℕ) {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∑ j : Fin m, N j * x ^ (j : ℕ)

lemma digitSum_succ (x : ℕ) {m : ℕ} (N : Fin (m + 1) → ℕ) :
    digitSum x N = N 0 + x * digitSum x (fun j : Fin m => N j.succ) := by
  unfold digitSum
  rw [Fin.sum_univ_succ, mul_sum]
  congr 1
  · simp
  · refine sum_congr rfl fun j _ => ?_
    simp [pow_succ]
    ring

/-- If every digit is below `x`, the number is below `x ^ m`. -/
theorem digitSum_lt {x m : ℕ} (N : Fin m → ℕ) (hN : ∀ j, N j < x) :
    digitSum x N < x ^ m := by
  induction m with
  | zero => simp [digitSum]
  | succ m ih =>
    rw [digitSum_succ, pow_succ']
    have h0 := hN 0
    have h1 := ih (fun j => N j.succ) (fun j => hN _)
    nlinarith

/-- **Decoding.** If every digit is below `x`, the `k`-th base-`x` digit of
`∑ N j * x ^ j` is exactly `N k`. -/
theorem digitSum_digit {x m : ℕ} (N : Fin m → ℕ) (hN : ∀ j, N j < x) (k : Fin m) :
    digitSum x N / x ^ (k : ℕ) % x = N k := by
  induction m with
  | zero => exact k.elim0
  | succ m ih =>
    have hx : 0 < x := lt_of_le_of_lt (Nat.zero_le _) (hN 0)
    rw [digitSum_succ]
    cases k using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hN 0)]
    | succ k =>
      rw [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hx, Nat.div_eq_of_lt (hN 0), zero_add]
      exact ih (fun j => N j.succ) (fun j => hN _) k

/-- **Uniqueness of base-`x` representation.** -/
theorem digitSum_injective {x m : ℕ} {N M : Fin m → ℕ} (hN : ∀ j, N j < x)
    (hM : ∀ j, M j < x) (h : digitSum x N = digitSum x M) : N = M := by
  funext k
  rw [← digitSum_digit N hN k, ← digitSum_digit M hM k, h]

/-- Regrouping `∑ₚ x ^ J p` by the value of `J`: the coefficient of `x ^ j` is the
number of `p` with `J p = j`. -/
lemma sum_pow_eq_digitSum {ι : Type*} [Fintype ι] {m : ℕ} (x : ℕ) (J : ι → Fin m) :
    ∑ p, x ^ (J p : ℕ) = digitSum x (fun j => #{p | J p = j}) := by
  unfold digitSum
  rw [← sum_fiberwise univ J (fun p => x ^ (J p : ℕ))]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_congr rfl (g := fun _ => x ^ (j : ℕ)) (fun p hp => by rw [(mem_filter.1 hp).2]),
    sum_const, smul_eq_mul]

end PDemos
