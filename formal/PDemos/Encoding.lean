import PDemos.Digits

/-!
# The Encoding Lemma (`zkp.tex`, Lemma 1)

Let `x > m` and `v₁, …, vₘ ∈ 𝒳 = {x⁰, …, x^{m-1}}`. Then `∑ₚ vₚ = S := ∑ⱼ xʲ`
iff `(v₁, …, vₘ)` is a permutation of `(x⁰, …, x^{m-1})`, i.e. iff each power of
`x` occurs exactly once. We also check the "From integers to `ℤ_q`" remark:
if `x ^ m ≤ q`, then congruence modulo `q` already forces equality.
-/

namespace PDemos

open Finset

/-- The opened sum `S = x⁰ + x¹ + ⋯ + x^{m-1}`. -/
def S (x m : ℕ) : ℕ := ∑ j : Fin m, x ^ (j : ℕ)

lemma S_eq_digitSum (x m : ℕ) : S x m = digitSum x (fun _ : Fin m => 1) := by
  simp [S, digitSum]

/-- Core of the lemma, phrased via the index map `J`: `∑ₚ x^{J p} = S` iff `J` is a
bijection. -/
theorem sum_pow_eq_S_iff {x m : ℕ} (hx : m < x) (J : Fin m → Fin m) :
    ∑ p, x ^ (J p : ℕ) = S x m ↔ Function.Bijective J := by
  constructor
  · intro h
    rw [sum_pow_eq_digitSum, S_eq_digitSum] at h
    -- every coefficient is at most `m < x`, so base-`x` uniqueness applies
    have hc : ∀ j, #{p | J p = j} < x := fun j =>
      lt_of_le_of_lt ((card_le_univ _).trans (Fintype.card_fin m).le) hx
    have h1 : ∀ j, #{p | J p = j} = 1 := fun j =>
      congrFun (digitSum_injective hc (fun _ => lt_of_le_of_lt (Fin.pos j) hx) h) j
    have hsurj : Function.Surjective J := fun j => by
      obtain ⟨p, hp⟩ := card_pos.1 (by rw [h1 j]; exact Nat.one_pos)
      exact ⟨p, (mem_filter.1 hp).2⟩
    exact ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  · intro hJ
    exact Equiv.sum_comp (Equiv.ofBijective J hJ) (fun j : Fin m => x ^ (j : ℕ))

/-- **Encoding Lemma** (`zkp.tex`, Lemma 1). For `x > m` and `v : Fin m → 𝒳`,
the values sum to `S` iff they are a permutation of `x⁰, …, x^{m-1}`. -/
theorem encoding_lemma {x m : ℕ} (hx : m < x) (v : Fin m → ℕ)
    (hv : ∀ p, ∃ j : Fin m, v p = x ^ (j : ℕ)) :
    ∑ p, v p = S x m ↔ ∃ σ : Equiv.Perm (Fin m), ∀ p, v p = x ^ (σ p : ℕ) := by
  choose J hJ using hv
  have hvJ : v = fun p => x ^ (J p : ℕ) := funext hJ
  subst hvJ
  rw [sum_pow_eq_S_iff hx]
  constructor
  · intro hb
    exact ⟨Equiv.ofBijective J hb, fun p => rfl⟩
  · rintro ⟨σ, hσ⟩
    have hJσ : J = σ := funext fun p =>
      Fin.ext (Nat.pow_right_injective (by have := Fin.pos (J p); omega) (hσ p))
    rw [hJσ]
    exact σ.bijective

/-- **Encoding Lemma, counting form.** For `x > m` and `v : Fin m → 𝒳`, the values
sum to `S` iff each power `x ^ j` (`j < m`) occurs exactly once among them. -/
theorem encoding_lemma_count {x m : ℕ} (hx : m < x) (v : Fin m → ℕ)
    (hv : ∀ p, ∃ j : Fin m, v p = x ^ (j : ℕ)) :
    ∑ p, v p = S x m ↔ ∀ j : Fin m, #{p | v p = x ^ (j : ℕ)} = 1 := by
  choose J hJ using hv
  have hvJ : v = fun p => x ^ (J p : ℕ) := funext hJ
  subst hvJ
  -- for `j : Fin m` we have `m ≥ 1`, hence `x ≥ 2` and `x ^ ·` is injective
  have hfib : ∀ j : Fin m, #{p | x ^ (J p : ℕ) = x ^ (j : ℕ)} = #{p | J p = j} := by
    intro j
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      exact Fin.ext (Nat.pow_right_injective (by have := Fin.pos j; omega) h)
    · rintro rfl
      rfl
  simp_rw [hfib]
  constructor
  · intro h j
    rw [sum_pow_eq_digitSum, S_eq_digitSum] at h
    exact congrFun (digitSum_injective
      (fun j => lt_of_le_of_lt ((card_le_univ _).trans (Fintype.card_fin m).le) hx)
      (fun j => lt_of_le_of_lt (Fin.pos j) hx) h) j
  · intro h
    rw [sum_pow_eq_digitSum, S_eq_digitSum]
    exact congrArg (digitSum x) (funext h)

/-- Any sum of `m` elements of `𝒳` is below `x ^ m` (used with `x ^ m ≤ q`). -/
theorem sum_lt_pow {x m : ℕ} (hx : m < x) (v : Fin m → ℕ)
    (hv : ∀ p, ∃ j : Fin m, v p = x ^ (j : ℕ)) :
    ∑ p, v p < x ^ m := by
  choose J hJ using hv
  simp_rw [hJ, sum_pow_eq_digitSum]
  exact digitSum_lt _
    (fun j => lt_of_le_of_lt ((card_le_univ _).trans (Fintype.card_fin m).le) hx)

/-- **From integers to `ℤ_q`** (`zkp.tex`, after Lemma 1). If `x ^ m ≤ q`, then
`∑ₚ vₚ ≡ S (mod q)` implies `∑ₚ vₚ = S` over the integers, so the Encoding Lemma
applies to the sum check on commitments. -/
theorem sum_eq_S_of_modEq {x m q : ℕ} (hx : m < x) (hq : x ^ m ≤ q) (v : Fin m → ℕ)
    (hv : ∀ p, ∃ j : Fin m, v p = x ^ (j : ℕ)) (h : ∑ p, v p ≡ S x m [MOD q]) :
    ∑ p, v p = S x m := by
  have hS : S x m < x ^ m := by
    rw [S_eq_digitSum]
    exact digitSum_lt _ (fun j => lt_of_le_of_lt (Fin.pos j) hx)
  exact Nat.ModEq.eq_of_lt_of_lt h (lt_of_lt_of_le (sum_lt_pow hx v hv) hq)
    (lt_of_lt_of_le hS hq)

end PDemos
