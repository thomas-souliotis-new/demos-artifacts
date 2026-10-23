import Mathlib

/-!
# Lifted ElGamal commitments (`background.tex`, Section 2)

Let `G` be a commutative group of prime order `q` with a generator `g ≠ 1`. The
commitment key is an arbitrary `h : G`. It may be chosen by a malicious
Election Authority, and nothing is assumed about `log_g h`. A commitment to
`v ∈ ℤ_q` with randomness `r ∈ ℤ_q` is

  `Com(v; r) = (g^r, g^v h^r) ∈ G × G`,

and `⊙` is the componentwise product in `G × G`.

Exponents live in `ZMod q`. We write `x ^ₘ a` for `x ^ a.val`. Because every
element of `G` satisfies `x ^ q = 1`, this is a `ℤ_q`-action (`zpow_add`,
`zpow_mul`, …), which is all the algebra the proofs below use.

We prove the three properties the paper uses:

* `com_mul`, `com_pow`, `com_prod`: the homomorphism;
* `com_injective` (**perfect binding**): `Com(v; r) = Com(v'; r')` forces
  `v = v'` and `r = r'`, for every `h`;
* `exists_com`: every pair in `G × G` is a commitment, so every posted
  commitment has exactly one committed value (`committed_value_unique`).
-/

namespace PDemos

open Finset

variable {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime]

/-- Exponentiation by an element of `ℤ_q`. -/
def zpowq (x : G) (a : ZMod q) : G := x ^ a.val

@[inherit_doc] infixr:75 " ^ₘ " => zpowq

section Exp

variable (hq : Nat.card G = q)
include hq

omit [Fact q.Prime] in
lemma pow_q (x : G) : x ^ q = 1 := hq ▸ pow_card_eq_one'

omit [Fact q.Prime] in
lemma pow_mod_q (x : G) (k : ℕ) : x ^ (k % q) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k q, pow_add, pow_mul, pow_q hq, one_pow, mul_one]

lemma zpowq_natCast (x : G) (k : ℕ) : x ^ₘ (k : ZMod q) = x ^ k := by
  rw [zpowq, ZMod.val_natCast, pow_mod_q hq]

omit hq in
lemma zpowq_zero (x : G) : x ^ₘ (0 : ZMod q) = 1 := by simp [zpowq]

lemma zpowq_one (x : G) : x ^ₘ (1 : ZMod q) = x := by
  simpa using zpowq_natCast hq x 1

lemma zpowq_add (x : G) (a b : ZMod q) : x ^ₘ (a + b) = x ^ₘ a * x ^ₘ b := by
  rw [zpowq, ZMod.val_add, pow_mod_q hq, pow_add, zpowq, zpowq]

lemma zpowq_neg (x : G) (a : ZMod q) : x ^ₘ (-a) = (x ^ₘ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← zpowq_add hq, neg_add_cancel, zpowq_zero])

lemma zpowq_sub (x : G) (a b : ZMod q) : x ^ₘ (a - b) = x ^ₘ a * (x ^ₘ b)⁻¹ := by
  rw [sub_eq_add_neg, zpowq_add hq, zpowq_neg hq]

lemma zpowq_mul (x : G) (a b : ZMod q) : x ^ₘ (a * b) = (x ^ₘ a) ^ₘ b := by
  rw [zpowq, ZMod.val_mul, pow_mod_q hq, pow_mul, zpowq, zpowq]

omit [Fact q.Prime] hq in
lemma mul_zpowq (x y : G) (a : ZMod q) : (x * y) ^ₘ a = x ^ₘ a * y ^ₘ a := by
  simp [zpowq, mul_pow]

omit [Fact q.Prime] hq in
lemma inv_zpowq (x : G) (a : ZMod q) : x⁻¹ ^ₘ a = (x ^ₘ a)⁻¹ := by
  simp [zpowq, inv_pow]

lemma zpowq_sum {ι : Type*} (s : Finset ι) (x : G) (a : ι → ZMod q) :
    x ^ₘ (∑ i ∈ s, a i) = ∏ i ∈ s, x ^ₘ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zpowq_zero]
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, zpowq_add hq, ih]

/-- A non-identity element of a group of prime order `q` has order `q`. -/
lemma orderOf_eq_q {g : G} (hg : g ≠ 1) : orderOf g = q :=
  orderOf_eq_prime (pow_q hq g) hg

/-- Exponentiation of a generator is injective on `ℤ_q` (this is where `g ≠ 1`
and the primality of `q` are used). -/
lemma zpowq_injective {g : G} (hg : g ≠ 1) : Function.Injective (g ^ₘ · : ZMod q → G) := by
  intro a b h
  have h' := pow_inj_mod.1 h
  rw [orderOf_eq_q hq hg, Nat.mod_eq_of_lt (ZMod.val_lt a),
    Nat.mod_eq_of_lt (ZMod.val_lt b)] at h'
  exact ZMod.val_injective q h'

/-- A non-identity `g` generates `G`: every element is `g ^ₘ a` for some `a`. -/
lemma exists_zpowq_eq {g : G} (hg : g ≠ 1) (y : G) : ∃ a : ZMod q, g ^ₘ a = y := by
  have hfin : Finite G := Nat.finite_of_card_ne_zero (by rw [hq]; exact (Fact.out : q.Prime).ne_zero)
  have hy : y ∈ Subgroup.zpowers g := by
    rw [zpowers_eq_top_of_prime_card hq hg]; trivial
  obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 hy
  exact ⟨k, by rw [zpowq_natCast hq]; exact hk⟩

end Exp

/-! ### The commitment scheme -/

/-- Lifted ElGamal commitment `Com_h(v; r) = (g^r, g^v h^r)`. -/
def Com (g h : G) (v r : ZMod q) : G × G := (g ^ₘ r, g ^ₘ v * h ^ₘ r)

/-- `c` commits to `v`: some randomness `r` opens `c` to `v`. -/
def CommitsTo (g h : G) (c : G × G) (v : ZMod q) : Prop := ∃ r, c = Com g h v r

variable (hq : Nat.card G = q) (g h : G)
include hq

/-- **Homomorphism.** `Com(v₁; r₁) ⊙ Com(v₂; r₂) = Com(v₁ + v₂; r₁ + r₂)`. -/
theorem com_mul (v₁ r₁ v₂ r₂ : ZMod q) :
    Com g h v₁ r₁ * Com g h v₂ r₂ = Com g h (v₁ + v₂) (r₁ + r₂) := by
  simp only [Com, Prod.mk_mul_mk, zpowq_add hq]
  congr 1
  ac_rfl

/-- **Homomorphism, scalar form.** `Com(v; r)^w = Com(w v; w r)` for a public `w : ℕ`. -/
theorem com_pow (v r : ZMod q) (w : ℕ) :
    Com g h v r ^ w = Com g h ((w : ZMod q) * v) ((w : ZMod q) * r) := by
  simp only [Com, Prod.pow_mk, mul_comm (w : ZMod q), zpowq_mul hq, zpowq_natCast hq, mul_pow]

theorem com_inv (v r : ZMod q) : (Com g h v r)⁻¹ = Com g h (-v) (-r) := by
  simp [Com, zpowq_neg hq, mul_comm]

theorem com_div (v₁ r₁ v₂ r₂ : ZMod q) :
    Com g h v₁ r₁ / Com g h v₂ r₂ = Com g h (v₁ - v₂) (r₁ - r₂) := by
  rw [div_eq_mul_inv, com_inv hq, com_mul hq, ← sub_eq_add_neg, ← sub_eq_add_neg]

/-- **Homomorphism, product form.** `⨀ᵢ Com(vᵢ; rᵢ) = Com(∑ vᵢ; ∑ rᵢ)`. -/
theorem com_prod {ι : Type*} (s : Finset ι) (v r : ι → ZMod q) :
    ∏ i ∈ s, Com g h (v i) (r i) = Com g h (∑ i ∈ s, v i) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Com, zpowq_zero]; rfl
  | insert i s hi ih => rw [prod_insert hi, ih, com_mul hq, sum_insert hi, sum_insert hi]

/-- Commitments to `v` form a group under `⊙` up to the value: the product of a
commitment to `v₁` and one to `v₂` commits to `v₁ + v₂`. -/
theorem CommitsTo.mul {c₁ c₂ : G × G} {v₁ v₂ : ZMod q} (h₁ : CommitsTo g h c₁ v₁)
    (h₂ : CommitsTo g h c₂ v₂) : CommitsTo g h (c₁ * c₂) (v₁ + v₂) := by
  obtain ⟨r₁, rfl⟩ := h₁
  obtain ⟨r₂, rfl⟩ := h₂
  exact ⟨r₁ + r₂, com_mul hq g h _ _ _ _⟩

theorem CommitsTo.prod {ι : Type*} (s : Finset ι) {c : ι → G × G} {v : ι → ZMod q}
    (hc : ∀ i ∈ s, CommitsTo g h (c i) (v i)) :
    CommitsTo g h (∏ i ∈ s, c i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [Com, zpowq_zero]; rfl⟩
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    exact (hc i (mem_insert_self i s)).mul hq g h
      (ih fun j hj => hc j (mem_insert_of_mem hj))

theorem CommitsTo.pow {c : G × G} {v : ZMod q} (hc : CommitsTo g h c v) (w : ℕ) :
    CommitsTo g h (c ^ w) ((w : ZMod q) * v) := by
  obtain ⟨r, rfl⟩ := hc
  exact ⟨(w : ZMod q) * r, com_pow hq g h _ _ _⟩

variable {g} (hg : g ≠ 1)
include hg

/-- **Perfect binding.** For every key `h`, `Com(v; r) = Com(v'; r')` implies
`v = v'` and `r = r'`. -/
theorem com_injective {v r v' r' : ZMod q} (h_eq : Com g h v r = Com g h v' r') :
    v = v' ∧ r = r' := by
  simp only [Com, Prod.mk.injEq] at h_eq
  obtain ⟨h1, h2⟩ := h_eq
  have hr : r = r' := zpowq_injective hq hg h1
  subst hr
  exact ⟨zpowq_injective hq hg (mul_right_cancel h2), rfl⟩

/-- **Perfect binding, value form.** A pair commits to at most one value. -/
theorem committed_value_unique {c : G × G} {v v' : ZMod q} (h₁ : CommitsTo g h c v)
    (h₂ : CommitsTo g h c v') : v = v' := by
  obtain ⟨r, rfl⟩ := h₁
  obtain ⟨r', hr'⟩ := h₂
  exact (com_injective hq h hg hr').1

/-- Every pair in `G × G` is a commitment to some value. Together with
`committed_value_unique`, every posted commitment has exactly one committed value. -/
theorem exists_com (c : G × G) : ∃ v r : ZMod q, c = Com g h v r := by
  obtain ⟨r, hr⟩ := exists_zpowq_eq hq hg c.1
  obtain ⟨v, hv⟩ := exists_zpowq_eq hq hg (c.2 * (h ^ₘ r)⁻¹)
  exact ⟨v, r, Prod.ext hr.symm (by simp [Com, hv])⟩

theorem existsUnique_committed (c : G × G) : ∃! v : ZMod q, CommitsTo g h c v := by
  obtain ⟨v, r, hc⟩ := exists_com hq h hg c
  exact ⟨v, ⟨r, hc⟩, fun v' hv' => committed_value_unique hq h hg hv' ⟨r, hc⟩⟩

end PDemos
