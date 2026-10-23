import PDemos.Protocol

/-!
# Theorem 1 (Correctness), end to end (`security.tex`, `newProtocol.tex`)

We run the honest protocol: Setup by an honest `EA`, Cast by honest voters, Tally
by the honest `EA`. The result is the `info` that `Verify` and `Result` read.
`correctness` shows that every universal check (U2)–(U6) passes, that every voter
who cast a ballot passes (I1)–(I2), and that `Result(info) = f(ω)` in both modes.

The statement holds for **every** choice of the honest parties' randomness (key,
codes, permutations, commitment randomness, Σ-protocol randomness) and every
coin, provided only that the vote codes within each part are distinct, as the
`EA` samples them. So it holds with probability `1`.

The optional opening of unused ballots is not modelled (it is outside the protocol
analysed for privacy as well).
-/

namespace PDemos

open Finset

variable {G : Type*} [CommGroup G] {q n m κ : ℕ}

/-- All randomness of an honest Setup. -/
structure SetupRand (G : Type*) (q n m κ : ℕ) where
  key : G
  /-- `C^{(a)}_{l,j}`: code of candidate `j` on part `a` of ballot `l`. -/
  code : Fin n → Bool → Fin m → ZMod q
  /-- `π^{(a)}_l`: candidate `j` sits at position `π j`. -/
  perm : Fin n → Bool → Equiv.Perm (Fin m)
  /-- `t^{(a)}_{l,p}`, by position. -/
  t : Fin n → Bool → Fin m → ZMod q
  /-- `r^{(a)}_{l,p}`, by position. -/
  r : Fin n → Bool → Fin m → ZMod q
  /-- Randomness of the true branch: ballot, part, position, instance. -/
  ρ : Fin n → Bool → Fin m → Fin κ → ZMod q
  /-- Simulated challenges and responses of the other branches. -/
  eSim : Fin n → Bool → Fin m → Fin κ → Fin m → ZMod q
  zSim : Fin n → Bool → Fin m → Fin κ → Fin m → ZMod q

variable (P : Params G m) (R : SetupRand G q n m κ)

/-! ### Setup -/

/-- The candidate at position `p` of part `a` of ballot `l`. -/
def SetupRand.cand (l : Fin n) (a : Bool) (p : Fin m) : Fin m := (R.perm l a).symm p

/-- Part `a` of ballot `l` as posted by the honest `EA`. -/
def setupPart (l : Fin n) (a : Bool) : PartPub G q m κ where
  U p := Com P.g R.key (R.code l a (R.cand l a p)) (R.t l a p)
  E p := Com P.g R.key (encX q P.x (R.cand l a p)) (R.r l a p)
  φ p k := cdsFirst P.g R.key (encX q P.x) (Com P.g R.key (encX q P.x (R.cand l a p)) (R.r l a p))
    (R.cand l a p) (R.ρ l a p k) (R.eSim l a p k) (R.zSim l a p k)
  R := ∑ p, R.r l a p

/-- Honest Setup: `Pub`. -/
def setup : Pub G q n m κ := ⟨R.key, setupPart P R⟩

/-- The paper ballot of `V_l`. -/
def paperBallot (l : Fin n) : PaperBallot q n m := ⟨l, R.code l⟩

/-! ### Cast -/

variable (ω : Fin n → Option (Equiv.Perm (Fin m))) (a : Fin n → Bool)

/-- `ψ_l`: the codes of part `a_l` in the voter's order of preference, or nothing
if `V_l` abstains. -/
def castPsi (l : Fin n) : Option (Psi q m) :=
  (ω l).map fun σ => ⟨a l, fun i => R.code l (a l) (σ i)⟩

/-- The receipt `α_l` of a voter who cast `σ`. -/
def receipt (l : Fin n) (σ : Equiv.Perm (Fin m)) : Receipt q n m :=
  ⟨l, a l, R.code l (!a l), ⟨a l, fun i => R.code l (a l) (σ i)⟩⟩

/-! ### Tally -/

/-- The coin recorded under tag `l` (`0` for an unused ballot). -/
def hCoin (l : Fin n) : Bool := match ω l with
  | some _ => a l
  | none => false

/-- The ranking cast on ballot `l` (the identity for an unused ballot). -/
def hRank (l : Fin n) : Equiv.Perm (Fin m) := (ω l).getD 1

/-- The cast ballots. -/
def hCast : Finset (Fin n) := univ.filter fun l => (ω l).isSome

/-- The position opened at rank `i` of ballot `l`: `π^{(a_l)}_l(ω_l(i))`. -/
def hPos (l : Fin n) (i : Fin m) : Fin m := R.perm l (hCoin ω a l) (hRank ω l i)

/-- Honest Tally: `τ`. -/
def tally : Tau q n m κ where
  psi := castPsi R ω a
  audit l p :=
    ⟨R.code l (!hCoin ω a l) (R.cand l (!hCoin ω a l) p), R.t l (!hCoin ω a l) p,
      encX q P.x (R.cand l (!hCoin ω a l) p), R.r l (!hCoin ω a l) p⟩
  castPos := hPos R ω a
  castRand l i := R.t l (hCoin ω a l) (hPos R ω a l i)
  resp l p k :=
    cdsResp (R.cand l (hCoin ω a l) p) (R.r l (hCoin ω a l) p) (R.ρ l (hCoin ω a l) p k)
      (R.eSim l (hCoin ω a l) p k) (R.zSim l (hCoin ω a l) p k)
      (challenge κ P.β (hCoin ω a) k)
  aggMat i :=
    (∑ l ∈ hCast ω, encX q P.x (hRank ω l i), ∑ l ∈ hCast ω, R.r l (hCoin ω a l) (hPos R ω a l i))
  aggSc :=
    (∑ l ∈ hCast ω, ∑ i, (P.w i : ZMod q) * encX q P.x (hRank ω l i),
      ∑ l ∈ hCast ω, ∑ i, (P.w i : ZMod q) * R.r l (hCoin ω a l) (hPos R ω a l i))

/-- The final `BB` of an honest run. -/
def honestInfo : Info G q n m κ := ⟨setup P R, tally P R ω a⟩

/-! ### Reading the honest `BB` -/

section Read

variable {P R ω a}

lemma honest_pub : (honestInfo P R ω a).pub = setup P R := rfl

lemma honest_tau : (honestInfo P R ω a).tau = tally P R ω a := rfl

lemma honest_key : (honestInfo P R ω a).pub.key = R.key := rfl

lemma honest_coin (l : Fin n) : (honestInfo P R ω a).coin l = hCoin ω a l := by
  simp only [Info.coin, honest_tau, tally, castPsi, hCoin]
  cases ω l <;> rfl

lemma honest_coinString : (honestInfo P R ω a).coinString = hCoin ω a :=
  funext honest_coin

lemma honest_castSet : (honestInfo P R ω a).castSet = hCast ω := by
  simp [Info.castSet, honest_tau, tally, castPsi, hCast]

lemma honest_castPart (l : Fin n) :
    (honestInfo P R ω a).castPart l = setupPart P R l (hCoin ω a l) := by
  rw [Info.castPart, honest_coin]; rfl

lemma honest_auditPart (l : Fin n) :
    (honestInfo P R ω a).auditPart l = setupPart P R l (!hCoin ω a l) := by
  rw [Info.auditPart, honest_coin]; rfl

lemma hCoin_of_mem {l : Fin n} (hl : l ∈ hCast ω) : hCoin ω a l = a l := by
  simp only [hCast, mem_filter, mem_univ, true_and, Option.isSome_iff_exists] at hl
  obtain ⟨σ, hσ⟩ := hl
  simp [hCoin, hσ]

lemma honest_routed (l : Fin n) (i : Fin m) :
    (honestInfo P R ω a).routed l i =
      Com P.g R.key (encX q P.x (hRank ω l i)) (R.r l (hCoin ω a l) (hPos R ω a l i)) := by
  rw [Info.routed, honest_castPart, honest_tau]
  simp [setupPart, tally, hPos, SetupRand.cand]

/-- `f(ω)` is the multiset of the cast rankings. -/
lemma profile_eq : profile ω = (hCast ω).val.map (hRank ω) := by
  have key : ∀ s : Multiset (Fin n), s.filterMap ω =
      (s.filter fun l => (ω l).isSome).map fun l => (ω l).getD 1 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons l s ih =>
      cases h : ω l with
      | none => simp [Multiset.filterMap_cons_none _ _ h, h, ih]
      | some σ => simp [Multiset.filterMap_cons_some _ _ _ h, h, ih]
  rw [profile, key, hCast, Finset.filter_val]
  rfl

end Read

/-! ### Theorem 1 -/

variable [Fact q.Prime]

/-- **Theorem 1 (Correctness).** In an honest run, every universal check passes,
every voter who cast a ballot passes (I1) and (I2), and `Result(info) = f(ω)`, in
both modes. The hypotheses are the parameter conditions of Section 3 that the
theorem uses (`x^m ≤ q` and `n·W < x`; `x > m` is not needed here) and distinct
vote codes within each part. -/
theorem correctness (hq : Nat.card G = q) (hg : P.g ≠ 1) (hm : 0 < m) (hw : Antitone P.w)
    (hxq : P.x ^ m ≤ q) (hnx : n * P.W hm < P.x)
    (hcode : ∀ l b, Function.Injective (R.code l b)) :
    Universal P (honestInfo P R ω a) ∧
      (∀ l σ, ω l = some σ →
        I1 P (honestInfo P R ω a) (receipt R a l σ) ∧ I2 (honestInfo P R ω a) (receipt R a l σ)) ∧
      Result P (honestInfo P R ω a) = elect P.w P.mode (profile ω) := by
  set I := honestInfo P R ω a with hI
  refine ⟨⟨?U2, ?U3, ?U4, ?U5, ?U6⟩, ?indiv, ?result⟩
  case U2 =>
    intro l b
    simp only [hI, honest_pub, setup, setupPart, SetupRand.cand]
    rw [com_prod hq]
    congr 1
    rw [Equiv.sum_comp (R.perm l b).symm (encX q P.x)]
    simp [encX, S]
  case U3 =>
    intro l _
    refine ⟨fun p => ?_, ?_⟩
    · simp [hI, honest_auditPart, honest_tau, honest_key, setupPart, tally, SetupRand.cand]
    · intro p p' h
      simp only [hI, honest_tau, tally, SetupRand.cand] at h
      exact (R.perm l _).symm.injective (hcode l _ h)
  case U4 =>
    intro l ψ hψ
    simp only [hI, honest_tau, tally, castPsi, Option.map_eq_some_iff] at hψ
    obtain ⟨σ, hσ, rfl⟩ := hψ
    refine ⟨fun i => ?_, ?_⟩
    · simp [hI, honest_castPart, honest_tau, honest_key, setupPart, tally, hPos, hRank, hσ, hCoin,
        SetupRand.cand]
    · intro i i' h
      simpa [hI, honest_tau, tally, hPos] using h
  case U5 =>
    intro l _ p k
    simp only [hI, honest_castPart, honest_coinString, honest_pub, honest_tau]
    exact cds_complete hq _ _ _ _ _ _ _ _ _
  case U6 =>
    simp only [U6]
    cases hmode : P.mode with
    | mat =>
      intro i
      simp only [hI, honest_castSet, honest_routed, honest_pub, honest_tau, tally, setup]
      exact com_prod hq _ _ _ _ _
    | sc =>
      simp only [hI, honest_castSet, honest_routed, com_pow hq, honest_pub, honest_tau, tally,
        setup]
      rw [prod_congr rfl fun l _ => com_prod hq _ _ _ _ _, com_prod hq]
  case indiv =>
    intro l σ hσ
    have hl : hCoin ω a l = a l := by simp [hCoin, hσ]
    refine ⟨fun j => ⟨R.perm l (!a l) j, ?_⟩, ?_⟩
    · simp [hI, honest_tau, tally, receipt, hl, SetupRand.cand]
    · simp [I2, hI, honest_tau, tally, castPsi, receipt, hσ]
  case result =>
    -- reindex the cast ballots and apply Step 2 (`matrix_result_eq`, `score_result_eq`)
    set s := hCast ω
    set σ' : Fin s.card → Equiv.Perm (Fin m) := fun k => hRank ω (enum s k)
    have hcard : s.card ≤ n := card_le_univ s |>.trans (Fintype.card_fin n).le
    have hC : ∀ k i, CommitsTo P.g R.key (I.routed (enum s k) i)
        ((P.x ^ (σ' k i : ℕ) : ℕ) : ZMod q) := fun k i => ⟨_, honest_routed _ _⟩
    rw [profile_eq]
    simp only [Result, elect]
    cases hmode : P.mode with
    | mat =>
      have hn : s.card < P.x := by
        have : P.W hm = 1 := by simp [Params.W, hmode]
        rw [this, mul_one] at hnx
        omega
      dsimp only
      congr 1
      funext i j
      have hT : ∀ i, ∏ k, I.routed (enum s k) i =
          Com P.g R.key (I.tau.aggMat i).1 (I.tau.aggMat i).2 := by
        intro i
        rw [← prod_enum s (fun t => I.routed t i)]
        simp only [hI, honest_routed, honest_tau, tally]
        exact com_prod hq _ _ _ _ _
      have := (matrix_result_eq hq hg R.key hn hxq σ' (fun k i => I.routed (enum s k) i) hC
        (fun i => (I.tau.aggMat i).1) (fun i => (I.tau.aggMat i).2) hT i).2 j
      rw [decode, this, posMatrix_enum]
    | sc =>
      have hW : ∀ i, P.w i ≤ w₁ P.w hm := fun i => hw (Fin.mk_le_mk.2 (Nat.zero_le _) :
        (⟨0, hm⟩ : Fin m) ≤ i)
      have hn : s.card * w₁ P.w hm < P.x := by
        have : P.W hm = w₁ P.w hm := by simp [Params.W, hmode]
        rw [this] at hnx
        exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hcard) hnx
      dsimp only
      congr 1
      funext c
      have hT : ∏ k, ∏ i, I.routed (enum s k) i ^ P.w i =
          Com P.g R.key I.tau.aggSc.1 I.tau.aggSc.2 := by
        rw [← prod_enum s (fun t => ∏ i, I.routed t i ^ P.w i)]
        simp only [hI, honest_routed, com_pow hq, honest_tau, tally]
        rw [prod_congr rfl fun l _ => com_prod hq _ _ _ _ _, com_prod hq]
      have := (score_result_eq hq hg R.key P.w hW hn hxq σ' (fun k i => I.routed (enum s k) i)
        hC _ _ hT).2 c
      rw [decode, this, scoreVec_enum]

end PDemos
