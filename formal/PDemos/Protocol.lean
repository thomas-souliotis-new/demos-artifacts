import PDemos.Completeness
import PDemos.Verifiability

/-!
# The P-DEMOS protocol (`newProtocol.tex`; syntax of `security.tex`)

This file fixes the data on the bulletin board `BB`, the voters' paper ballots and
receipts, the universal checks (U2)–(U6), the individual checks (I1)–(I2),
`Result`, the election function `f` and the distance `δ`. The honest algorithms
are in `PDemos.Correctness` and the game `G_e2e` in `PDemos.Game`.

## Modelling conventions

* The group is any commutative group `G` of prime order `q`, with generator
  `g ≠ 1` (as in `PDemos.ElGamal`). Vote codes are elements of `ℤ_q`.
* **Tags are `BB` slots.** Check (U1) requires exactly `n` ballots with pairwise
  distinct tags, ordered by tag, and at most one cast ballot per tag. We identify
  the tags with their ranks `0, …, n-1`, so the `BB` is indexed by `Fin n` and the
  cast ballot of tag `t` is `psi t : Option Psi`. (U1) then holds by construction.
* A position of a part is `p : Fin m`, a candidate `j : Fin m` (encoded as
  `x ^ j`), a rank `i : Fin m`. The first messages of the `κ` instances of each
  membership proof are posted at Setup.
* An opening of a cast code commitment at rank `i` names the position
  `castPos t i` and the randomness `castRand t i`. The audit part of a cast ballot
  is opened in full, position by position.
-/

namespace PDemos

open Finset

section Data

variable (G : Type*) (q n m κ : ℕ)

/-- One ballot part as posted at Setup, listed by `BB` position. -/
structure PartPub where
  /-- Code commitments `U_p`. -/
  U : Fin m → G × G
  /-- Encoding commitments `E_p`. -/
  E : Fin m → G × G
  /-- First messages: position, instance, branch. -/
  φ : Fin m → Fin κ → Fin m → G × G
  /-- The opened randomness `R = ∑_p r_p` of the sum check (U2). -/
  R : ZMod q

/-- `Pub`: everything posted at Setup. -/
structure Pub where
  /-- The commitment key `ck = h`. -/
  key : G
  /-- Part `a` of the ballot with tag `t`. -/
  part : Fin n → Bool → PartPub G q m κ

/-- A paper ballot: its tag and, for each part, the code printed next to each
candidate. -/
structure PaperBallot where
  tag : Fin n
  code : Bool → Fin m → ZMod q

/-- A cast ballot `ψ` (without its tag, which is its `BB` slot): the coin and the
codes in order of preference. -/
structure Psi where
  coin : Bool
  codes : Fin m → ZMod q

/-- The full opening of one position of an audit part. -/
structure Opening where
  code : ZMod q
  t : ZMod q
  v : ZMod q
  r : ZMod q

/-- `τ`: everything posted after the voting period (the cast ballots and Tally). -/
structure Tau where
  /-- The cast ballot under each tag, if any. -/
  psi : Fin n → Option (Psi q m)
  /-- Openings of the audit part of every cast ballot, by position. -/
  audit : Fin n → Fin m → Opening q
  /-- The position opened at each rank of the cast part. -/
  castPos : Fin n → Fin m → Fin m
  /-- The randomness of that code commitment. -/
  castRand : Fin n → Fin m → ZMod q
  /-- Responses: tag, position, instance, branch. -/
  resp : Fin n → Fin m → Fin κ → Fin m → ZMod q × ZMod q
  /-- Matrix mode: the opening `(T_i, R̂_i)` of each rank aggregate. -/
  aggMat : Fin m → ZMod q × ZMod q
  /-- Score mode: the opening `(T, R̂)` of the weighted aggregate. -/
  aggSc : ZMod q × ZMod q

/-- `info = (Pub, ⟨ψ⟩, τ)`: the final contents of `BB`. -/
structure Info where
  pub : Pub G q n m κ
  tau : Tau q n m κ

/-- A voter's audit information `α = (Tag, a, s^{(1-a)}, ψ)`. -/
structure Receipt where
  tag : Fin n
  coin : Bool
  /-- The codes printed on the audit part, by candidate. -/
  audit : Fin m → ZMod q
  psi : Psi q m

end Data

/-- The result mode. -/
inductive Mode
  | mat
  | sc
  deriving DecidableEq

/-- A result: the positional matrix `N` or the score vector `s⃗`. -/
inductive Outcome (m : ℕ)
  | mat (N : Fin m → Fin m → ℕ)
  | sc (s : Fin m → ℕ)

/-- The public parameters other than the sizes. -/
structure Params (G : Type*) (m : ℕ) where
  g : G
  /-- The base `x`. -/
  x : ℕ
  /-- Bits per challenge block. -/
  β : ℕ
  /-- Weights `w₁ ≥ ⋯ ≥ wₘ`, 0-indexed. -/
  w : Fin m → ℕ
  mode : Mode

variable {G : Type*} [CommGroup G] {q n m κ : ℕ}

/-- `𝒳 = {x⁰, …, x^{m-1}}` as a family of elements of `ℤ_q`. -/
def encX (q x : ℕ) {m : ℕ} (j : Fin m) : ZMod q := ((x ^ (j : ℕ) : ℕ) : ZMod q)

namespace Params

variable (P : Params G m)

/-- `W = 1` in matrix mode and `W = w₁` in score mode. -/
def W (hm : 0 < m) : ℕ := match P.mode with
  | .mat => 1
  | .sc => w₁ P.w hm

end Params

/-! ### Election function, scores and distance -/

section Election

variable {m : ℕ}

/-- The election function on the multiset of cast rankings (abstentions absent). -/
def elect (w : Fin m → ℕ) : Mode → Multiset (Equiv.Perm (Fin m)) → Outcome m
  | .mat, M => .mat fun i j => M.countP fun σ => σ i = j
  | .sc, M => .sc (msScore w M)

/-- `f(ω₁, …, ωₙ)`, with `⊥` (abstention) as `none`. -/
def profile {n : ℕ} (ω : Fin n → Option (Equiv.Perm (Fin m))) : Multiset (Equiv.Perm (Fin m)) :=
  (univ : Finset (Fin n)).val.filterMap ω

/-- `sc_w`: the score vector of a result. -/
def scw (w : Fin m → ℕ) : Outcome m → Fin m → ℕ
  | .mat N => fun j => ∑ i, w i * N i j
  | .sc s => s

/-- `δ(R, R') = ‖sc_w(R) - sc_w(R')‖_∞`. -/
def dist (w : Fin m → ℕ) (R R' : Outcome m) : ℕ :=
  univ.sup fun c => ((scw w R c : ℤ) - scw w R' c).natAbs

/-- Base-`x` digit extraction (Algorithm 1). -/
def decode (x T : ℕ) (j : Fin m) : ℕ := T / x ^ (j : ℕ) % x

lemma scw_elect (w : Fin m → ℕ) (mode : Mode) (M : Multiset (Equiv.Perm (Fin m))) (c : Fin m) :
    scw w (elect w mode M) c = msScore w M c := by
  cases mode with
  | sc => rfl
  | mat =>
    simp only [elect, scw, msScore]
    induction M using Multiset.induction_on with
    | empty => simp
    | cons σ M ih =>
      have h1 : ∑ i, w i * (if σ i = c then 1 else 0) = score w σ c := by
        rw [sum_eq_single (σ.symm c)]
        · simp [score]
        · intro i _ hi
          simp [← Equiv.eq_symm_apply, hi]
        · simp
      simp only [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons, mul_add,
        sum_add_distrib, ih, h1]
      ring

end Election

/-! ### Reading the bulletin board -/

namespace Info

variable (I : Info G q n m κ)

/-- The coin recorded under tag `t` (`0` if no ballot is cast). -/
def coin (t : Fin n) : Bool := match I.tau.psi t with
  | some ψ => ψ.coin
  | none => false

/-- The coin string `c⃗`, ordered by tag. -/
def coinString : Fin n → Bool := I.coin

/-- The tags of the cast ballots. -/
def castSet : Finset (Fin n) := univ.filter fun t => (I.tau.psi t).isSome

/-- The cast part of tag `t`. -/
def castPart (t : Fin n) : PartPub G q m κ := I.pub.part t (I.coin t)

/-- The audit part of tag `t`. -/
def auditPart (t : Fin n) : PartPub G q m κ := I.pub.part t (!I.coin t)

/-- The encoding commitment routed to rank `i` of the cast part of tag `t`. -/
def routed (t : Fin n) (i : Fin m) : G × G := (I.castPart t).E (I.tau.castPos t i)

end Info

/-! ### Verification -/

section Verify

variable (P : Params G m) (I : Info G q n m κ)

/-- (U2): every part of every ballot passes the sum check. -/
def U2 : Prop :=
  ∀ t a, ∏ p, (I.pub.part t a).E p = Com P.g I.pub.key ((S P.x m : ℕ) : ZMod q) (I.pub.part t a).R

/-- (U3): every opening of an audit part is valid, and its codes are distinct. -/
def U3 : Prop :=
  ∀ t ∈ I.castSet,
    (∀ p, (I.auditPart t).U p = Com P.g I.pub.key (I.tau.audit t p).code (I.tau.audit t p).t ∧
      (I.auditPart t).E p = Com P.g I.pub.key (I.tau.audit t p).v (I.tau.audit t p).r) ∧
    Function.Injective fun p => (I.tau.audit t p).code

/-- (U4): in every cast part, the opened code commitments are valid, open to the
codes of `ψ` in the posted order, and occupy distinct positions. -/
def U4 : Prop :=
  ∀ t ψ, I.tau.psi t = some ψ →
    (∀ i, (I.castPart t).U (I.tau.castPos t i) =
      Com P.g I.pub.key (ψ.codes i) (I.tau.castRand t i)) ∧
    Function.Injective (I.tau.castPos t)

/-- (U5): every membership proof of every cast part accepts, in all `κ` instances,
under the challenge recomputed from the posted coins. -/
def U5 : Prop :=
  ∀ t ∈ I.castSet, ∀ p (k : Fin κ),
    CDSAccept P.g I.pub.key (encX q P.x) ((I.castPart t).E p) ((I.castPart t).φ p k)
      (challenge κ P.β I.coinString k) (I.tau.resp t p k)

/-- (U6): the aggregates recomputed from `BB` match the posted openings. -/
def U6 : Prop := match P.mode with
  | .mat => ∀ i, ∏ t ∈ I.castSet, I.routed t i = Com P.g I.pub.key (I.tau.aggMat i).1 (I.tau.aggMat i).2
  | .sc => ∏ t ∈ I.castSet, ∏ i, I.routed t i ^ P.w i = Com P.g I.pub.key I.tau.aggSc.1 I.tau.aggSc.2

/-- The universal checks. (U1) holds by construction (tags are `BB` slots). -/
def Universal : Prop := U2 P I ∧ U3 P I ∧ U4 P I ∧ U5 P I ∧ U6 P I

/-- (I1): every code printed on the audit part opens at a position whose
`E`-commitment opens to the encoding of its candidate. -/
def I1 (α : Receipt q n m) : Prop :=
  ∀ j, ∃ p, (I.tau.audit α.tag p).code = α.audit j ∧ (I.tau.audit α.tag p).v = encX q P.x j

/-- (I2): the `ψ` posted under the voter's tag is the one she submitted. -/
def I2 (α : Receipt q n m) : Prop := I.tau.psi α.tag = some α.psi ∧ α.psi.coin = α.coin

/-- `Verify(info, α)`. -/
def Verify (α : Receipt q n m) : Prop := Universal P I ∧ I1 P I α ∧ I2 I α

/-- `Result(info)`: decode the opened aggregates. -/
def Result : Outcome m := match P.mode with
  | .mat => .mat fun i => decode P.x (I.tau.aggMat i).1.val
  | .sc => .sc (decode P.x I.tau.aggSc.1.val)

end Verify

/-! ### Reindexing the cast ballots

Steps 1–2 in `PDemos.Verifiability` and the decoding in `PDemos.Tally` are stated
for `n` ballots indexed by `Fin n`. The cast ballots form a subset `s` of the tags;
`enum s` lists it as `Fin s.card`. -/

section Enum

variable {α : Type*}

/-- The elements of a finset, listed by `Fin s.card`. -/
noncomputable def enum (s : Finset α) (j : Fin s.card) : α := (s.equivFin.symm j : α)

lemma enum_mem (s : Finset α) (j : Fin s.card) : enum s j ∈ s := (s.equivFin.symm j).2

lemma prod_enum {M : Type*} [CommMonoid M] (s : Finset α) (F : α → M) :
    ∏ t ∈ s, F t = ∏ j, F (enum s j) := by
  rw [← prod_coe_sort s F]
  exact (Equiv.prod_comp s.equivFin.symm (fun t : s => F t)).symm

lemma sum_enum {M : Type*} [AddCommMonoid M] (s : Finset α) (F : α → M) :
    ∑ t ∈ s, F t = ∑ j, F (enum s j) := by
  rw [← sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun t : s => F t)).symm

/-- The decoded matrix of a reindexed profile counts the cast rankings. -/
lemma posMatrix_enum {m : ℕ} (s : Finset α) (σ : α → Equiv.Perm (Fin m)) (i j : Fin m) :
    posMatrix (fun k => σ (enum s k)) i j = (s.val.map σ).countP fun τ => τ i = j := by
  rw [posMatrix, card_filter, ← sum_enum s (fun t => if σ t i = j then 1 else 0),
    Multiset.countP_map, ← Finset.filter_val, ← card_def, card_filter]

lemma scoreVec_enum {m : ℕ} (w : Fin m → ℕ) (s : Finset α) (σ : α → Equiv.Perm (Fin m))
    (c : Fin m) : scoreVec w (fun k => σ (enum s k)) c = msScore w (s.val.map σ) c := by
  rw [msScore_map, scoreVec, sum_enum s (fun t => score w (σ t) c)]

end Enum

end PDemos
