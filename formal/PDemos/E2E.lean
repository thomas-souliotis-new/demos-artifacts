import PDemos.Game

/-!
# Theorem 2 (E2E verifiability), end to end (`appendix.tex`, Appendix B)

We bound `Pr[G_e2e = 1]` for every adversary of `PDemos.Game`:

  `Pr[G_e2e = 1] ≤ 2^{-⌈d/w₁⌉} + 2nm · 2^{-θ}`  (`e2e_verifiability`).

The proof follows Appendix B and reduces the game to the step lemmas of
`PDemos.Verifiability`, `PDemos.Sigma` and `PDemos.Coins`.

* `Bad`: some cast part has a commitment outside `𝒳` (the event `Z` of Lemma
  `amplified`, together with (U5)). If the game is won and `Bad` holds, every honest
  coin hits the bit of a string `c⃗*` fixed at Setup (`amplified_coins_unique`), so
  one of `2nm` strategies hits `θ` targets (`win_bad_hits`).
* Otherwise Steps 1–2 (`cast_part_ranking`, `matrix_result_eq`, `score_result_eq`)
  show that `𝓔` succeeds and the result is `f` of the cast rankings. Step 3 bounds
  the deviation by `w₁ · U`, where `U` counts the honest voters that are not the
  first holder of their tag and the first holders whose cast part is inconsistent.
  It is proved for any functional of the counted rankings (`win_good_val`), so
  that `PDemos.Margin` can reuse it for a pairwise score difference.
  Step 4 (`faithful_of_consistent` and the individual checks) shows that each of
  these `U` voters' coins must hit a target fixed before it is drawn
  (`win_good_hits`, `win_good_count`).
* `e2e_error_bound` adds the two bounds.
-/

namespace PDemos

open Finset
open scoped ENNReal

variable {G : Type*} [CommGroup G] {q n m κ : ℕ}

/-! ### Small facts -/

lemma encX_injective {x m : ℕ} (hx : m < x) (hxq : x ^ m ≤ q) :
    Function.Injective (encX q x : Fin m → ZMod q) := by
  intro j j' h
  have hlt : ∀ j : Fin m, x ^ (j : ℕ) < q := fun j =>
    (Nat.pow_lt_pow_right (by have := j.pos; omega) j.isLt).trans_le hxq
  simp only [encX] at h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt _), Nat.mod_eq_of_lt (hlt _)] at h
  exact Fin.ext (Nat.pow_right_injective (by have := j.pos; omega) h)

lemma cval_eq [Fact q.Prime] (hq : Nat.card G = q) {g : G} (hg : g ≠ 1) (key : G)
    {c : G × G} {v : ZMod q} (hc : CommitsTo g key c v) : cval g key c = v := by
  have hex : ∃ v, CommitsTo g key c v := ⟨v, hc⟩
  rw [cval, dite_eq_left hex]
  exact committed_value_unique hq key hg hex.choose_spec hc

lemma card_le_countP_range {L : ℕ} (S : Finset (Fin L)) (p : ℕ → Bool)
    (hS : ∀ i ∈ S, p i = true) : S.card ≤ (List.range L).countP p := by
  have h1 : (List.range L).countP p = ((Finset.range L).filter fun i => p i = true).card := by
    rw [List.countP_eq_length_filter, Finset.card_def, Finset.filter_val, Finset.range_val,
      Multiset.range]
    simp
  rw [h1, ← Finset.card_map Fin.valEmbedding]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_map, Fin.valEmbedding_apply] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  simp [hS j hj]

lemma filterMap_eq_map {α β : Type*} {f : α → Option β} {g : α → β} :
    ∀ {L : List α}, (∀ a ∈ L, f a = some (g a)) → L.filterMap f = L.map g
  | [], _ => rfl
  | a :: L, hL => by
    rw [List.filterMap_cons, hL a (by simp), List.map_cons,
      filterMap_eq_map fun b hb => hL b (by simp [hb])]

/-! ### Integer functionals of rankings

Step 3 bounds how much the result can move a functional of the counted rankings:
the score of one candidate (Theorem 2) or the difference of two candidates' scores
(Corollary `margin`). `msVal φ M` sums `φ` over a multiset of rankings. -/

section MsVal

variable {m : ℕ}

/-- `∑_{σ ∈ M} φ σ`. -/
def msVal (φ : Equiv.Perm (Fin m) → ℤ) (M : Multiset (Equiv.Perm (Fin m))) : ℤ := (M.map φ).sum

variable (φ : Equiv.Perm (Fin m) → ℤ)

lemma msVal_add (M M' : Multiset (Equiv.Perm (Fin m))) :
    msVal φ (M + M') = msVal φ M + msVal φ M' := by
  simp [msVal]

lemma msVal_map {τ : Type*} (Ts : Finset τ) (σ : τ → Equiv.Perm (Fin m)) :
    msVal φ (Ts.val.map σ) = ∑ t ∈ Ts, φ (σ t) := by
  simp [msVal, Finset.sum_map_val]

lemma msVal_sub (ψ : Equiv.Perm (Fin m) → ℤ) (M : Multiset (Equiv.Perm (Fin m))) :
    msVal (fun σ => φ σ - ψ σ) M = msVal φ M - msVal ψ M := by
  simp [msVal, Multiset.sum_map_sub]

lemma msVal_score (w : Fin m → ℕ) (c : Fin m) (M : Multiset (Equiv.Perm (Fin m))) :
    msVal (fun σ => (score w σ c : ℤ)) M = msScore w M c := by
  induction M using Multiset.induction_on with
  | empty => simp [msVal, msScore]
  | cons σ M ih => simp_all [msVal, msScore]

variable {φ}

lemma msVal_le {hi : ℤ} (hφ : ∀ τ, φ τ ≤ hi) (M : Multiset (Equiv.Perm (Fin m))) :
    msVal φ M ≤ Multiset.card M * hi := by
  unfold msVal
  calc (M.map φ).sum ≤ (M.map fun _ => hi).sum := Multiset.sum_map_le_sum_map _ _ fun τ _ => hφ τ
    _ = Multiset.card M * hi := by simp

lemma le_msVal {lo : ℤ} (hφ : ∀ τ, lo ≤ φ τ) (M : Multiset (Equiv.Perm (Fin m))) :
    Multiset.card M * lo ≤ msVal φ M := by
  unfold msVal
  calc Multiset.card M * lo = (M.map fun _ => lo).sum := by simp
    _ ≤ (M.map φ).sum := Multiset.sum_map_le_sum_map _ _ fun τ _ => hφ τ

end MsVal

/-! ### Consistent ballot parts and faithful tags (Step 4) -/

/-- Part `b` of the paper ballot `B` is *consistent* with `Pub`: its printed codes
are distinct, and the code of candidate `j` opens at a position whose
`E`-commitment commits to `x^j`. This depends only on data fixed at the end of
Setup. -/
def Consistent (P : Params G m) (pub : Pub G q n m κ) (B : PaperBallot q n m) (b : Bool) : Prop :=
  Function.Injective (B.code b) ∧
    ∀ j, ∃ p, CommitsTo P.g pub.key ((pub.part B.tag b).U p) (B.code b j) ∧
      CommitsTo P.g pub.key ((pub.part B.tag b).E p) (encX q P.x j)

section Faithful

variable [Fact q.Prime] (hq : Nat.card G = q) {g : G} (hg : g ≠ 1) (key : G)
include hq hg

/-- **Step 4: a consistent cast part makes its tag faithful.** If the codes of
the cast part are distinct and consistent, the positions routed by (U4) to the
ranks hold the codes of `ω`, and the routed commitments encode `σ`, then
`σ = ω`. This extends `faithful_of_consistent` by the routing argument. -/
theorem faithful_of_routing {x : ℕ} (hx : m < x) (hxq : x ^ m ≤ q) {U E : Fin m → G × G}
    {code : Fin m → ZMod q} (hinj : Function.Injective code)
    (hcons : ∀ j, ∃ p, CommitsTo g key (U p) (code j) ∧ CommitsTo g key (E p) (encX q x j))
    (π : Fin m → Fin m) (ω σ : Equiv.Perm (Fin m))
    (hU : ∀ r, CommitsTo g key (U (π r)) (code (ω r)))
    (hE : ∀ r, CommitsTo g key (E (π r)) (encX q x (σ r))) : σ = ω := by
  choose pos hpos using hcons
  have hposinj : Function.Injective pos := fun j j' hjj => by
    have h' : CommitsTo g key (U (pos j)) (code j') := by rw [hjj]; exact (hpos j').1
    exact hinj (committed_value_unique hq key hg (hpos j).1 h')
  have hπ : ∀ r, π r = pos (ω r) := by
    intro r
    obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.1 hposinj) (π r)
    have h' : CommitsTo g key (U (π r)) (code j) := by rw [← hj]; exact (hpos j).1
    rw [← hj, hinj (committed_value_unique hq key hg h' (hU r))]
  exact faithful_of_consistent hq hg key hx hxq E pos (fun j => (hpos j).2) ω σ
    (fun r => by rw [← hπ r]; exact hE r)

end Faithful

/-! ### Step 2 for the bulletin board -/

/-- **Step 2 on `BB`.** If every cast part routes commitments to `x^{σ_t(i)}`
(Step 1) and (U6) holds, the score vector of `Result(info)` is that of the cast
rankings, in both modes. -/
theorem scw_result_eq [Fact q.Prime] (hq : Nat.card G = q) (P : Params G m) (hg : P.g ≠ 1)
    (hm : 0 < m) (hw : Antitone P.w) (hxq : P.x ^ m ≤ q) (hnx : n * P.W hm < P.x)
    (I : Info G q n m κ) (hU6 : U6 P I) (σ : Fin n → Equiv.Perm (Fin m))
    (hσ : ∀ t ∈ I.castSet, ∀ r, CommitsTo P.g I.pub.key (I.routed t r) (encX q P.x (σ t r)))
    (c : Fin m) : scw P.w (Result P I) c = ∑ t ∈ I.castSet, score P.w (σ t) c := by
  set s := I.castSet
  set σ' : Fin s.card → Equiv.Perm (Fin m) := fun k => σ (enum s k)
  have hcard : s.card ≤ n := card_le_univ s |>.trans (Fintype.card_fin n).le
  have hC : ∀ k r, CommitsTo P.g I.pub.key (I.routed (enum s k) r)
      ((P.x ^ (σ' k r : ℕ) : ℕ) : ZMod q) := fun k r => hσ _ (enum_mem s k) r
  have hsum : ∑ t ∈ s, score P.w (σ t) c = scoreVec P.w σ' c := by
    rw [scoreVec, sum_enum s]
  rw [hsum]
  cases hmode : P.mode with
  | mat =>
    have hn : s.card < P.x := by
      have : P.W hm = 1 := by simp [Params.W, hmode]
      rw [this, mul_one] at hnx
      omega
    simp only [U6, hmode] at hU6
    have hT : ∀ i, ∏ k, I.routed (enum s k) i =
        Com P.g I.pub.key (I.tau.aggMat i).1 (I.tau.aggMat i).2 := fun i => by
      rw [← prod_enum s (fun t => I.routed t i)]
      exact hU6 i
    simp only [Result, hmode, scw]
    rw [← sum_weight_posMatrix]
    refine sum_congr rfl fun i _ => ?_
    rw [decode, (matrix_result_eq hq hg I.pub.key hn hxq σ' (fun k i => I.routed (enum s k) i) hC
      (fun i => (I.tau.aggMat i).1) (fun i => (I.tau.aggMat i).2) hT i).2 c]
  | sc =>
    have hW : ∀ i, P.w i ≤ w₁ P.w hm := fun i => hw (Fin.mk_le_mk.2 (Nat.zero_le _) :
      (⟨0, hm⟩ : Fin m) ≤ i)
    have hn : s.card * w₁ P.w hm < P.x := by
      have : P.W hm = w₁ P.w hm := by simp [Params.W, hmode]
      rw [this] at hnx
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hcard) hnx
    simp only [U6, hmode] at hU6
    have hT : ∏ k, ∏ i, I.routed (enum s k) i ^ P.w i =
        Com P.g I.pub.key I.tau.aggSc.1 I.tau.aggSc.2 := by
      rw [← prod_enum s (fun t => ∏ i, I.routed t i ^ P.w i)]
      exact hU6
    simp only [Result, hmode, scw]
    rw [decode, (score_result_eq hq hg I.pub.key P.w hW hn hxq σ'
      (fun k i => I.routed (enum s k) i) hC _ _ hT).2 c]

/-! ### What the checks of an honest voter give -/

section Run

variable (P : Params G m) (A : Adversary G q n m κ) (h : List Bool)

/-- The tag held by the `i`-th honest voter. -/
def Adversary.tagOf (i : Fin h.length) : Fin n := (A.ballotOf h i).tag

variable {P A h}

lemma voter_psi {i : Fin h.length} (hv : Verify P (A.info h) (A.receipt h i)) :
    (A.info h).tau.psi (A.tagOf h i) =
      some ⟨h[i], fun r => (A.ballotOf h i).code h[i] (A.rankOf h i r)⟩ :=
  hv.2.2.1

lemma voter_coin {i : Fin h.length} (hv : Verify P (A.info h) (A.receipt h i)) :
    (A.info h).coin (A.tagOf h i) = h[i] := by
  simp [Info.coin, voter_psi hv]

lemma voter_cast {i : Fin h.length} (hv : Verify P (A.info h) (A.receipt h i)) :
    A.tagOf h i ∈ (A.info h).castSet := by
  simp [Info.castSet, voter_psi hv]

lemma voter_castPart {i : Fin h.length} (hv : Verify P (A.info h) (A.receipt h i)) :
    (A.info h).castPart (A.tagOf h i) = A.pub.part (A.ballotOf h i).tag h[i] := by
  rw [Info.castPart, voter_coin hv]; rfl

/-- (U3) and (I1) make the audit part of every honest voter consistent. -/
lemma voter_audit (hx : m < P.x) (hxq : P.x ^ m ≤ q) {i : Fin h.length}
    (hv : Verify P (A.info h) (A.receipt h i)) :
    Consistent P A.pub (A.ballotOf h i) (!h[i]) := by
  have hcast := voter_cast hv
  have hcoin := voter_coin hv
  obtain ⟨⟨-, hU3, -⟩, hI1, -⟩ := hv
  obtain ⟨hopen, hdist⟩ := hU3 _ hcast
  have hpart : (A.info h).auditPart (A.tagOf h i) = A.pub.part (A.ballotOf h i).tag (!h[i]) := by
    rw [Info.auditPart, hcoin]; rfl
  rw [hpart] at hopen
  simp only [Adversary.tagOf] at hopen hdist
  simp only [I1, Adversary.receipt] at hI1
  refine ⟨fun j j' hjj => ?_, fun j => ?_⟩
  · obtain ⟨p, hp1, hp2⟩ := hI1 j
    obtain ⟨p', hp1', hp2'⟩ := hI1 j'
    have hpp : p = p' := hdist (hp1.trans (hjj.trans hp1'.symm))
    subst hpp
    exact encX_injective hx hxq (hp2.symm.trans hp2')
  · obtain ⟨p, hp1, hp2⟩ := hI1 j
    exact ⟨p, ⟨_, by rw [(hopen p).1, hp1]; rfl⟩, ⟨_, by rw [(hopen p).2, hp2]; rfl⟩⟩

variable (θ d : ℕ)

lemma universal_of_win (hθ : 1 ≤ θ) (hwin : Win P θ d A h) : Universal P (A.info h) :=
  (hwin.2.1 ⟨0, by have := hwin.1; omega⟩).1

end Run

/-! ### Lemma `amplified`: a commitment outside `𝒳` -/

section Amplified

variable (P : Params G m)

/-- The event `Z` of Lemma `amplified`, given (U5): some cast part has a
commitment that commits to no element of `𝒳`. -/
def Bad (I : Info G q n m κ) : Prop :=
  ∃ t ∈ I.castSet, ∃ p, ∀ j : Fin m, ¬ CommitsTo P.g I.pub.key ((I.castPart t).E p) (encX q P.x j)

/-- The string `c⃗*` that the coins must equal for the membership proofs of the
commitment `j = (tag, part, position)` to accept (`amplified_coins_unique`). It is
fixed by `Pub`. -/
noncomputable def cstar (pub : Pub G q n m κ) (j : Fin n × Bool × Fin m) : Fin n → Bool :=
  Classical.epsilon fun cs => ∀ coins : Fin n → Bool,
    AmpAccept P.g pub.key (encX q P.x) ((pub.part j.1 j.2.1).E j.2.2)
      ((pub.part j.1 j.2.1).φ j.2.2) (challenge κ P.β coins) → coins = cs

/-- The strategy of Lemma `amplified` for commitment `j`: every honest coin is
targeted at the bit of `c⃗*` at the voter's tag. -/
noncomputable def baseZ (A : Adversary G q n m κ) (j : Fin n × Bool × Fin m) :
    List Bool → Option Bool :=
  fun pfx => some (cstar P A.pub j (A.ballot pfx).tag)

variable {P} {A : Adversary G q n m κ} {h : List Bool} {θ d : ℕ}

/-- **Lemma `amplified`, glue.** If the game is won and a cast part has a
commitment outside `𝒳`, then for one of the `2nm` commitments every honest coin
hits its target, and there are at least `θ` of them. -/
theorem win_bad_hits [Fact q.Prime] (hq : Nat.card G = q) (hn : n ≤ κ * P.β) (hβ : 2 ^ P.β ≤ q)
    (hθ : 1 ≤ θ) (hwin : Win P θ d A h) (hbad : Bad P (A.info h)) :
    ∃ j, (∀ i (hi : i < h.length) t, baseZ P A j (h.take i) = some t → h[i] = t) ∧
      θ ≤ (List.range h.length).countP fun i => (baseZ P A j (h.take i)).isSome := by
  obtain ⟨t, ht, p, hp⟩ := hbad
  obtain ⟨-, -, -, hU5, -⟩ := universal_of_win θ d hθ hwin
  set I := A.info h
  have hamp : AmpAccept P.g A.pub.key (encX q P.x) ((A.pub.part t (I.coin t)).E p)
      ((A.pub.part t (I.coin t)).φ p) (challenge κ P.β I.coinString) :=
    fun k => ⟨_, hU5 t ht p k⟩
  obtain ⟨cs, hcs⟩ := amplified_coins_unique hq hn hβ hp ((A.pub.part t (I.coin t)).φ p)
  have hcoin : I.coinString = cstar P A.pub (t, I.coin t, p) :=
    Classical.epsilon_spec (p := fun cs => ∀ coins : Fin n → Bool,
      AmpAccept P.g A.pub.key (encX q P.x) ((A.pub.part t (I.coin t)).E p)
        ((A.pub.part t (I.coin t)).φ p) (challenge κ P.β coins) → coins = cs) ⟨cs, hcs⟩ _ hamp
  refine ⟨(t, I.coin t, p), fun i hi b hb => ?_, ?_⟩
  · simp only [baseZ, Option.some.injEq] at hb
    have := voter_coin (hwin.2.1 ⟨i, hi⟩)
    rw [← hb, ← hcoin]
    exact this.symm
  · simpa [baseZ] using hwin.1

end Amplified

/-! ### Step 4: the coins that the attack must hit -/

section Step4

variable (P : Params G m) (A : Adversary G q n m κ)

open Classical in
/-- The Step 4 strategy. Before the honest voter with paper ballot `B` flips:
* if exactly one part of `B` is inconsistent, its coin must cast that part;
* otherwise, if an earlier honest voter holds the same tag, its coin must repeat
  that voter's coin;
* otherwise the coin is free. -/
noncomputable def base4 (pfx : List Bool) : Option Bool :=
  if Consistent P A.pub (A.ballot pfx) false ∧ ¬ Consistent P A.pub (A.ballot pfx) true then
    some true
  else if ¬ Consistent P A.pub (A.ballot pfx) false ∧ Consistent P A.pub (A.ballot pfx) true then
    some false
  else if hex : ∃ i < pfx.length, (A.ballot (pfx.take i)).tag = (A.ballot pfx).tag then
    some (pfx.getD (Nat.find hex) false)
  else none

variable (h : List Bool)

/-- Honest voters that are not the first holder of their tag. -/
def later : Finset (Fin h.length) :=
  univ.filter fun i => ∃ i', i' < i ∧ A.tagOf h i' = A.tagOf h i

/-- The first holders of the honest tags. -/
def firsts : Finset (Fin h.length) :=
  univ.filter fun i => ¬ ∃ i', i' < i ∧ A.tagOf h i' = A.tagOf h i

open Classical in
/-- First holders whose cast part is inconsistent. -/
noncomputable def badFirsts : Finset (Fin h.length) :=
  (firsts A h).filter fun i => ¬ Consistent P A.pub (A.ballotOf h i) h[i]

variable {P A h} {θ d : ℕ}

/-- Under (2), every coin targeted by the Step 4 strategy hits its target. -/
theorem win_good_hits (hx : m < P.x) (hxq : P.x ^ m ≤ q) (hwin : Win P θ d A h) :
    ∀ i (hi : i < h.length) t, base4 P A (h.take i) = some t → h[i] = t := by
  intro i hi t ht
  have hv := hwin.2.1 ⟨i, hi⟩
  have haud : Consistent P A.pub (A.ballot (h.take i)) (!h[i]) := voter_audit hx hxq hv
  simp only [base4] at ht
  split_ifs at ht with h1 h2 h3
  · cases hb : h[i]
    · rw [hb] at haud; exact absurd haud h1.2
    · simp_all
  · cases hb : h[i]
    · simp_all
    · rw [hb] at haud; exact absurd haud h2.1
  · obtain ⟨hlt, htag⟩ := Nat.find_spec h3
    set i' := Nat.find h3
    have hi' : i' < i := by simp at hlt; omega
    have hv' := hwin.2.1 ⟨i', by omega⟩
    have htake : (h.take i).take i' = h.take i' := by rw [List.take_take, min_eq_left hi'.le]
    rw [htake] at htag
    have e1 := voter_psi hv
    have e2 := voter_psi hv'
    simp only [Adversary.tagOf, Adversary.ballotOf] at e1 e2
    rw [htag, e1, Option.some.injEq] at e2
    have hcoins : h[i'] = h[i] := (congrArg Psi.coin e2).symm
    simp only [Option.some.injEq] at ht
    rw [← ht, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take]
    exact hcoins.symm

/-- Under (2), the Step 4 strategy targets every later holder of a tag and every
first holder whose cast part is inconsistent. -/
theorem win_count (hx : m < P.x) (hxq : P.x ^ m ≤ q) (hwin : Win P θ d A h) :
    (later A h).card + (badFirsts P A h).card
      ≤ (List.range h.length).countP fun i => (base4 P A (h.take i)).isSome := by
  have hdisj : Disjoint (later A h) (badFirsts P A h) := by
    rw [disjoint_left]
    intro i hl hb
    simp only [badFirsts, firsts, later, mem_filter, mem_univ, true_and] at hl hb
    exact hb.1 hl
  rw [← card_union_of_disjoint hdisj]
  apply card_le_countP_range
  intro i hi
  rcases mem_union.1 hi with hl | hb
  · simp only [later, mem_filter, mem_univ, true_and] at hl
    obtain ⟨i', hi'i, htag⟩ := hl
    simp only [base4]
    split_ifs with h1 h2 h3 <;> try rfl
    exfalso
    refine h3 ⟨i', by simp; omega, ?_⟩
    rw [List.take_take, min_eq_left (show (i' : ℕ) ≤ i from hi'i.le)]
    exact htag
  · have haud : Consistent P A.pub (A.ballotOf h i) (!h[i]) := voter_audit hx hxq (hwin.2.1 i)
    simp only [badFirsts, mem_filter] at hb
    have hbad := hb.2
    simp only [base4]
    split_ifs with h1 h2 h3 <;> try rfl
    exfalso
    cases hc : h[i]
    · rw [hc] at haud hbad
      exact h2 ⟨hbad, haud⟩
    · rw [hc] at haud hbad
      exact h1 ⟨haud, hbad⟩

end Step4

/-! ### Steps 1–3 on the bulletin board -/

section Deviation

variable {P : Params G m} [Fact q.Prime] (hq : Nat.card G = q) (hg : P.g ≠ 1)
include hq hg

/-- **Step 1 on `BB`.** Under the universal checks and `¬Z`, every cast part
routes to its ranks the encodings of a ranking. -/
theorem step1_bb (hx : m < P.x) (hxq : P.x ^ m ≤ q) {I : Info G q n m κ} (hU : Universal P I)
    (hgood : ¬ Bad P I) :
    ∀ t ∈ I.castSet, ∃ τ : Equiv.Perm (Fin m),
      ∀ r, CommitsTo P.g I.pub.key (I.routed t r) (encX q P.x (τ r)) := by
  intro t ht
  obtain ⟨hU2, -, hU4, -, -⟩ := hU
  obtain ⟨ψ, hψ⟩ := Option.isSome_iff_exists.1 (by simpa [Info.castSet] using ht)
  have hmem : ∀ p, ∃ j : Fin m,
      CommitsTo P.g I.pub.key ((I.castPart t).E p) ((P.x ^ (j : ℕ) : ℕ) : ZMod q) := by
    intro p
    by_contra hcon
    push Not at hcon
    exact hgood ⟨t, ht, p, hcon⟩
  exact cast_part_ranking hq hg I.pub.key hx hxq _ hmem (hU2 t (I.coin t)) _ (hU4 t ψ hψ).2

/-- Under Step 1, the extractor outputs the cast rankings of the tags outside the
honest receipts; in particular it does not output `⊥` (case (3b) is impossible). -/
theorem extractor_eq (hx : m < P.x) (hxq : P.x ^ m ≤ q) (I : Info G q n m κ)
    (αs : List (Receipt q n m)) (σ : Fin n → Equiv.Perm (Fin m))
    (hσ : ∀ t ∈ I.castSet, ∀ r, CommitsTo P.g I.pub.key (I.routed t r) (encX q P.x (σ t r))) :
    extractor P I αs = some ((extractTags I αs).map σ) := by
  have hone : ∀ t ∈ I.castSet, extractOne P I t = some (σ t) := by
    intro t ht
    have hex : ∃ σ' : Equiv.Perm (Fin m),
        ∀ r, cval P.g I.pub.key (I.routed t r) = encX q P.x (σ' r) :=
      ⟨σ t, fun r => cval_eq hq hg _ (hσ t ht r)⟩
    rw [extractOne, dite_eq_left hex]
    exact congrArg some (Equiv.ext fun r => encX_injective hx hxq
      ((hex.choose_spec r).symm.trans (cval_eq hq hg _ (hσ t ht r))))
  have hsub : ∀ t ∈ extractTags I αs, t ∈ I.castSet := by
    intro t htl
    simp only [extractTags, Finset.mem_sort, mem_filter, mem_univ, true_and] at htl
    simpa [Info.castSet] using htl.1
  rw [extractor, ite_eq_left]
  · rw [filterMap_eq_map fun t ht => hone t (hsub t ht)]
  · rw [List.all_eq_true]
    intro t ht
    rw [hone t (hsub t ht)]
    rfl

omit [CommGroup G] [Fact q.Prime] hq hg in
lemma firsts_injOn (A : Adversary G q n m κ) (h : List Bool) :
    Set.InjOn (A.tagOf h) (firsts A h) := by
  intro i hi j hj hij
  simp only [firsts, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hj ⟨i, hlt, hij⟩
  · exact hi ⟨j, hlt, hij.symm⟩

omit [CommGroup G] [Fact q.Prime] hq hg in
lemma image_firsts (A : Adversary G q n m κ) (h : List Bool) :
    (firsts A h).image (A.tagOf h) = univ.image (A.tagOf h) := by
  apply Subset.antisymm (image_subset_image (subset_univ _))
  intro t ht
  obtain ⟨i, -, rfl⟩ := mem_image.1 ht
  classical
  set fib := univ.filter fun j => A.tagOf h j = A.tagOf h i
  have hne : fib.Nonempty := ⟨i, by simp [fib]⟩
  have hmin := min'_mem fib hne
  simp only [fib, mem_filter, mem_univ, true_and] at hmin
  refine mem_image.2 ⟨fib.min' hne, ?_, hmin⟩
  simp only [firsts, mem_filter, mem_univ, true_and]
  rintro ⟨i', hlt, htag⟩
  have : fib.min' hne ≤ i' := min'_le fib i' (by simp [fib, htag, hmin])
  exact absurd hlt (not_lt.2 this)

omit [CommGroup G] [Fact q.Prime] hq hg in
lemma card_firsts_add_later (A : Adversary G q n m κ) (h : List Bool) :
    (firsts A h).card + (later A h).card = h.length := by
  classical
  rw [add_comm, later, firsts, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]

variable {A : Adversary G q n m κ} {h : List Bool} {θ d : ℕ}

/-- **Steps 1–3, for any functional.** If the game is won and `¬Z`, there are
rankings `σ` of the cast tags such that the result is the score vector of `σ`, the
extractor outputs the cast rankings of the other tags, and the following holds.
Let `ε` be that output and `U` the number of later holders of a tag plus the first
holders whose cast part is inconsistent. For every `φ` with values in `[lo, hi]`,
`lo ≤ 0 ≤ hi`, summing `φ` over the cast rankings and over the argument of `f` in
the game gives values within `(hi - lo) · U`. With `φ` the score of one candidate
this is Step 3 of Theorem 2; with the difference of two candidates' scores it is
the `2Δ` per unit of Corollary `margin`. -/
theorem win_good_val (hm : 0 < m) (hw : Antitone P.w) (hx : m < P.x) (hxq : P.x ^ m ≤ q)
    (hnx : n * P.W hm < P.x) (hθ : 1 ≤ θ) (hwin : Win P θ d A h) (hgood : ¬ Bad P (A.info h)) :
    ∃ σ : Fin n → Equiv.Perm (Fin m),
      (∀ c, scw P.w (Result P (A.info h)) c = ∑ t ∈ (A.info h).castSet, score P.w (σ t) c) ∧
      ∃ ε, extractor P (A.info h) (List.ofFn (A.receipt h)) = some ε ∧
      ∀ (φ : Equiv.Perm (Fin m) → ℤ) (lo hi : ℤ), lo ≤ 0 → 0 ≤ hi → (∀ τ, lo ≤ φ τ ∧ φ τ ≤ hi) →
        |∑ t ∈ (A.info h).castSet, φ (σ t)
            - msVal φ (A.honestRanks h + ↑(ε.take (n - h.length)))|
          ≤ (hi - lo) * ((later A h).card + (badFirsts P A h).card : ℕ) := by
  classical
  set I := A.info h with hI
  set αs := List.ofFn (A.receipt h) with hαs
  have hU := universal_of_win θ d hθ hwin
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin n → Equiv.Perm (Fin m),
      ∀ t ∈ I.castSet, ∀ r, CommitsTo P.g I.pub.key (I.routed t r) (encX q P.x (σ t r)) := by
    have := step1_bb hq hg hx hxq hU hgood
    choose! σ hσ using this
    exact ⟨σ, hσ⟩
  refine ⟨σ, fun c => scw_result_eq hq P hg hm hw hxq hnx I hU.2.2.2.2 σ hσ c,
    (extractTags I αs).map σ, extractor_eq hq hg hx hxq I αs σ hσ, ?_⟩
  intro φ lo hi hlo hhi hφ
  set L := extractTags I αs with hL
  set k := n - h.length
  -- the honest tags and the extracted tags
  set Ts := univ.image (A.tagOf h) with hTs
  have hmemT : ∀ t, t ∈ αs.map Receipt.tag ↔ t ∈ Ts := by
    intro t
    simp [hαs, hTs, List.mem_ofFn, Adversary.receipt, Adversary.tagOf]
  obtain ⟨Lset, hLsort, hLmem⟩ : ∃ Lset : Finset (Fin n), L = Lset.sort (· ≤ ·) ∧
      ∀ t, t ∈ Lset ↔ t ∈ I.castSet ∧ t ∉ Ts :=
    ⟨_, rfl, fun t => by simp [Info.castSet, hmemT]⟩
  have hTsub : Ts ⊆ I.castSet := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := mem_image.1 ht
    exact voter_cast (hwin.2.1 i)
  have hfaith : ∀ i ∈ firsts A h, Consistent P A.pub (A.ballotOf h i) h[i] →
      σ (A.tagOf h i) = A.rankOf h i := by
    intro i _ hcons
    have hv := hwin.2.1 i
    have hcp := voter_castPart hv
    obtain ⟨-, -, hU4, -, -⟩ := hU
    have hU4' := hU4 _ _ (voter_psi hv)
    refine faithful_of_routing hq hg A.pub.key hx hxq hcons.1 hcons.2 (I.tau.castPos (A.tagOf h i))
      (A.rankOf h i) (σ (A.tagOf h i)) (fun r => ⟨I.tau.castRand (A.tagOf h i) r, ?_⟩)
      (fun r => ?_)
    · have := hU4'.1 r
      rw [hcp] at this
      exact this
    · have := hσ _ (voter_cast hv) r
      rw [Info.routed, hcp] at this
      exact this
  set sc : Fin n → ℤ := fun t => φ (σ t)
  set so : Fin h.length → ℤ := fun i => φ (A.rankOf h i)
  -- the result: honest tags plus extracted tags
  have E3 : ∑ t ∈ I.castSet, φ (σ t) = ∑ t ∈ Ts, sc t + ∑ t ∈ Lset, sc t := by
    rw [← sum_filter_add_sum_filter_not I.castSet (· ∈ Ts)]
    congr 1
    · rw [filter_mem_eq_inter, inter_eq_right.2 hTsub]
    · exact sum_congr (by ext t; simp [hLmem, and_comm]) fun _ _ => rfl
  have E4 : ∑ t ∈ Ts, sc t = ∑ i ∈ firsts A h, sc (A.tagOf h i) := by
    rw [hTs, ← image_firsts, sum_image (firsts_injOn A h)]
  have E5 : ∑ i ∈ firsts A h, sc (A.tagOf h i)
      = ∑ i ∈ (firsts A h).filter (fun i => Consistent P A.pub (A.ballotOf h i) h[i]), so i
        + ∑ i ∈ badFirsts P A h, sc (A.tagOf h i) := by
    rw [← sum_filter_add_sum_filter_not (firsts A h)
      (fun i => Consistent P A.pub (A.ballotOf h i) h[i])]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [mem_filter] at hi
    simp only [sc, so, hfaith i hi.1 hi.2]
  -- the honest choices
  have E6 : msVal φ (A.honestRanks h)
      = ∑ i ∈ (firsts A h).filter (fun i => Consistent P A.pub (A.ballotOf h i) h[i]), so i
        + ∑ i ∈ badFirsts P A h, so i + ∑ i ∈ later A h, so i := by
    have hsplit : ∑ i, so i = ∑ i ∈ later A h, so i + ∑ i ∈ firsts A h, so i :=
      (sum_filter_add_sum_filter_not univ _ _).symm
    rw [Adversary.honestRanks, msVal_map, hsplit, add_comm,
      ← sum_filter_add_sum_filter_not (firsts A h)
        (fun i => Consistent P A.pub (A.ballotOf h i) h[i])]
    rfl
  -- the extracted choices: kept and discarded
  have E2 : msVal φ ↑((L.map σ).take k) + msVal φ ↑((L.map σ).drop k) = ∑ t ∈ Lset, sc t := by
    rw [← msVal_add, Multiset.coe_add, List.take_append_drop, ← Multiset.map_coe, hLsort,
      Finset.sort_eq, msVal_map]
  -- counting
  have hcardTs : Ts.card = (firsts A h).card := by
    rw [hTs, ← image_firsts, card_image_of_injOn (firsts_injOn A h)]
  have hFL := card_firsts_add_later A h
  have hLT : Lset.card + Ts.card ≤ n := by
    have hdisj : Disjoint Lset Ts := disjoint_left.2 fun t ht ht' => ((hLmem t).1 ht).2 ht'
    rw [← card_union_of_disjoint hdisj]
    exact (card_le_univ _).trans (Fintype.card_fin n).le
  have hdrop : ((L.map σ).drop k).length ≤ (later A h).card := by
    rw [List.length_drop, List.length_map, hLsort, Finset.length_sort]
    omega
  -- bounds: every term lies in `[lo, hi]`
  set b := (badFirsts P A h).card
  set l := (later A h).card
  have B1 : ∑ i ∈ badFirsts P A h, sc (A.tagOf h i) ≤ b * hi := by
    simpa using sum_le_card_nsmul _ _ hi fun i _ => (hφ _).2
  have B1' : b * lo ≤ ∑ i ∈ badFirsts P A h, sc (A.tagOf h i) := by
    simpa using card_nsmul_le_sum _ _ lo fun i _ => (hφ _).1
  have B2 : ∑ i ∈ badFirsts P A h, so i ≤ b * hi := by
    simpa using sum_le_card_nsmul _ _ hi fun i _ => (hφ _).2
  have B2' : b * lo ≤ ∑ i ∈ badFirsts P A h, so i := by
    simpa using card_nsmul_le_sum _ _ lo fun i _ => (hφ _).1
  have B3 : ∑ i ∈ later A h, so i ≤ l * hi := by
    simpa using sum_le_card_nsmul _ _ hi fun i _ => (hφ _).2
  have B3' : l * lo ≤ ∑ i ∈ later A h, so i := by
    simpa using card_nsmul_le_sum _ _ lo fun i _ => (hφ _).1
  have hdrop' : (((L.map σ).drop k).length : ℤ) ≤ l := by exact_mod_cast hdrop
  have B4 : msVal φ ↑((L.map σ).drop k) ≤ l * hi :=
    (msVal_le (fun τ => (hφ τ).2) _).trans (by simpa using mul_le_mul_of_nonneg_right hdrop' hhi)
  have B4' : l * lo ≤ msVal φ ↑((L.map σ).drop k) := by
    have h1 : (l : ℤ) * lo ≤ (((L.map σ).drop k).length : ℤ) * lo :=
      mul_le_mul_of_nonpos_right hdrop' hlo
    exact h1.trans (by simpa using le_msVal (fun τ => (hφ τ).1) ↑((L.map σ).drop k))
  rw [msVal_add, E6, E3, E4, E5, ← E2]
  generalize ∑ i ∈ (firsts A h).filter (fun i => Consistent P A.pub (A.ballotOf h i) h[i]), so i
    = a1 at *
  generalize ∑ i ∈ badFirsts P A h, sc (A.tagOf h i) = a2 at *
  generalize ∑ i ∈ badFirsts P A h, so i = a3 at *
  generalize ∑ i ∈ later A h, so i = a4 at *
  generalize msVal φ ↑((L.map σ).take k) = e1 at *
  generalize msVal φ ↑((L.map σ).drop k) = e2 at *
  rw [abs_le]
  push_cast
  constructor <;> nlinarith

/-- **Steps 1–3.** If the game is won and `¬Z`, the deviation `d` costs at least
`⌈d / w₁⌉` units: later holders of a tag, and first holders whose cast part is
inconsistent. -/
theorem win_good_units (hm : 0 < m) (hw : Antitone P.w) (hx : m < P.x) (hxq : P.x ^ m ≤ q)
    (hnx : n * P.W hm < P.x) (hθ : 1 ≤ θ) (hwin : Win P θ d A h) (hgood : ¬ Bad P (A.info h)) :
    ⌈(d : ℚ) / w₁ P.w hm⌉₊ ≤ (later A h).card + (badFirsts P A h).card := by
  obtain ⟨σ, hres, ε, hext, hval⟩ := win_good_val hq hg hm hw hx hxq hnx hθ hwin hgood
  have h3 : d ≤ dist P.w (Result P (A.info h))
      (elect P.w P.mode (A.honestRanks h + ↑(ε.take (n - h.length)))) := by
    have := hwin.2.2
    rwa [hext] at this
  set M := A.honestRanks h + ↑(ε.take (n - h.length))
  set W := w₁ P.w hm
  set U := (later A h).card + (badFirsts P A h).card
  have hdev : ∀ c, ((scw P.w (Result P (A.info h)) c : ℤ)
      - scw P.w (elect P.w P.mode M) c).natAbs ≤ W * U := by
    intro c
    have := hval (fun τ => (score P.w τ c : ℤ)) 0 W le_rfl (Nat.cast_nonneg _)
      fun τ => ⟨Nat.cast_nonneg _, by exact_mod_cast score_le_w₁ hw hm τ c⟩
    rw [msVal_score, sub_zero] at this
    rw [scw_elect, hres c]
    have h' : ((((∑ t ∈ (A.info h).castSet, score P.w (σ t) c : ℕ) : ℤ)
        - (msScore P.w M c : ℤ)).natAbs : ℤ) ≤ ((W * U : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      push_cast
      exact this
    exact_mod_cast h'
  have hdist : dist P.w (Result P (A.info h)) (elect P.w P.mode M) ≤ W * U :=
    Finset.sup_le fun c _ => hdev c
  rcases Nat.eq_zero_or_pos W with hW0 | hWpos
  · have hd : d = 0 := by
      have := h3.trans hdist
      rw [hW0, zero_mul] at this
      omega
    simp [hd]
  · exact units_of_deviation hWpos h3 hdist

end Deviation

/-! ### Theorem 2 -/

/-- **Theorem 2 (E2E verifiability).** For every adversary `𝒜` of `G_e2e` (a
deterministic, adaptive, computationally unbounded `EA` that also plays the
corrupted voters), with the extractor `𝓔` of Appendix B,

  `Pr[G_e2e = 1] ≤ 2^{-⌈d/w₁⌉} + 2nm · 2^{-θ}`.

The hypotheses are the parameter conditions of the paper: `x > m`, `x^m ≤ q`,
`n·W < x`, `n ≤ κβ` and `2^β ≤ q`, weights `w₁ ≥ ⋯ ≥ wₘ`, and `θ ≥ 1`. -/
theorem e2e_verifiability [Fact q.Prime] (hq : Nat.card G = q) (P : Params G m) (hg : P.g ≠ 1)
    (hm : 0 < m) (hw : Antitone P.w) (hx : m < P.x) (hxq : P.x ^ m ≤ q)
    (hnx : n * P.W hm < P.x) (hn : n ≤ κ * P.β) (hβ : 2 ^ P.β ≤ q) (θ d : ℕ) (hθ : 1 ≤ θ)
    (A : Adversary G q n m κ) :
    gameE2E P θ d A true ≤ 2⁻¹ ^ ⌈(d : ℚ) / w₁ P.w hm⌉₊ + 2 * n * m * 2⁻¹ ^ θ := by
  rw [gameE2E_apply_true]
  have hbound := e2e_error_bound n (fun c => Win P θ d A (runCoins A.more [] c))
    (fun c => Win P θ d A (runCoins A.more [] c) ∧ Bad P (A.info (runCoins A.more [] c)))
    (fun c => Win P θ d A (runCoins A.more [] c) ∧ ¬ Bad P (A.info (runCoins A.more [] c)))
    (fun c hc => by
      by_cases hb : Bad P (A.info (runCoins A.more [] c))
      exacts [Or.inl ⟨hc, hb⟩, Or.inr ⟨hc, hb⟩])
    (univ : Finset (Fin n × Bool × Fin m)) (fun j => normStrat A.more (baseZ P A j)) θ
    (fun c hc => by
      obtain ⟨j, hj1, hj2⟩ := win_bad_hits hq hn hβ hθ hc.1 hc.2
      exact ⟨j, mem_univ _, succeeds_normStrat _ _ c θ hj1 hj2⟩)
    (normStrat A.more (base4 P A)) ⌈(d : ℚ) / w₁ P.w hm⌉₊
    (fun c hc => succeeds_normStrat _ _ c _ (win_good_hits hx hxq hc.1)
      ((win_good_units hq hg hm hw hx hxq hnx hθ hc.1 hc.2).trans (win_count hx hxq hc.1)))
  refine hbound.trans_eq ?_
  congr 1
  rw [card_univ]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  push_cast
  ring

/-- **Theorem 2 for randomised adversaries.** A randomised adversary is a
distribution over deterministic ones, and its winning probability is the average. -/
theorem e2e_verifiability_rand [Fact q.Prime] (hq : Nat.card G = q) (P : Params G m)
    (hg : P.g ≠ 1) (hm : 0 < m) (hw : Antitone P.w) (hx : m < P.x) (hxq : P.x ^ m ≤ q)
    (hnx : n * P.W hm < P.x) (hn : n ≤ κ * P.β) (hβ : 2 ^ P.β ≤ q) (θ d : ℕ) (hθ : 1 ≤ θ)
    (μ : PMF (Adversary G q n m κ)) :
    gameE2ERand P θ d μ true ≤ 2⁻¹ ^ ⌈(d : ℚ) / w₁ P.w hm⌉₊ + 2 * n * m * 2⁻¹ ^ θ := by
  rw [gameE2ERand, PMF.bind_apply]
  calc ∑' A, μ A * gameE2E P θ d A true
      ≤ ∑' A, μ A * (2⁻¹ ^ ⌈(d : ℚ) / w₁ P.w hm⌉₊ + 2 * n * m * 2⁻¹ ^ θ) :=
        ENNReal.tsum_le_tsum fun A => by
          gcongr
          exact e2e_verifiability hq P hg hm hw hx hxq hnx hn hβ θ d hθ A
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end PDemos
