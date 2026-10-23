import PDemos.ElGamal
import PDemos.Encoding
import PDemos.ScoreBound

/-!
# Theorem 2 (E2E verifiability), deterministic Steps 1–3 (`appendix.tex`, Appendix B)

These are the steps of the proof that hold for every adversary once the event
`¬Z` of Lemma `amplified` holds (every value of every cast part lies in `𝒳`).
Group elements are as in `PDemos.ElGamal`: `G` has prime order `q`, `g ≠ 1`, and
the key `h` is arbitrary. The values of `𝒳` are the residues of the natural
numbers `x ^ j`, `j < m`.

* **Step 1** (`part_encodes_permutation`, `cast_part_ranking`): a ballot part whose
  `m` commitments each commit to an element of `𝒳` and whose product opens to `S`
  (check (U2)) commits to a permutation of `𝒳`. This is the "Soundness of the
  validity check" paragraph of Appendix A. With the distinct routing of (U4), the
  values routed to ranks `0, …, m-1` are `x^{σ(0)}, …, x^{σ(m-1)}` for a ranking `σ`.
* **Step 2** (`matrix_result_eq`, `score_result_eq`): if the aggregates open as
  required by (U6), the decoded result equals `f` of the encoded rankings, in
  both modes. `sum_weight_posMatrix` shows that `sc_w(f_mat(σ)) = f_sc(σ)`.
* **Step 3** (`deviation_le`): the result and the argument of `f` in the game
  have score vectors within `w₁ · U` of each other, where
  `U = ∑_t ([σ_t ≠ ω_t] + y_t - 1)`. `extractor_truncation` checks the counting of
  surplus extracted choices, and `units_of_deviation` gives `U ≥ ⌈d / w₁⌉`.
* **Step 4, deterministic part** (`faithful_of_consistent`): a tag whose cast part
  is consistent is faithful.
-/

namespace PDemos

open Finset

/-! ### Step 1: every cast part encodes a ranking -/

section Commitments

variable {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime]
  (hq : Nat.card G = q) {g : G} (hg : g ≠ 1) (h : G) {x m : ℕ}
include hq hg

/-- **Step 1** / soundness of the validity check (Appendix A). Let every
commitment `E p` of a part commit to some element of `𝒳`, and let `⨀ₚ E p` open to
`S = ∑ⱼ xʲ` (check (U2)). If `x > m` and `x^m ≤ q`, the committed values are a
permutation of `𝒳`. -/
theorem part_encodes_permutation (hx : m < x) (hxq : x ^ m ≤ q) (E : Fin m → G × G)
    (hmem : ∀ p, ∃ j : Fin m, CommitsTo g h (E p) ((x ^ (j : ℕ) : ℕ) : ZMod q))
    {R : ZMod q} (hsum : ∏ p, E p = Com g h ((S x m : ℕ) : ZMod q) R) :
    ∃ σ : Equiv.Perm (Fin m), ∀ p, CommitsTo g h (E p) ((x ^ (σ p : ℕ) : ℕ) : ZMod q) := by
  choose J hJ using hmem
  -- by the homomorphism and perfect binding, the values sum to `S` modulo `q`
  have hprod := CommitsTo.prod hq g h univ (fun p _ => hJ p)
  have hval := committed_value_unique hq h hg hprod ⟨R, hsum⟩
  rw [← Nat.cast_sum, ZMod.natCast_eq_natCast_iff] at hval
  -- hence over the integers, and the Encoding Lemma applies
  have hv : ∀ p, ∃ j : Fin m, x ^ (J p : ℕ) = x ^ (j : ℕ) := fun p => ⟨J p, rfl⟩
  obtain ⟨σ, hσ⟩ := (encoding_lemma hx _ hv).1 (sum_eq_S_of_modEq hx hxq _ hv hval)
  exact ⟨σ, fun p => hσ p ▸ hJ p⟩

/-- **Step 1, routed form.** If, in addition, the ranks are routed to pairwise
distinct positions `π i` (check (U4)), the values routed to the ranks encode a
ranking `τ`: rank `i` receives a commitment to `x^{τ i}`. -/
theorem cast_part_ranking (hx : m < x) (hxq : x ^ m ≤ q) (E : Fin m → G × G)
    (hmem : ∀ p, ∃ j : Fin m, CommitsTo g h (E p) ((x ^ (j : ℕ) : ℕ) : ZMod q))
    {R : ZMod q} (hsum : ∏ p, E p = Com g h ((S x m : ℕ) : ZMod q) R)
    (π : Fin m → Fin m) (hπ : Function.Injective π) :
    ∃ τ : Equiv.Perm (Fin m), ∀ i, CommitsTo g h (E (π i)) ((x ^ (τ i : ℕ) : ℕ) : ZMod q) := by
  obtain ⟨σ, hσ⟩ := part_encodes_permutation hq hg h hx hxq E hmem hsum
  have hπb : Function.Bijective π := Finite.injective_iff_bijective.1 hπ
  exact ⟨(Equiv.ofBijective π hπb).trans σ, fun i => hσ (π i)⟩

/-! ### Step 2: tallied as recorded -/

variable {n : ℕ}

/-- **Step 2, matrix mode.** Let `C ℓ i` be the commitment that cast ballot `ℓ`
routes to rank `i`, committing to `x^{σ ℓ i}` (Step 1). If the aggregate of rank
`i` opens to `T i` (check (U6)), `n < x` and `x^m ≤ q`, then `T i`, read as an
integer in `[0, q)`, equals `Tᵢ = ∑ₗ x^{σₗ(i)}`, and its base-`x` digits are the
entries `N i j` of `f_mat(σ)`. -/
theorem matrix_result_eq (hn : n < x) (hxq : x ^ m ≤ q) (σ : Fin n → Equiv.Perm (Fin m))
    (C : Fin n → Fin m → G × G)
    (hC : ∀ ℓ i, CommitsTo g h (C ℓ i) ((x ^ (σ ℓ i : ℕ) : ℕ) : ZMod q))
    (T R : Fin m → ZMod q) (hT : ∀ i, ∏ ℓ, C ℓ i = Com g h (T i) (R i)) (i : Fin m) :
    (T i).val = rankTally x σ i ∧ ∀ j : Fin m, (T i).val / x ^ (j : ℕ) % x = posMatrix σ i j := by
  have hprod := CommitsTo.prod hq g h univ (fun ℓ _ => hC ℓ i)
  have hval := committed_value_unique hq h hg ⟨R i, hT i⟩ hprod
  rw [← Nat.cast_sum] at hval
  have hTi : (T i).val = rankTally x σ i := by
    rw [hval, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt ((rankTally_lt hn σ i).trans_le hxq)
  exact ⟨hTi, fun j => hTi ▸ rankTally_digit hn σ i j⟩

/-- **Step 2, score mode.** If the weighted aggregate `⨀ₗ ⨀ᵢ (C ℓ i)^{wᵢ}` opens to
`T` (check (U6)), every weight is at most `W`, `n W < x` and `x^m ≤ q`, then the
base-`x` digits of `T` are the scores `f_sc(σ)`. -/
theorem score_result_eq {W : ℕ} (w : Fin m → ℕ) (hW : ∀ i, w i ≤ W) (hn : n * W < x)
    (hxq : x ^ m ≤ q) (σ : Fin n → Equiv.Perm (Fin m)) (C : Fin n → Fin m → G × G)
    (hC : ∀ ℓ i, CommitsTo g h (C ℓ i) ((x ^ (σ ℓ i : ℕ) : ℕ) : ZMod q))
    (T R : ZMod q) (hT : ∏ ℓ, ∏ i, C ℓ i ^ w i = Com g h T R) :
    T.val = scoreTally x w σ ∧ ∀ c : Fin m, T.val / x ^ (c : ℕ) % x = scoreVec w σ c := by
  have hprod := CommitsTo.prod hq g h univ (fun ℓ _ =>
    CommitsTo.prod hq g h univ (fun i _ => (hC ℓ i).pow hq g h (w i)))
  have hval := committed_value_unique hq h hg ⟨R, hT⟩ hprod
  simp only [← Nat.cast_mul, ← Nat.cast_sum] at hval
  have hT' : T.val = scoreTally x w σ := by
    rw [hval, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt ((scoreTally_lt w hW hn σ).trans_le hxq)
  exact ⟨hT', fun c => hT' ▸ scoreTally_digit w hW hn σ c⟩

/-! ### Step 4, deterministic part: a consistent cast part is faithful -/

/-- If the cast part of a tag is *consistent* (the code printed next to candidate
`j` opens at position `pos j`, whose commitment commits to `x^j`), and the voter
ranked candidate `ω i` at rank `i`, then the ranking `σ` that Step 1 extracts
from the routed commitments is `ω`: the tag is faithful. -/
theorem faithful_of_consistent (hx : m < x) (hxq : x ^ m ≤ q) (E : Fin m → G × G)
    (pos : Fin m → Fin m) (hcons : ∀ j, CommitsTo g h (E (pos j)) ((x ^ (j : ℕ) : ℕ) : ZMod q))
    (ω σ : Equiv.Perm (Fin m))
    (hσ : ∀ i, CommitsTo g h (E (pos (ω i))) ((x ^ (σ i : ℕ) : ℕ) : ZMod q)) : σ = ω := by
  ext i
  have hv := committed_value_unique hq h hg (hσ i) (hcons (ω i))
  have hlt : ∀ j : Fin m, x ^ (j : ℕ) < q := fun j =>
    (Nat.pow_lt_pow_right (by have := j.pos; omega) j.isLt).trans_le hxq
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt _), Nat.mod_eq_of_lt (hlt _)] at hv
  exact Nat.pow_right_injective (by have := (σ i).pos; omega) hv

end Commitments

/-- In matrix mode, `sc_w(N) = (∑ᵢ wᵢ N i j)ⱼ` is the score vector, so `δ` compares
score vectors in both modes. -/
theorem sum_weight_posMatrix {n m : ℕ} (w : Fin m → ℕ) (ω : Fin n → Equiv.Perm (Fin m))
    (j : Fin m) : ∑ i, w i * posMatrix ω i j = scoreVec w ω j := by
  simp only [posMatrix, card_filter, mul_sum, mul_ite, mul_one, mul_zero, scoreVec, score]
  rw [sum_comm]
  refine sum_congr rfl fun ℓ _ => ?_
  simp_rw [← Equiv.eq_symm_apply]
  simp

/-! ### Step 3: counting the deviation -/

section Deviation

variable {m : ℕ} (w : Fin m → ℕ)

/-- Score of candidate `c` in a multiset of rankings (abstentions are absent). -/
def msScore (M : Multiset (Equiv.Perm (Fin m))) (c : Fin m) : ℕ :=
  (M.map fun σ => score w σ c).sum

lemma msScore_add (M M' : Multiset (Equiv.Perm (Fin m))) (c : Fin m) :
    msScore w (M + M') c = msScore w M c + msScore w M' c := by
  simp [msScore]

lemma msScore_replicate (k : ℕ) (σ : Equiv.Perm (Fin m)) (c : Fin m) :
    msScore w (Multiset.replicate k σ) c = k * score w σ c := by
  simp [msScore]

lemma msScore_finsetSum {τ : Type*} (Ts : Finset τ) (M : τ → Multiset (Equiv.Perm (Fin m)))
    (c : Fin m) : msScore w (∑ t ∈ Ts, M t) c = ∑ t ∈ Ts, msScore w (M t) c := by
  classical
  induction Ts using Finset.induction_on with
  | empty => simp [msScore]
  | insert t Ts ht ih => rw [sum_insert ht, sum_insert ht, msScore_add, ih]

lemma msScore_map {τ : Type*} (Ts : Finset τ) (σ : τ → Equiv.Perm (Fin m)) (c : Fin m) :
    msScore w (Ts.val.map σ) c = ∑ t ∈ Ts, score w (σ t) c := by
  simp [msScore, Finset.sum_map_val]

/-- The score vector of a profile `ω : Fin n → Perm` is `msScore` of its multiset. -/
lemma msScore_profile {n : ℕ} (ω : Fin n → Equiv.Perm (Fin m)) (c : Fin m) :
    msScore w (univ.val.map ω) c = scoreVec w ω c := by
  rw [msScore_map]; rfl

variable {w} (hw : Antitone w) (hm : 0 < m)

/-- `w₁`, the largest weight. -/
def w₁ (w : Fin m → ℕ) (hm : 0 < m) : ℕ := w ⟨0, hm⟩

include hw in
lemma score_le_w₁ (σ : Equiv.Perm (Fin m)) (c : Fin m) : score w σ c ≤ w₁ w hm :=
  hw (Fin.mk_le_mk.2 (Nat.zero_le _) : (⟨0, hm⟩ : Fin m) ≤ σ.symm c)

include hw in
lemma msScore_le (M : Multiset (Equiv.Perm (Fin m))) (c : Fin m) :
    msScore w M c ≤ Multiset.card M * w₁ w hm := by
  unfold msScore
  calc (M.map fun σ => score w σ c).sum ≤ (M.map fun _ => w₁ w hm).sum :=
        Multiset.sum_map_le_sum_map _ _ fun σ _ => score_le_w₁ hw hm σ c
    _ = Multiset.card M * w₁ w hm := by simp

include hw in
/-- **Step 3 of Theorem 2.** Let `Ts` be the honest tags. Tag `t` carries the cast
ranking `σ t` (Step 1) and is held by `y t ≥ 1` honest voters, who all voted
`ω t`. The result counts `σ t` once per tag plus the extracted choices `ε`. The
argument of `f` in the game counts `ω t` with multiplicity `y t` plus the
extracted choices `ε' ≤ ε` that remain after truncation, where at most
`∑ₜ (y t - 1)` choices were dropped. Then every candidate's score differs by at
most `w₁ · U`, where `U = ∑ₜ ([σ t ≠ ω t] + y t - 1)`. -/
theorem deviation_le {τ : Type*} [DecidableEq (Equiv.Perm (Fin m))] (Ts : Finset τ)
    (σ ω : τ → Equiv.Perm (Fin m)) (y : τ → ℕ) (hy : ∀ t ∈ Ts, 1 ≤ y t)
    (ε ε' : Multiset (Equiv.Perm (Fin m))) (hε : ε' ≤ ε)
    (hcard : Multiset.card ε ≤ Multiset.card ε' + ∑ t ∈ Ts, (y t - 1)) (c : Fin m) :
    |(msScore w (Ts.val.map σ + ε) c : ℤ)
        - msScore w ((∑ t ∈ Ts, Multiset.replicate (y t) (ω t)) + ε') c|
      ≤ w₁ w hm * ∑ t ∈ Ts, ((if σ t = ω t then 0 else 1) + (y t - 1)) := by
  set W := w₁ w hm
  set Y := ∑ t ∈ Ts, (y t - 1) with hYdef
  obtain ⟨δε, rfl⟩ := Multiset.le_iff_exists_add.1 hε
  have hδε : Multiset.card δε ≤ Y := by simp at hcard; omega
  simp only [msScore_add, msScore_map, msScore_finsetSum, msScore_replicate]
  -- one copy of `ω t` is compared with `σ t`, the other `y t - 1` copies are missing
  have hsplit : ∀ t ∈ Ts, ((y t : ℤ) * score w (ω t) c)
      = score w (ω t) c + ((y t - 1 : ℕ) : ℤ) * score w (ω t) c := fun t ht => by
    have := hy t ht
    push_cast [Nat.cast_sub this]
    ring
  set P : ℤ := ∑ t ∈ Ts, ((score w (σ t) c : ℤ) - score w (ω t) c) with hPdef
  set Q : ℤ := (msScore w δε c : ℤ) - ∑ t ∈ Ts, ((y t - 1 : ℕ) : ℤ) * score w (ω t) c
    with hQdef
  have hdiff : ((∑ t ∈ Ts, score w (σ t) c + (msScore w ε' c + msScore w δε c) : ℕ) : ℤ)
      - ((∑ t ∈ Ts, y t * score w (ω t) c + msScore w ε' c : ℕ) : ℤ) = P + Q := by
    rw [hPdef, hQdef]
    push_cast
    rw [sum_congr rfl hsplit, sum_add_distrib, sum_sub_distrib]
    ring
  rw [hdiff]
  -- the replaced copies: one per non-faithful tag, each costing at most `W`
  have hP : |P| ≤ W * ((∑ t ∈ Ts, (if σ t = ω t then 0 else 1 : ℕ) : ℕ) : ℤ) := by
    calc |P| ≤ ∑ t ∈ Ts, |(score w (σ t) c : ℤ) - score w (ω t) c| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Ts, ((W : ℤ) * ((if σ t = ω t then 0 else 1 : ℕ) : ℤ)) :=
          sum_le_sum fun t _ => by
            have h1 := score_le_w₁ hw hm (σ t) c
            have h2 := score_le_w₁ hw hm (ω t) c
            split_ifs with heq
            · simp [heq]
            · rw [abs_le]; push_cast; constructor <;> omega
      _ = _ := by rw [Nat.cast_sum, mul_sum]
  -- missing copies lower the score, surplus choices raise it: at most `W · Y` either way
  have hQ : |Q| ≤ W * Y := by
    have hlo : (0 : ℤ) ≤ ∑ t ∈ Ts, ((y t - 1 : ℕ) : ℤ) * score w (ω t) c :=
      sum_nonneg fun t _ => by positivity
    have hhi : ∑ t ∈ Ts, ((y t - 1 : ℕ) : ℤ) * score w (ω t) c ≤ W * Y := by
      have : ∑ t ∈ Ts, (y t - 1) * score w (ω t) c ≤ W * Y := by
        rw [hYdef, mul_comm, sum_mul]
        exact sum_le_sum fun t _ => Nat.mul_le_mul_left _ (score_le_w₁ hw hm (ω t) c)
      exact_mod_cast this
    have hδ : (msScore w δε c : ℤ) ≤ W * Y := by
      have : msScore w δε c ≤ W * Y :=
        (msScore_le hw hm δε c).trans (by rw [mul_comm]; exact Nat.mul_le_mul_left _ hδε)
      exact_mod_cast this
    have hδ0 : (0 : ℤ) ≤ msScore w δε c := by positivity
    rw [abs_le]; constructor <;> linarith
  calc |P + Q| ≤ |P| + |Q| := abs_add_le _ _
    _ ≤ W * ((∑ t ∈ Ts, (if σ t = ω t then 0 else 1 : ℕ) : ℕ) : ℤ) + W * Y := add_le_add hP hQ
    _ = _ := by rw [sum_add_distrib, Nat.cast_add, mul_add]

end Deviation

/-- **Truncation by the extractor.** The extracted choices `ε` (one per cast ballot
whose tag is not honest, `|ε| = n - |Ts|`) are assigned in order to the
`n - ∑ₜ y t` voters outside `𝒱_succ`. The dropped surplus is at most
`∑ₜ (y t - 1)`, as `deviation_le` requires. -/
theorem extractor_truncation {α τ : Type*} {n : ℕ} (Ts : Finset τ) (y : τ → ℕ)
    (hy : ∀ t ∈ Ts, 1 ≤ y t) (hn : ∑ t ∈ Ts, y t ≤ n) (ε : List α)
    (hε : ε.length = n - Ts.card) :
    ((ε.take (n - ∑ t ∈ Ts, y t) : List α) : Multiset α) ≤ ε ∧
      Multiset.card (ε : Multiset α)
        ≤ Multiset.card ((ε.take (n - ∑ t ∈ Ts, y t) : List α) : Multiset α)
          + ∑ t ∈ Ts, (y t - 1) := by
  refine ⟨Multiset.coe_le.2 (List.take_sublist _ _).subperm, ?_⟩
  have hsum : ∑ t ∈ Ts, (y t - 1) + Ts.card = ∑ t ∈ Ts, y t := by
    rw [card_eq_sum_ones, ← sum_add_distrib]
    exact sum_congr rfl fun t ht => Nat.sub_add_cancel (hy t ht)
  simp only [Multiset.coe_card, List.length_take]
  omega

/-- **From the deviation to the number of units.** If the game requires
`δ ≥ d`, Step 3 gives `δ ≤ w₁ · U`, and `w₁ > 0`, then `U ≥ ⌈d / w₁⌉`. -/
theorem units_of_deviation {d δ w₁ U : ℕ} (hw : 0 < w₁) (hd : d ≤ δ) (hδ : δ ≤ w₁ * U) :
    ⌈(d : ℚ) / w₁⌉₊ ≤ U := by
  rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hw)]
  exact_mod_cast hd.trans (hδ.trans_eq (mul_comm _ _))

end PDemos
