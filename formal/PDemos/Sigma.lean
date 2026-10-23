import PDemos.ElGamal
import PDemos.Digits

/-!
# Σ-protocol soundness (`background.tex`, Section 2; `appendix.tex`, Lemma `amplified`)

* **Chaum–Pedersen.** For a statement `(u₁, u₂)`, read as "`log_g u₁ = log_h u₂`",
  a transcript `(a, e, z)` accepts iff `g^z = a₁ u₁^e` and `h^z = a₂ u₂^e`.
  Special soundness (`cp_special_soundness`): two accepting transcripts with the
  same `a` and `e ≠ e'` give the witness `r = (z - z') / (e - e')`.
* **CDS OR-proof** for "`c` commits to some `s ∈ 𝒳 = {s₁, …, s_k}`". Branch `j` is
  a Chaum–Pedersen proof for `(c₁, c₂ / g^{s_j})`, and the branch challenges must
  sum to `e`. `cds_challenge_unique` is the Claim inside the proof of Lemma
  `amplified`: if `c` commits to a value outside `𝒳`, then for fixed first
  messages at most one challenge `e` admits accepting responses.
* **Amplification and challenge derivation.** With `κ` parallel instances, the
  accepted challenge vectors form a subsingleton (`amplified_challenge_unique`).
  The voters' coins are cut into `κ` blocks of `β` bits with `2^β ≤ q`, and each
  block is read in binary as an element of `ℤ_q`. This map is injective
  (`challenge_injective`), so acceptance forces the coin string to equal one
  string `c⃗*` fixed by the posted data (`amplified_coins_unique`).
-/

namespace PDemos

open Finset

variable {G : Type*} [CommGroup G] {q : ℕ}

/-! ### Chaum–Pedersen -/

/-- Verifier of the Chaum–Pedersen protocol for `log_g u.1 = log_h u.2`. -/
def CPAccept (g h : G) (u : G × G) (a : G × G) (e z : ZMod q) : Prop :=
  g ^ₘ z = a.1 * u.1 ^ₘ e ∧ h ^ₘ z = a.2 * u.2 ^ₘ e

/-- The Chaum–Pedersen statement for "`c` commits to `s`": `(c₁, c₂ / g^s)`. -/
def cpStatement (g : G) (c : G × G) (s : ZMod q) : G × G := (c.1, c.2 / g ^ₘ s)

section

variable [Fact q.Prime] (hq : Nat.card G = q)
include hq

/-- One component of special soundness: from `x^z = a·y^e` and `x^{z'} = a·y^{e'}`
with `e ≠ e'`, the discrete logarithm of `y` to base `x` is `(z - z') / (e - e')`. -/
lemma extract_log {x y a : G} {e z e' z' : ZMod q} (h₁ : x ^ₘ z = a * y ^ₘ e)
    (h₂ : x ^ₘ z' = a * y ^ₘ e') (he : e ≠ e') : y = x ^ₘ ((z - z') / (e - e')) := by
  have hsub : x ^ₘ (z - z') = y ^ₘ (e - e') := by
    rw [zpowq_sub hq, zpowq_sub hq, h₁, h₂, ← div_eq_mul_inv, ← div_eq_mul_inv,
      mul_div_mul_left_eq_div]
  rw [div_eq_mul_inv, zpowq_mul hq, hsub, ← zpowq_mul hq,
    mul_inv_cancel₀ (sub_ne_zero.2 he), zpowq_one hq]

/-- **Special soundness of Chaum–Pedersen.** Two accepting transcripts with the same
first message and different challenges yield `r` with `u₁ = g^r` and `u₂ = h^r`. -/
theorem cp_special_soundness {g h : G} {u a : G × G} {e z e' z' : ZMod q}
    (h₁ : CPAccept g h u a e z) (h₂ : CPAccept g h u a e' z') (he : e ≠ e') :
    u.1 = g ^ₘ ((z - z') / (e - e')) ∧ u.2 = h ^ₘ ((z - z') / (e - e')) :=
  ⟨extract_log hq h₁.1 h₂.1 he, extract_log hq h₁.2 h₂.2 he⟩

omit [Fact q.Prime] hq in
/-- The witness for `cpStatement g c s` is an opening of `c` to `s`. -/
lemma commitsTo_of_cpStatement {g h : G} {c : G × G} {s r : ZMod q}
    (h₁ : (cpStatement g c s).1 = g ^ₘ r) (h₂ : (cpStatement g c s).2 = h ^ₘ r) :
    CommitsTo g h c s :=
  ⟨r, Prod.ext h₁ (by
    simp only [cpStatement] at h₂
    simp [Com, ← h₂, mul_div_cancel])⟩

/-- Special soundness, commitment form: two accepting transcripts for
"`c` commits to `s`" with different challenges show that `c` does commit to `s`. -/
theorem cp_extract_commitment {g h : G} {c a : G × G} {s e z e' z' : ZMod q}
    (h₁ : CPAccept g h (cpStatement g c s) a e z)
    (h₂ : CPAccept g h (cpStatement g c s) a e' z') (he : e ≠ e') :
    CommitsTo g h c s :=
  have hw := cp_special_soundness hq h₁ h₂ he
  commitsTo_of_cpStatement hw.1 hw.2

end

/-! ### CDS OR-composition -/

section CDS

variable {k : ℕ}

/-- Verifier of the CDS OR-proof that `c` commits to one of `s 0, …, s (k-1)`.
`a j` is the first message of branch `j`, and `resp j = (e_j, z_j)`. -/
def CDSAccept (g h : G) (s : Fin k → ZMod q) (c : G × G) (a : Fin k → G × G)
    (e : ZMod q) (resp : Fin k → ZMod q × ZMod q) : Prop :=
  ∑ j, (resp j).1 = e ∧ ∀ j, CPAccept g h (cpStatement g c (s j)) (a j) (resp j).1 (resp j).2

variable [Fact q.Prime] (hq : Nat.card G = q)
include hq

/-- **Special soundness of the OR-proof.** Two accepting transcripts with the same
first messages and different challenges show that `c` commits to some `s j`. -/
theorem cds_special_soundness {g h : G} {s : Fin k → ZMod q} {c : G × G}
    {a : Fin k → G × G} {e e' : ZMod q} {resp resp' : Fin k → ZMod q × ZMod q}
    (h₁ : CDSAccept g h s c a e resp) (h₂ : CDSAccept g h s c a e' resp') (he : e ≠ e') :
    ∃ j, CommitsTo g h c (s j) := by
  -- the branch challenges sum to different values, so they differ somewhere
  have : ∃ j, (resp j).1 ≠ (resp' j).1 := by
    by_contra! hall
    exact he (h₁.1.symm.trans ((sum_congr rfl fun j _ => hall j).trans h₂.1))
  obtain ⟨j, hj⟩ := this
  exact ⟨j, cp_extract_commitment hq (h₁.2 j) (h₂.2 j) hj⟩

/-- **Claim in the proof of Lemma `amplified`.** If `c` commits to no element of
`𝒳`, then for fixed first messages at most one challenge admits accepting
responses. -/
theorem cds_challenge_unique {g h : G} {s : Fin k → ZMod q} {c : G × G}
    (hc : ∀ j, ¬ CommitsTo g h c (s j)) (a : Fin k → G × G) :
    {e : ZMod q | ∃ resp, CDSAccept g h s c a e resp}.Subsingleton := by
  rintro e ⟨resp, h₁⟩ e' ⟨resp', h₂⟩
  by_contra he
  obtain ⟨j, hj⟩ := cds_special_soundness hq h₁ h₂ he
  exact hc j hj

/-- The same claim, with the hypothesis as in the paper: `c` commits to a value
`v ∉ 𝒳`. Perfect binding turns this into "`c` commits to no element of `𝒳`". -/
theorem cds_challenge_unique_of_value {g h : G} (hg : g ≠ 1) {s : Fin k → ZMod q}
    {c : G × G} {v : ZMod q} (hv : CommitsTo g h c v) (hvX : v ∉ Set.range s)
    (a : Fin k → G × G) :
    {e : ZMod q | ∃ resp, CDSAccept g h s c a e resp}.Subsingleton :=
  cds_challenge_unique hq (fun j hj =>
    hvX ⟨j, (committed_value_unique hq h hg hv hj).symm⟩) a

/-! ### Amplification -/

variable {κ : ℕ}

/-- All `κ` parallel instances accept, instance `i` answering challenge `e i`. -/
def AmpAccept (g h : G) (s : Fin k → ZMod q) (c : G × G) (a : Fin κ → Fin k → G × G)
    (e : Fin κ → ZMod q) : Prop :=
  ∀ i, ∃ resp, CDSAccept g h s c (a i) (e i) resp

omit [Fact q.Prime] hq in
/-- If every component ranges over a subsingleton, so does the vector. -/
lemma pi_subsingleton {ι α : Type*} {P : ι → α → Prop} (hP : ∀ i, {x | P i x}.Subsingleton) :
    {f : ι → α | ∀ i, P i (f i)}.Subsingleton :=
  fun _ hf _ hf' => funext fun i => hP i (hf i) (hf' i)

/-- For a commitment outside `𝒳`, at most one challenge vector makes all `κ`
instances accept. -/
theorem amplified_challenge_unique {g h : G} {s : Fin k → ZMod q} {c : G × G}
    (hc : ∀ j, ¬ CommitsTo g h c (s j)) (a : Fin κ → Fin k → G × G) :
    {e : Fin κ → ZMod q | AmpAccept g h s c a e}.Subsingleton :=
  pi_subsingleton fun i => cds_challenge_unique hq hc (a i)

end CDS

/-! ### Challenge derivation from the voters' coins -/

/-- A block of `β` bits read in binary (least significant bit first). -/
def blockNat {β : ℕ} (b : Fin β → Bool) : ℕ := digitSum 2 (fun i => (b i).toNat)

lemma blockNat_lt {β : ℕ} (b : Fin β → Bool) : blockNat b < 2 ^ β :=
  digitSum_lt _ fun _ => Bool.toNat_lt _

lemma blockNat_injective {β : ℕ} : Function.Injective (blockNat (β := β)) := by
  intro b b' h
  have := digitSum_injective (fun i => Bool.toNat_lt (b i)) (fun i => Bool.toNat_lt (b' i)) h
  funext i
  have hi := congrFun this i
  cases hb : b i <;> cases hb' : b' i <;> simp_all

/-- A block of `β` bits as an element of `ℤ_q`. -/
def blockValue {β : ℕ} (b : Fin β → Bool) : ZMod q := (blockNat b : ZMod q)

/-- With `2^β ≤ q`, distinct blocks give distinct elements of `ℤ_q`. -/
lemma blockValue_injective {β : ℕ} (hβ : 2 ^ β ≤ q) :
    Function.Injective (blockValue (q := q) (β := β)) := by
  intro b b' h
  apply blockNat_injective
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  rwa [Nat.mod_eq_of_lt ((blockNat_lt b).trans_le hβ),
    Nat.mod_eq_of_lt ((blockNat_lt b').trans_le hβ)] at this

/-- Cut a string of `n` coins into `κ` consecutive blocks of `β` bits, padding the
last block with zeros. -/
def toBlocks {n β : ℕ} (κ : ℕ) (c : Fin n → Bool) : Fin κ → Fin β → Bool :=
  fun i j => if h : i.val * β + j.val < n then c ⟨i.val * β + j.val, h⟩ else false

lemma toBlocks_injective {κ n β : ℕ} (hn : n ≤ κ * β) :
    Function.Injective (toBlocks (n := n) (β := β) κ) := by
  intro c c' h
  funext l
  have hβ : 0 < β := by
    rcases Nat.eq_zero_or_pos β with rfl | h
    · have := l.isLt; simp at hn; omega
    · exact h
  have hi : l.val / β < κ := by
    rw [Nat.div_lt_iff_lt_mul hβ]; exact lt_of_lt_of_le l.isLt hn
  have hl : l.val / β * β + l.val % β = l.val := by rw [mul_comm]; exact Nat.div_add_mod _ _
  have := congrFun (congrFun h ⟨l.val / β, hi⟩) ⟨l.val % β, Nat.mod_lt _ hβ⟩
  simp only [toBlocks, hl, l.isLt, dite_true] at this
  exact this

/-- The challenge vector `(e₁, …, e_κ)` derived from the coin string `c⃗`. -/
def challenge {n : ℕ} (κ β : ℕ) (c : Fin n → Bool) : Fin κ → ZMod q :=
  fun i => blockValue (toBlocks (β := β) κ c i)

lemma challenge_injective {κ n β : ℕ} (hn : n ≤ κ * β) (hβ : 2 ^ β ≤ q) :
    Function.Injective (challenge (q := q) (n := n) κ β) :=
  fun _ _ h => toBlocks_injective hn
    (funext fun i => blockValue_injective hβ (congrFun h i))

/-- **Lemma `amplified`, deterministic part.** For a commitment that commits to no
element of `𝒳`, acceptance of all `κ` instances forces the coin string to equal
one string `c⃗*`, which depends only on data posted at Setup. -/
theorem amplified_coins_unique [Fact q.Prime] (hq : Nat.card G = q) {k κ n β : ℕ}
    (hn : n ≤ κ * β) (hβ : 2 ^ β ≤ q) {g h : G} {s : Fin k → ZMod q} {c : G × G}
    (hc : ∀ j, ¬ CommitsTo g h c (s j)) (a : Fin κ → Fin k → G × G) :
    ∃ cstar : Fin n → Bool, ∀ coins, AmpAccept g h s c a (challenge κ β coins) →
      coins = cstar := by
  by_cases hex : ∃ coins : Fin n → Bool, AmpAccept g h s c a (challenge κ β coins)
  · obtain ⟨c₀, h₀⟩ := hex
    exact ⟨c₀, fun coins hc' => challenge_injective hn hβ
      (amplified_challenge_unique hq hc a hc' h₀)⟩
  · exact ⟨fun _ => false, fun coins hc' => (hex ⟨coins, hc'⟩).elim⟩

end PDemos
