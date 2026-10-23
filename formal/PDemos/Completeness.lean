import PDemos.Sigma

/-!
# Completeness of the Σ-protocols (`background.tex`, Section 2)

The honest provers of the paper, and the proof that their transcripts accept for
*every* challenge.

* **Chaum–Pedersen.** With witness `r` for `u = (g^r, h^r)`, the prover sends
  `a = (g^ρ, h^ρ)` and answers `z = ρ + e r` (`cp_complete`).
* **Simulated branch.** For any `e, z`, the first message
  `(g^z u₁^{-e}, h^z u₂^{-e})` accepts with challenge `e` and response `z`
  (`cp_sim_accept`). This needs no witness.
* **CDS OR-proof.** For the true index `t`, branch `t` is an honest
  Chaum–Pedersen proof and every other branch is simulated with prover-chosen
  `(e_j, z_j)`. On challenge `e`, the prover sets `e_t = e - ∑_{j ≠ t} e_j`
  and `z_t = ρ + e_t r` (`cds_complete`, `amp_complete`).
-/

namespace PDemos

open Finset

variable {G : Type*} [CommGroup G] {q : ℕ}

/-! ### Chaum–Pedersen -/

/-- Honest Chaum–Pedersen first message `(g^ρ, h^ρ)`. -/
def cpFirst (g h : G) (ρ : ZMod q) : G × G := (g ^ₘ ρ, h ^ₘ ρ)

/-- Honest Chaum–Pedersen response `z = ρ + e r`. -/
def cpResp (ρ r e : ZMod q) : ZMod q := ρ + e * r

/-- Simulated first message for challenge `e` and response `z`. -/
def cpSim (g h : G) (u : G × G) (e z : ZMod q) : G × G :=
  (g ^ₘ z * (u.1 ^ₘ e)⁻¹, h ^ₘ z * (u.2 ^ₘ e)⁻¹)


/-- A simulated transcript always accepts. -/
theorem cp_sim_accept (g h : G) (u : G × G) (e z : ZMod q) :
    CPAccept g h u (cpSim g h u e z) e z := by
  simp [CPAccept, cpSim]

section
variable [Fact q.Prime] (hq : Nat.card G = q)
include hq

/-- **Completeness of Chaum–Pedersen.** With witness `r` for `u = (g^r, h^r)`, the
honest transcript accepts for every challenge. -/
theorem cp_complete (g h : G) (r ρ e : ZMod q) :
    CPAccept g h (g ^ₘ r, h ^ₘ r) (cpFirst g h ρ) e (cpResp ρ r e) := by
  simp [CPAccept, cpFirst, cpResp, zpowq_add hq, ← zpowq_mul hq, mul_comm r e]

omit [Fact q.Prime] hq in
/-- The statement for "`Com(v; r)` commits to `v`" is `(g^r, h^r)`. -/
lemma cpStatement_com (g h : G) (v r : ZMod q) :
    cpStatement g (Com g h v r) v = (g ^ₘ r, h ^ₘ r) := by
  simp [cpStatement, Com]

end

/-! ### CDS OR-proof -/

section CDS

variable {k : ℕ}

/-- Honest CDS first messages: branch `t` is honest, every other branch simulated
with the prover's `(eSim j, zSim j)`. -/
def cdsFirst (g h : G) (s : Fin k → ZMod q) (c : G × G) (t : Fin k) (ρ : ZMod q)
    (eSim zSim : Fin k → ZMod q) : Fin k → G × G :=
  fun j => if j = t then cpFirst g h ρ else cpSim g h (cpStatement g c (s j)) (eSim j) (zSim j)

/-- The challenge left for the true branch. -/
def cdsTrueChal {k : ℕ} (t : Fin k) (eSim : Fin k → ZMod q) (e : ZMod q) : ZMod q :=
  e - ∑ j ∈ univ.erase t, eSim j

/-- Honest CDS responses on challenge `e`. -/
def cdsResp (t : Fin k) (r ρ : ZMod q) (eSim zSim : Fin k → ZMod q) (e : ZMod q) :
    Fin k → ZMod q × ZMod q :=
  fun j => if j = t then (cdsTrueChal t eSim e, cpResp ρ r (cdsTrueChal t eSim e))
    else (eSim j, zSim j)

variable [Fact q.Prime] (hq : Nat.card G = q)
include hq

/-- **Completeness of the CDS OR-proof.** If `c = Com(s t; r)`, the honest prover's
transcript accepts for every challenge `e`. -/
theorem cds_complete (g h : G) (s : Fin k → ZMod q) (t : Fin k) (r ρ : ZMod q)
    (eSim zSim : Fin k → ZMod q) (e : ZMod q) :
    CDSAccept g h s (Com g h (s t) r) (cdsFirst g h s (Com g h (s t) r) t ρ eSim zSim) e
      (cdsResp t r ρ eSim zSim e) := by
  refine ⟨?_, fun j => ?_⟩
  · rw [← add_sum_erase _ _ (mem_univ t),
      sum_congr rfl fun j hj => by rw [cdsResp, ite_eq_right (ne_of_mem_erase hj)]]
    simp [cdsResp, cdsTrueChal]
  · by_cases hj : j = t
    · subst hj
      simp only [cdsFirst, cdsResp, ite_true]
      rw [cpStatement_com]
      exact cp_complete hq g h r ρ _
    · simp only [cdsFirst, cdsResp, ite_eq_right hj]
      exact cp_sim_accept g h _ _ _

/-- **Completeness of the amplified proof.** With one independent set of prover
randomness per instance, all `κ` instances accept for every challenge vector. -/
theorem amp_complete {κ : ℕ} (g h : G) (s : Fin k → ZMod q) (t : Fin k) (r : ZMod q)
    (ρ : Fin κ → ZMod q) (eSim zSim : Fin κ → Fin k → ZMod q) (e : Fin κ → ZMod q) :
    AmpAccept g h s (Com g h (s t) r)
      (fun i => cdsFirst g h s (Com g h (s t) r) t (ρ i) (eSim i) (zSim i)) e :=
  fun i => ⟨_, cds_complete hq g h s t r (ρ i) (eSim i) (zSim i) (e i)⟩

end CDS

end PDemos
