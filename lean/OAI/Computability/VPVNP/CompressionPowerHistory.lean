import OAI.Computability.VPVNP.CompressionPowers
import OAI.Computability.VPVNP.CompressionProcedureHistory

/-!
# Local records throughout a repeated compressor block

The term chosen in each substep determines the network for the next substep.
Append the actual local records along this branch-dependent execution. The
fixed per-block bound on substeps then gives the exponential bounds on local
field lengths and occurrences in Theorem 7.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Procedure

variable {R : Type*} [CommSemiring R] {a k κ C s : ℕ} {μ : ℝ} {P : Procedure R a a k κ μ}

/-- Keep the records supplied by the same procedure on each branch. -/
noncomputable def repeatRecords (B : P.RecordBounds C s) (g : ℕ) :
    (T n : ℕ) → (h : n = T * k + g) → (X : State a n) → (P.repeatExecution g T n h X).Records
  | 0, n, h, X => by
    have hn : n = g := by simpa using h
    subst g
    exact PUnit.unit
  | t + 1, n, h, X =>
    let h₀ : n = k + (t * k + g) := by rw [h, Nat.succ_mul]; omega
    let E := P.run (t * k + g) n h₀ X
    E.bindRecords (fun z => P.repeatExecution g t (t * k + g) rfl (E.finalState z))
      (B.records _ _ h₀ X) fun z => repeatRecords B g t (t * k + g) rfl (E.finalState z)

/-- Bounds for every elementary record remain uniform. A repeated execution
contains at most `s*T` substeps on any branch. -/
theorem repeat_recordBounds (B : P.RecordBounds C s) (g T n : ℕ) (h : n = T * k + g)
    (X : State a n) :
    let E := P.repeatExecution g T n h X
    let data := repeatRecords B g T n h X
    E.Bounded C data ∧ ∀ z, (E.termChain data z).length ≤ s * T := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa using h
    subst g
    exact ⟨trivial, fun _ => Nat.zero_le _⟩
  | succ t ih =>
    let h₀ : n = k + (t * k + g) := by rw [h, Nat.succ_mul]; omega
    let E := P.run (t * k + g) n h₀ X
    let f := fun z : E.Choices => P.repeatExecution g t (t * k + g) rfl (E.finalState z)
    let r := B.records _ _ h₀ X
    let r' := fun z : E.Choices => repeatRecords B g t (t * k + g) rfl (E.finalState z)
    have hb z := ih (t * k + g) rfl (E.finalState z)
    refine ⟨E.bounded_bindRecords f r r' (B.bounded _ _ h₀ X) (fun z => (hb z).1), fun z => ?_⟩
    have hl := E.length_bindRecords_le f r r' (B.length_le _ _ h₀ X) (fun z => (hb z).2) z
    change ((E.bind f).termChain (E.bindRecords f r r') z).length ≤ s * (t + 1)
    exact hl.trans_eq (by rw [Nat.mul_succ, Nat.add_comm])

/-- Every local expansion has bounded occurrence count and peak field width
with one uniform constant `C^s` per whole block. -/
theorem repeat_history_growth (B : P.RecordBounds C s) (hC : 1 ≤ C) (g T n : ℕ)
    (h : n = T * k + g) (X : State a n) (z : (P.repeatExecution g T n h X).Choices) :
    let E := P.repeatExecution g T n h X
    let chain := E.termChain (repeatRecords B g T n h X) z
    (∀ v, chain.occurrences (fun _ => 1) v ≤ (C ^ s) ^ T) ∧
      chain.peak X.maxWireWidth + 1 ≤ (C ^ s) ^ T * (X.maxWireWidth + 1) := by
  obtain ⟨hb, hl⟩ := repeat_recordBounds B g T n h X
  exact (P.repeatExecution g T n h X).localHistory_bounds _ hC hb z (hl z)

/-- Every intermediate field width, individual map degree, and final wire width
obeys the same estimate. Enlarging the coefficient to at least two gives the
constant convention of Theorem 7.1. -/
theorem repeatWithLanes_history_bounds (B : P.RecordBounds C s) (hC : 1 ≤ C) (T n : ℕ)
    (h : T * k ≤ n) (X : State a n) (z : (P.repeatWithLanes T n h X).Choices) :
    let E := P.repeatWithLanes T n h X
    let records := repeatRecords B (n - T * k) T n (Nat.add_sub_of_le h).symm X
    let chain := E.termChain records z
    let C₂ := max 2 (C ^ s)
    (∀ v, chain.occurrences (fun _ => 1) v ≤ C₂ ^ T) ∧
      chain.AllRecordsLe (C₂ ^ T * (X.maxWireWidth + 1)) ∧
      (E.finalState z).maxWireWidth ≤ C₂ ^ T * (X.maxWireWidth + 1) := by
  let eqn := (Nat.add_sub_of_le h).symm
  let E := P.repeatWithLanes T n h X
  let records := repeatRecords B (n - T * k) T n eqn X
  let chain := E.termChain records z
  have hg := repeat_history_growth B hC (n - T * k) T n eqn X z
  have hpow := Nat.pow_le_pow_left (le_max_right 2 (C ^ s)) T
  have hpeak : chain.peak X.maxWireWidth ≤ max 2 (C ^ s) ^ T * (X.maxWireWidth + 1) :=
    (Nat.le_succ _).trans (hg.2.trans (Nat.mul_le_mul_right _ hpow))
  have hb := (repeat_recordBounds B (n - T * k) T n eqn X).1
  exact ⟨fun v => (hg.1 v).trans hpow, chain.allRecordsLe_of_peak hpeak,
    (E.final_maxWireWidth_le_peak records hb le_rfl z).trans hpeak⟩

end Compression.Procedure

end VPVNP
end Computability
end OAI
