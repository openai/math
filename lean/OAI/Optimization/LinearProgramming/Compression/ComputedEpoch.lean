import OAI.Optimization.LinearProgramming.Compression.CommitProgram
import OAI.Optimization.LinearProgramming.Compression.AdaptiveRequests
import OAI.Optimization.LinearProgramming.Compression.CommitCap

/-! Executing the generator commitment from bounded affine sign queries. Reindexing the
present generator list avoids any enumeration of the universe of minors. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

def epochFormBudget (d width H : ℕ) := (d+1)*fiberProjectionBudget d width H+1

theorem validEpochCommit_of_encoded_signs {κ : Type*} [Fintype κ] {d : ℕ}
    (e : κ ≃ Fin d) (x : κ → ℝ) (γ : Fin d → ℚ) (width H : ℕ)
    (hs : ∀ i, (γ i).num.natAbs.size ≤ affineCommitWidth d (epochFormBudget d width H) ∧
      (γ i).den.size ≤ affineCommitWidth d (epochFormBudget d width H))
    (ht : RequestSigns (fun i => x (e.symm i)) (fun i => (γ i : ℝ)) (epochFormBudget d width H)) :
    ValidEpochCommit x width H (fun j => γ (e j)) := by
  have hd : Fintype.card κ = d := (Fintype.card_congr e).trans (Fintype.card_fin _)
  constructor
  · intro i
    rw [hd]
    exact ⟨computed_lt_fiberCommitCap (hs (e i)).1, computed_lt_fiberCommitCap (hs (e i)).2⟩
  · rw [hd]
    exact projection_tests_of_requestSigns e x γ (fiberProjectionBudget d width H) ht

/-- The searchable, deterministic reference variant of the commitment stage. -/
def computedEpochCommit {κ : Type*} {d : ℕ} (e : κ ≃ Fin d)
    (width H : ℕ) (negative : (Fin d → ℤ) → ℤ → Bool) (j : κ) : ℚ :=
  computeCommit (epochFormBudget d width H) negative (e j)

theorem computedEpochCommit_valid {κ : Type*} [Fintype κ] {d : ℕ} (e : κ ≃ Fin d)
    (x : κ → ℝ) (width H : ℕ) (negative : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ a c, negative a c = true ↔ requestForm (fun i => x (e.symm i)) a + c < 0) :
    ValidEpochCommit x width H (computedEpochCommit e width H negative) := by
  have hM : 0 < epochFormBudget d width H := Nat.zero_lt_succ _
  obtain ⟨hs,_,ht⟩ := computeCommit_spec (fun i => x (e.symm i)) hM negative ho
  exact validEpochCommit_of_encoded_signs e x _ width H hs ht

/-- A different implementation of the rational approximation step may be substituted
without changing the committed-coordinate guarantee. -/
def computedEpochCommitWith {κ : Type*} {d : ℕ} (e : κ ≃ Fin d)
    (width H : ℕ) (select : (Fin (d+1) → ℚ) → ℕ × (Fin (d+1) → ℤ))
    (negative : (Fin d → ℤ) → ℤ → Bool) (j : κ) : ℚ :=
  computeCommitWith (epochFormBudget d width H) select negative (e j)

theorem computedEpochCommitWith_valid {κ : Type*} [Fintype κ] {d : ℕ} (e : κ ≃ Fin d)
    (x : κ → ℝ) (width H : ℕ) (select : (Fin (d+1) → ℚ) → ℕ × (Fin (d+1) → ℤ))
    (hsel : ∀ v, 0 < (select v).1 ∧
      (select v).1 ≤ Lattice.searchDenominator (d+1) (epochFormBudget d width H)^((d+1)+1) ∧
      ∀ i, |((select v).1 : ℚ)*v i - (select v).2 i| ≤
        1 / (8*((d+1 : ℕ) : ℚ)*epochFormBudget d width H))
    (negative : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ a c, negative a c = true ↔ requestForm (fun i => x (e.symm i)) a + c < 0) :
    ValidEpochCommit x width H (computedEpochCommitWith e width H select negative) := by
  have hM : 0 < epochFormBudget d width H := Nat.zero_lt_succ _
  obtain ⟨hs,_,ht⟩ := computeCommitWith_spec (fun i => x (e.symm i)) hM select hsel negative ho
  exact validEpochCommit_of_encoded_signs e x _ width H hs ht

end Compression
end LinearProgramming
end Optimization
end OAI
