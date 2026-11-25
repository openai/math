import OAI.Computability.BorderVNP.CrossingRankFrame

/-!
# Unique Boolean encodings of admissible intermediate states

Guessing the occupation bits and checking the energy introduces exactly one witness
per state. The rank outputs of the same circuit use the numbering of the fused cut,
so checking the final rank fixes that state without an additional multiplicity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.StateIndex

open Lemmata.FockCircuits Lemmata.FockCircuits.Families

/-- Membership in the selected subset is precisely the bit at the corresponding mode. -/
theorem mem_occupancy {E : ℕ} (x : Fin E → Bool) (i : Fin E) :
    i.val ∈ occupancy x ↔ x i = true := by
  simp [occupancy, Finset.mem_map, ← Fin.ext_iff]

private theorem occupancy_indicator {E : ℕ} (S : EnergyState E) :
    occupancy (fun i : Fin E => decide (i.val ∈ S.val)) = S.val := by
  ext j
  by_cases hj : j < E
  · simpa only [decide_eq_true_eq] using
      mem_occupancy (fun i : Fin E => decide (i.val ∈ S.val)) ⟨j,hj⟩
  · have hs := Finset.mem_powerset.mp
        (CrossingCircuit.cutoffEmbedding (E := E) le_rfl S).property
    have hout : j ∉ S.val := fun hin => hj (Finset.mem_range.mp (hs hin))
    simp [occupancy, Finset.mem_map, hout]
    intro i _ hi
    exact hj (hi ▸ i.isLt)

/-- Masks surviving the Boolean verifier. -/
abbrev ValidMask (E : ℕ) := {x : Fin E → Bool // (validFrame E).eval x () = true}

/-- A checked occupation mask and an admissible state are interchangeable, including
at energy zero. No unused or noncanonical mask represents a second copy of a state. -/
noncomputable def validMaskEquiv (E : ℕ) : ValidMask E ≃ EnergyState E where
  toFun x := ⟨occupancy x.val, mem_fullCutoff.mpr
    (by simpa only [validFrame_eval, decide_eq_true_eq] using x.property)⟩
  invFun S := ⟨fun i => decide (i.val ∈ S.val), by
    rw [validFrame_eval, decide_eq_true_eq]
    rw [occupancy_indicator]; exact mem_fullCutoff.mp S.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp [mem_occupancy]
  right_inv S := Subtype.ext (occupancy_indicator S)

/-- Rank bits of every surviving guess use the canonical occupation-state ordinal. -/
theorem rankFrame_validMask (E : ℕ) (x : ValidMask E) (j : Fin (E+1)) :
    (rankFrame E).eval x.val j = (energyStateEquiv E (validMaskEquiv E x)).val.testBit j.val :=
  rankFrame_eval E x.val j

end Crossing.StateIndex

end BorderVNP
end Computability
end OAI
