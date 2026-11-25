import OAI.Computability.NearSquareRoot.FixedCandidateCRTDispatchCases

/-! # Coverage of the fixed-candidate CRT half-stage directory -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code FixedPoint DigitPacking CRTTable
open private ties_le from OAI.Computability.NearSquareRoot.FixedCandidateCRTCloth

/-- Each target ordinal refers to a distinct physical axis of the box. -/
theorem targetOrder_length_le (d depth : ℕ) : (targetOrder d depth).length ≤ d := by
  have h := (targetAxis_injective d depth).comp (targetRank d depth).injective
  simpa using Fintype.card_le_of_injective _ h

/-- The batch containing the target ordinal is present in the physical directory. -/
theorem targetBatch_lt {u : ℕ} (hcap : 0 < CRTDispatch.Cap (addressBits u)) (s : Switch u)
    (r : TargetIndex (box u).length s.1.val) :
    ((targetRank (box u).length s.1.val).symm r).val / CRTDispatch.Cap (addressBits u) <
      CRTBudget.batches (addressBits u) := by
  exact CRTDispatch.which_lt hcap r

theorem directory_forest {u : ℕ} (h : Directory u) (inv : Bool) (s : Switch u)
    (low : Tally → Tally) :
    Task.forest (fun β => send (CRTDispatch.issue low (seed inv s, tally β)))
      (List.range (CRTBudget.batches (addressBits u))) =
      send (CRTDispatch.directory low (seed inv s)) := by
  rw [← Task.forest_map send (fun β => CRTDispatch.issue low (seed inv s, tally β)),
    Task.forest_send, CRTDispatch.directory_eq, ← CRTDispatch.countAt h inv s]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

theorem packedRows_size {u : ℕ} (hn : 2 ≤ u) (h : Directory u) (s : Switch u)
    (v : Packed u s → Record (addressBits u)) :
    (packedRows h s v).count ≤ 75000 * (u + 1) := by
  let r : Array u := v ∘ packing h s
  apply (ties_le (records r)).trans
  have bound := framed_size hn r
  change size (tally u, records r) ≤ _ at bound
  simp only [size_prod] at bound
  omega

end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
