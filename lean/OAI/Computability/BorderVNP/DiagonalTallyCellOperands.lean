import OAI.Computability.BorderVNP.DiagonalTallyMaterializeLoop
import OAI.Computability.BorderVNP.DiagonalTallyRAMRecords
import OAI.Computability.BorderVNP.CellSparseSemantics

/-! # Connecting actual cell reports to native tally operands

The finite public directory stores addresses of reported little-endian fields. A passing
private call verifies their contents against the actual table observations. Its outer
reader constructs a weighted use record from a delivered coordinate and binary place,
and a count record per fixed gadget position.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyMaterialize

open CellSparse DiagonalTallyGather

/-- A unary occurrence names its parameter and binary place in the delivered local
record, and its one-bit use flag in the returned assignment bank. -/
def unaryOperand (paramAddr placeAddr refAddr bitAddr i j : ℕ) (b : Bool) : Operand :=
  ⟨0,paramAddr,i,refAddr,[(bitAddr,b)],placeAddr,j⟩

/-- The real branch flag contributes its binary place exactly on selection. -/
theorem unaryOperand_pair (paramAddr placeAddr refAddr bitAddr i j : ℕ) (b : Bool) :
    (unaryOperand paramAddr placeAddr refAddr bitAddr i j b).pair =
      (i,if b then 2^j else 0) := by
  cases b <;> simp [unaryOperand,Operand.pair,readDigits]

/-- Read one cell's count field, retaining every supplied bit address and reversing
only the public traversal order for the most-significant-first native accumulator. -/
def countOperand (h zeroAddr refAddr : ℕ) (D : Directory) (bank : ℕ → Bool)
    (g : Fin D.reportedCounts.length) : Operand :=
  ⟨h+g.val,zeroAddr,0,refAddr,((D.reportedCounts[g]).map (fun a => (a,bank a))).reverse,zeroAddr,0⟩

private theorem report_value (bank : ℕ → Bool) (bits : List ℕ) :
    VPVNP.TapeWord.value (bits.map bank) = CellSparse.word bank bits := by
  induction bits with
  | nil => rfl
  | cons a xs ih =>
    cases h : bank a <;> simp [CellSparse.word,VPVNP.TapeWord.value,ih,h]

/-- The native pair computed for a checked count field stores exactly the number of
observed occurrences of that gadget ID, independently of its scalar value. -/
theorem countOperand_pair (h zeroAddr refAddr : ℕ) (D : Directory) (bank : ℕ → Bool)
    (g : Fin D.reportedCounts.length) (obs : List (Bool × Option ℕ))
    (checked : countsValid bank D.reportedCounts obs) :
    (countOperand h zeroAddr refAddr D bank g).pair =
      (h+g.val,(obs.filterMap Prod.snd).count g.val) := by
  rw [Operand.pair,countOperand]
  simp only [Nat.add_zero,List.map_reverse,List.map_map,Function.comp_def,pow_zero,Nat.mul_one]
  rw [readDigits_reverse, report_value,← checked.2 g]

/-- When the mathematical private cell generator passes, its count operand reads
exactly the ID frequency, with the required observation list produced by that generator. -/
theorem countOperands_of_passing (h zeroAddr refAddr : ℕ) (D : Directory) (bank : ℕ → Bool)
    (passing : D.weight bank ≠ 0) : ∃ obs, D.observations bank = some obs ∧
      ∀ g, (countOperand h zeroAddr refAddr D bank g).pair =
        (h+g.val,(obs.filterMap Prod.snd).count g.val) := by
  classical
  unfold Directory.weight at passing
  cases ho : D.observations bank with
  | none => simp [ho] at passing
  | some obs =>
    have hv : (∀ r ∈ D.records, r.Valid D.boxes bank) ∧ countsValid bank D.reportedCounts obs := by
      by_contra hn
      simp [ho,hn] at passing
    exact ⟨obs,rfl,fun g => countOperand_pair h zeroAddr refAddr D bank g obs hv.2⟩

/-- A chosen cube table position is named by its runtime output word and contributes
one occurrence. The one-bit operand points to a literal true word. -/
def packetOperand (h idAddr zeroAddr refAddr trueAddr id : ℕ) : Operand :=
  ⟨h,idAddr,id,refAddr,[(trueAddr,true)],zeroAddr,0⟩

/-- Each selected table position has its own exact count coordinate. -/
theorem packetOperand_pair (h idAddr zeroAddr refAddr trueAddr id : ℕ) :
    (packetOperand h idAddr zeroAddr refAddr trueAddr id).pair = (h+id,1) := by
  simp [packetOperand,Operand.pair,readDigits]

end DiagonalTallyMaterialize

end BorderVNP
end Computability
end OAI
