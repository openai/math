import OAI.Computability.BorderVNP.DiagonalTallyReportDriver
import OAI.Computability.BorderVNP.FiniteReportPermutation

/-! # Preparing scalar report tails at the owned cells of a finite field team

The geometry packet carries the bit-major subtotal address vectors. This
stage fills their chronological bit values in the supplied cell bank, publishes
the real tail lengths and clears the two supplemental-record counters. The
subsequent typed task builder and packet splice use these physical words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open RoutingISA DiagonalResidueRAM DiagonalTallyCellReports

namespace Reports

/-- The six-word owned-cell header table and its physical count come from
the control-row producer. Control words 27 and 22 hold the scalar alphabet
size and common count width. Words 14 and 7 point to the counters and tails. -/
def setup : Code := .block [
  readFrame 2 60 61 92, readControl 0 17, readFrame 1 60 61 90,
  .constant 60 6, .binary .mul 1 1 60, .binary .add 1 0 1,
  readControl 10 27, readControl 11 22, readControl 13 14, readControl 14 7]

/-- Read the owned global cell ordinal, physical supplied base and canonical
length. Advance the row cursor past the remaining three fields. -/
def beginCell : Code := .block [
  .constant 63 1, consume 0 7, consume 0 22, consume 0 4,
  .constant 60 3, .binary .add 0 0 60, .binary .add 22 22 4,
  .binary .mul 18 10 11]

/-- Publish the exact number of supplied scalar bits and both zero counters
for the supplement splice. There are no weighted-unary operands in this stage. -/
def publish : Code := .block [
  .binary .add 60 14 7, .store 60 18,
  .constant 61 2, .binary .mul 60 7 61, .binary .add 60 13 60,
  .constant 61 0, .store 60 61, .binary .add 60 60 63, .store 60 61]

/-- A fresh binary guess at every bit-major scalar position. -/
def cell : Code := .block [beginCell,publish,guessReports]

/-- The corresponding concrete address vectors in the geometry's report
metadata. Each list is the little-endian word for one scalar. -/
def fields (base scalars digits : ℕ) : List (List ℕ) :=
  List.ofFn fun v : Fin scalars => List.ofFn fun i : Fin digits => base + (finProdFinEquiv (i,v)).val

/-- The actual scalar address in a single geometry report word. -/
theorem fields_at (base scalars digits : ℕ) (v : Fin scalars) (i : Fin digits) :
    ((fields base scalars digits)[v.val]'(by simp [fields]))[i.val]'(by simp [fields]) =
      base + i.val*scalars + v.val := by
  simp [fields,Nat.mul_comm]
  omega

end Reports

/-- Parameter-free report preparation over the actual owned six-word rows.
The scalar count and digit width come from the public frame. -/
def prepareReports : Code := .seq Reports.setup (.whileLt 0 1 Reports.cell)

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
