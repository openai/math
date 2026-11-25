import OAI.ThreeFlat.Diagonal.TickTotalBudget
import OAI.ThreeFlat.RAM.TickAdmittedTransfer

namespace OAI
/-! # Fuel of the actual mounted native procedure at the dyadic age -/

namespace ThreeFlat.Diagonal.TickTotalBudget

open RAM RAM.BitLayout RAM.Contraction RAM.TickActiveROM
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] {w p H J : ℕ} {B : Layout} {clock : TickChronology.Clock}
variable {fit : Fits (TickWeightedBank.shape F p H J) w}

/-- Specialize the budget variables to instruction operands and the actual
array sizes, including the concrete list accessed on scan ticks. -/
def charges (x : CellInput B clock fit) (teamBits tickBits nav prep replay selected suffix : ℕ) : Charges where
  tickBits := tickBits
  teamBits := teamBits
  navigation := nav
  buckets := x.intervals.length
  replay := replay
  selected := selected
  prepare := prep
  suffix := suffix
  hidden := H
  cells := J
  entries := x.lib.count
  field := Fintype.card F

theorem charges_fuel (x : CellInput B clock fit) (nt ns nav prep replay selected suffix : ℕ) :
    (charges x nt ns nav prep replay selected suffix).fuel B.bits =
      (159+6*(nt+ns)+25+18*B.bits)+(1470+nav+21+x.tail prep) := by
  unfold charges Charges.fuel Charges.fieldCost CellInput.tail
  rw [Nat.add_comm ns nt]

/-- Full native tick duration admissible in the fixed universal trace.
The coefficient depends only on the cardinality of the field, the compact
table library length and the global polynomial majorant. -/
theorem mounted_half {u e C : ℕ} (x : CellInput B clock fit) {nt ns nav prep replay selected suffix : ℕ}
    (bits : B.bits=chunk u) (age : 8 ≤ u)
    (constant : 8*coefficient (charges x nt ns nav prep replay selected suffix) C ≤ u)
    (exponent : e+1+TraceVolume.cm ≤ u)
    (bounds : Bounds (charges x nt ns nav prep replay selected suffix)
      (TraceVolume.cap u) (replayBound u e C)) :
    (159+6*(nt+ns)+25+18*B.bits)+(1470+nav+21+x.tail prep) ≤ TraceVolume.cap u/2 := by
  rw [← charges_fuel x nt ns nav prep replay selected suffix,bits]
  exact paper_half age constant exponent bounds


end ThreeFlat.Diagonal.TickTotalBudget

end OAI
