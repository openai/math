import OAI.Hierarchy.DescentTerminalEmitterSpace
import OAI.Hierarchy.DescentDatedTerminalArea
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # End of the actual emitter columns, ten phases and final five checked chip scans -/
namespace Hierarchy.DescentTerminalEmitter.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM DescentDatedAddressBook
noncomputable section

def chipStart (base : ℕ) (c : Columns) (s : Shape) (i f flight : ℕ) :=
  Allocation.endAt s i f (flightEnd base c flight)
def chip (base : ℕ) (c : Columns) (s : Shape) (i f flight : ℕ) :=
  DescentTerminalChipRuntime.Dated.placed (chipStart base c s i f flight) s.rows
def endAddress (base : ℕ) (c : Columns) (s : Shape) (i f flight : ℕ) :=
  (chip base c s i f flight).keys+s.pool

theorem end_at (base : ℕ) (c : Columns) (s : Shape) (i f flight : ℕ) :
    endAddress base c s i f flight=base+endAddress 0 c s i f flight := by
  simp only [endAddress,chip,chipStart,DescentTerminalChipRuntime.Dated.placed,
    DescentTerminalChipRuntime.Layout.keys,DescentTerminalChipRuntime.Layout.width,Allocation.endAt,
    flightEnd,shelfEnd,Nat.zero_add,Nat.add_assoc]

theorem end_le (base : ℕ) (c : Columns) (s : Shape) (i f flight : ℕ) :
    endAddress base c s i f flight≤base+2*(∑j,need (c j))+43+flight+
      60*(s.rows+s.pool+s.leaves+i+f+1)+8*s.rows+6+s.pool := by
  have paid:=price base c s i f flight
  have key:=DescentTerminalChipRuntime.Dated.terminal_end (chipStart base c s i f flight) s.rows s.pool
  have size:=DescentTerminalChipRuntime.Dated.words_le s.rows s.pool
  change chipStart base c s i f flight≤_ at paid
  change endAddress base c s i f flight=_ at key
  omega

theorem chip_room {base i f flight w : ℕ} (c : Columns) (s : Shape) (src : DescentTerminalChipRuntime.Banks)
    (fit : endAddress base c s i f flight<2^w)
    (dense : (DescentTerminalChipRuntime.dense src).Fits w (chipStart base c s i f flight))
    (route : (DescentTerminalChipRuntime.route src).Fits w (chipStart base c s i f flight))
    (key : (DescentTerminalChipRuntime.key src).Fits w (chipStart base c s i f flight))
    (x : src.xWords.Fits w (chipStart base c s i f flight))
    (y : src.ySlices.Fits w (chipStart base c s i f flight))
    (xRows : s.rows≤ src.xWords.size) (yRows : s.rows≤ src.ySlices.size) :
    DescentTerminalChipRuntime.Room (chip base c s i f flight) src w s.rows s.pool := by
  apply DescentTerminalChipRuntime.Dated.room _ _ _ _ src dense route key x y xRows yRows
  rw [←DescentTerminalChipRuntime.Dated.terminal_end]
  exact fit

end
end Hierarchy.DescentTerminalEmitter.Compact

end OAI
