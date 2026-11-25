import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderSeed
import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepFragments
import OAI.Computability.BorderVNP.RoutingISASignedReaderArena

/-! # Addresses of all original signed header reads in the physical startup arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM TeamContraction TeamContraction.JointHeader TeamContraction.ProcessorSlots
open DiagonalTallyRAM DiagonalTallyAllocation DiagonalResidueRAM

variable {reserve axes groups cap width w : ℕ} (l : Layout) (A : StartupArena)
variable (p : PositiveFields reserve axes groups cap l.cube.teams l.dim width)

/-- The subtotal array begins after the positive bit, padded profile and the
actual upper-triangle spelling of the declaration. -/
def rawAddress (A : StartupArena) (reserve axes groups cap : ℕ) : ℕ :=
  A.broadcastBase+1+reserve+Cube.DeclarationBits.length axes groups cap

local notation "raw" => rawAddress A reserve axes groups cap

/-- The last subtotal bit is strictly before the first private pin position.
The sparse signed program may therefore replay the same bits through every
choice of pins and every later cell preparation. -/
theorem rawAddress_room (exactWidth : A.header=PositiveFields.width reserve axes groups cap l.cube.teams l.dim width) :
    A.frame+112 ≤ raw ∧ raw+l.cube.teams*l.dim*width=A.ibase ∧ A.ibase ≤ A.next := by
  refine ⟨?_,?_,?_⟩
  · unfold rawAddress StartupArena.broadcastBase StartupArena.dense; omega
  · rw [StartupArena.ibase,exactWidth]
    unfold rawAddress PositiveFields.width; omega
  · unfold StartupArena.next StartupArena.hbase; omega

/-- The chosen fixed address and physical word ceiling suffice for every numerical
room condition of the genuine parsed-claim suffix, for all legal operand counts. -/
theorem finishSeedRoom {u v k : ℕ}
    (exactWidth : A.header=PositiveFields.width reserve axes groups cap l.cube.teams l.dim width)
    (placement : A.next ≤ l.cube.header.header) (endFit : l.endAddress w u v k<2^w) :
    A.frame+101<l.after.start ∧ A.frame+45 ≤ raw ∧ raw+l.cube.teams*l.dim*width ≤ l.after.start ∧
    l.after.localBase+l.dim+l.cube.teams*l.dim+l.dim+l.dim+1+l.dim*w<2^w ∧
    l.dim<2^w ∧ l.after.localBase<2^w ∧ raw<2^w := by
  obtain ⟨low,last,pins⟩ := rawAddress_room l A exactWidth
  have high := (l.reader_bounds A 0 A.frame 0 0 placement).2.2.2.2.2.2.2.2.2.2.2.2
  have lower : l.after.start ≤ l.after.localBase := by
    have fresh : l.after.start ≤ l.after.fresh := by rw [l.after.footprint]; omega
    exact fresh.trans (Nat.le_add_right ..)
  unfold Layout.endAddress Layout.entry gateBase Layout.valuation Layout.tallyBits at endFit
  omega

/-- All header-seed reads are on the low side of every later public workspace. -/
theorem seedRead_before_pins {x : ℕ}
    (exactWidth : A.header=PositiveFields.width reserve axes groups cap l.cube.teams l.dim width)
    (read : headerSeedRead A.frame raw (l.cube.teams*l.dim*width) x) : x<A.ibase := by
  obtain ⟨low,last,_⟩ := rawAddress_room l A exactWidth
  exact headerSeedRead_below read (by omega) last.le

/-- The private pin choice affects only the row and column banks after the
subtotal bit interval, including the saved pin position for every physical lane. -/
theorem HeaderSeed.afterPins {pub : Arg → Word w} {team : ℕ} {m : Memory w} {pins : Pins.Layout}
    (chosen : ℕ → Bool) (seed : HeaderSeed l p pub raw team m)
    (frame : (pub 0).val=A.frame) (ibase : pins.ibase=A.ibase) (hbase : pins.hbase=A.hbase)
    (exactWidth : A.header=PositiveFields.width reserve axes groups cap l.cube.teams l.dim width) :
    HeaderSeed l p pub raw team (Pins.preparedMemory pins chosen m pins.count) := by
  apply seed.transfer
  intro x read
  have before := seedRead_before_pins l A exactWidth (frame ▸ read)
  apply Pins.preparedMemory_other
  · intro i _; rw [ibase]; omega
  · intro i _ _; rw [hbase]; unfold StartupArena.hbase; omega

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
