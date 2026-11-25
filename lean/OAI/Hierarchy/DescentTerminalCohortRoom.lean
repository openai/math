import OAI.Hierarchy.DescentTerminalCohortRate
import OAI.Hierarchy.DescentTerminalIssuedScale
import OAI.Hierarchy.DescentTerminalMaskAllocation

namespace OAI
/-! # The padded terminal instruction tables at the actual calendar width -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentPrimitivePalette
open DescentTerminalVertexFields Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec)
variable (q p drift : ℕ)
local notation "K" => NativeBranch.privateSlotCapacity G S drift
local notation "A" => max 8 (2^S.capGain)
local notation "palette" => colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "tags" => DescentBundleTagKeys.capacity palette A K p drift
local notation "nodes" => S.epochPower^S.localTokenExponent
local notation "table" => cohortSize (q:=q) (t:=tags) (H:=K) (N:=nodes) («A»:=K) (w:=p)
  (groups:=S.groupCount S.length) (blocks:=S.radix)

def terminalCohortCells :=
  MaskAllocation.marks (channelSize (q:=q) (t:=tags) (H:=K) (N:=nodes) («A»:=K) (w:=p)
    (groups:=S.groupCount S.length) (blocks:=S.radix))+table

theorem terminalCohortCells_le :
    terminalCohortCells G S op q p drift≤2*terminalCohortCapacity G S op q p drift+9*S.radix := by
  simpa only [terminalCohortCells,terminalCohortCapacity,MaskAllocation.marks,channels,Nat.mul_comm 9]
    using (MaskAllocation.bill (q:=q) (t:=tags) (H:=K) (N:=nodes) («A»:=K) (p:=p)
      (groups:=S.groupCount S.length) (blocks:=S.radix))

end
end Hierarchy.DescentSixParty

end OAI
