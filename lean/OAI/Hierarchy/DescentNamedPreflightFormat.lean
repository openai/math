import OAI.Hierarchy.DescentCensusPrecision
import OAI.Hierarchy.DescentTerminalPreflightAges
import OAI.Hierarchy.DescentTerminalIssuedScale
import OAI.Hierarchy.DescentTerminalPointerWordRoom

namespace OAI
/-! # Public register dimensions printed by the named terminal prologue -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale
open DescentTerminalPointerDigits
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F) (S:AtomSchedule)

/-- `raw` is the earlier page's pointer source word; `span` is the full vertex-field
width including its occupancy marker. Each input is shared through all resident groups. -/
def geometryFormat (k g p tail q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ) : PreflightFormat :=
  let groups:=S.groupCount S.length
  let V:=groups*2^k
  let A:=NativeBranch.localLimit G S
  let W:=NativeBranch.binLimit (k:=k) S
  let used:=S.epochPower^S.localTokenExponent
  let maxArgs:=NativeBranch.privateSlotCapacity G S drift
  let cb:=8+S.capGain*S.length
  let frozen:=k*S.length
  let cap:=(capCalendar G.b S.rounds g S.height).prod*256
  let side:=DescentSignedCableCodec.width 3 cap
  let raw:=DescentOperandWidth.recordBits G S k tail drift 3 p
  let extent:=actualSpan G S op q p drift
  let d:=inputWidth groups used (S.groupWidth k tail 0+k) frozen (2^cb)
    (Nat.clog 2 (used+1)) (Nat.clog 2 (maxArgs+1)) raw side
  let bookBits:=2+groups*max (max 1 (Nat.clog 2 (q+1))) side
  {columns:=columns cap used maxArgs, pointerBits:=d, countBits:=groups*extent,
   paidLanes:=groups,actorLanes:=groups,paidBits:=S.censusBits p,externalBits:=cb+1,
   vertices:=V,«arguments»:=A,binSize:=W,pageBits:=max 1 (V*extent),
   cableCellBits:=2+groups*side,printBits:=bookBits,headerRows:=headerRows,paidRows:=paidRows}

variable {cp P:ℕ} (X:Catalyst.Approximation F cp P)
variable (k g p tail q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ)
local notation "choices" => geometryFormat G S k g p tail q drift op headerRows paidRows
local notation "spec" => preflightSpec X G S k g p tail choices
local notation "V" => S.groupCount S.length*2^k

theorem geometry_book :
    (spec).vertices=V ∧ (spec).arguments=NativeBranch.localLimit G S ∧ (spec).binSize=NativeBranch.binLimit (k:=k) S ∧
    (spec).pageBits=max 1 (V*actualSpan G S op q p drift) := ⟨rfl,rfl,rfl,rfl⟩
theorem geometry_paid : (spec).paidSize=paidRows+headerRows := rfl
theorem geometry_columns : (spec).scalar.columns=columns (spec).cap (S.epochPower^S.localTokenExponent)
    (NativeBranch.privateSlotCapacity G S drift) := rfl
theorem geometry_count : (spec).scalar.countBits=S.groupCount S.length*actualSpan G S op q p drift := rfl
theorem geometry_positive : 0<(spec).scalar.columns := by rw [geometry_columns];unfold columns;omega

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
