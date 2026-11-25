import OAI.Hierarchy.DescentNamedPostEarlyPreflight
import OAI.Hierarchy.DescentOriginalPreflightPrice

namespace OAI
/-! # Charging the terminal portion of the authentic calendar once in the emitted host -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentMixedRouter Catalyst DescentInitialHost DescentExteriorReplay
open DescentTerminalPreflightSpace DescentTerminalFixedSlices DescentTerminalPrimitiveArena
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Routing CallPool
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 4000
set_option maxHeartbeats 650000

variable {F:Type} [Field F] {cp ar:ℕ} (X:Approximation F cp ar) (G:PoweredGadget F) (S:AtomSchedule)
  {k tail:ℕ} (baseGroups:S.baseGroups=2^tail) (radix:S.radix=2^k)
  (g p q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ)
local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "ports" => Fintype.card (Port ar X.width)
variable (j r t base compact:ℕ) (tag:ℕ→Bool) (rotation:ℕ→ℕ)
  (phase:Phase F) (snapshots:Snapshots k)
local notation "C" => replayCalendar X S k tail j r snapshots
local notation "early_" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t ports
local notation "slices_" => phase.stop early_
local notation "rom_" => (C).packetEnd slices_
local notation "shelf" => (spec).scanPages rom_ q
local notation "census_" => (shelf).stop
local notation "matrix" => DescentExteriorMatrixUpdate.Calendar.stop S k tail base+S.length
local notation "bks" => (spec).scalar.blocks
local notation "H" => (spec).scalar.shops
local notation "hw_" => phase.output.receiver
variable (blocks:2^k=phase.output.receiver.blocks) (shops:S.hostSize S.length=phase.output.receiver.hosts) (roleBase:ℕ)
  (peer:Bank) (paid actor:Fin (2^k)→Bank) (signed:Fin (2^k)→Fin (2*((capCalendar G.b S.rounds g S.height).prod*256))→Bank)
local notation "ptr" => fun (f:Fin 4) (j:Fin phase.output.argumentSlots) (b:Fin bks) =>
  phase.output.terminalPointers phase.dateBase f j (b.cast blocks)
variable {w:ℕ} (cohortRoom :
  let book := replayCalendar X S k tail j r snapshots
  let endAddress := DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))
  let layout := preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
  book.stop (layout.scanPages (book.packetEnd (phase.stop endAddress)) q).stop < 2^w)
local notation "fixed_" => fixedPreflight X G S baseGroups radix g p q drift op headerRows paidRows census_ rom_ w
  peer ((C).homes slices_) paid actor signed matrix roleBase (phase.banks early_) ptr
local notation "fixedImage" => fixedPreflightMemory X G S baseGroups radix g p q drift op headerRows paidRows census_ rom_ w
  peer ((C).homes slices_) paid actor signed matrix roleBase (phase.banks early_) ptr
local notation "fixedFee" => fixedPreflightClocks X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows census_ rom_
  peer ((C).homes slices_) paid actor signed matrix ptr

/-- Removing the early reel from its prepaid bracket leaves precisely the terminal middle
that follows the history count reel in the fixed host. -/
theorem post_early_invoice_identity (countCode lateCode : Procedure w) (countCost lateCost : ℕ) :
    let early:=DescentExteriorMatrixUpdate.Calendar.earlyProgram S k tail base tag rotation j r t ports compact w
    let earlyTicks:=DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j r t ports
    let post:=postEarlyPreflight (w:=w) X G S baseGroups radix g p q drift op headerRows paidRows j r t base phase
      snapshots blocks roleBase peer paid actor signed cohortRoom
    let price:=postEarlyPreflightClocks (w:=w) X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows j r t
      base phase snapshots blocks peer paid actor signed cohortRoom
    let prior:=originalPreflight (w:=w) X G S baseGroups radix g p q drift op headerRows paidRows j r t base compact
      tag rotation phase snapshots blocks roleBase peer paid actor signed cohortRoom
    let cost:=originalPreflightClocks (w:=w) X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows j r t
      base phase snapshots blocks peer paid actor signed cohortRoom
    countCost+earlyTicks+price+lateCost+
        7*DescentStaticWordColumn.names ((((countCode.seq early).seq post).seq lateCode))=
      countCost+cost+lateCost+7*DescentStaticWordColumn.names ((countCode.seq prior).seq lateCode) :=by
  dsimp only
  simp only [postEarlyPreflightClocks,originalPreflightClocks,postEarlyPreflight,originalPreflight,
    DescentStaticWordColumn.names_seq]
  omega

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
