import OAI.Hierarchy.DescentDatedRegisteredPages
import OAI.Hierarchy.DescentResetIssuedRange
import OAI.Hierarchy.DescentScheduledResetChart

namespace OAI
/-! # Equality of the final dated operand register and the reset scatter's packed field register -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentDatedPriorOperand DescentDatedAddressBook
open DescentLocalArchiveOrder DescentKernelHistory Computability.VPVNP.BurstRAM ProtocolRAM
noncomputable section
open scoped Classical

theorem fromRAM_layout {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {B : BitDescription W} {w : ℕ} (a : PriorResetArchive) (l l' : Layout) (same : l=l')
    (width : ℕ) (m : Memory w) (pos : 0<l.lanes) (block : NodeOrder.All B→Fin l.blocks)
    (host : NodeOrder.All B→Fin l.hosts) (groupOf : NodeOrder.All B→Fin l.groups)
    (number : NodeOrder.All B→Fin l.nodes) :
    fromRAM a l width m pos block host groupOf number =
      fromRAM a l' width m (by simpa only [←same] using pos)
        (fun x=>(block x).cast (congrArg Layout.blocks same)) (fun x=>(host x).cast (congrArg Layout.hosts same))
        (fun x=>(groupOf x).cast (congrArg Layout.groups same)) (fun x=>(number x).cast (congrArg Layout.nodes same)) :=by
  cases same
  rfl
end
end Hierarchy.DescentRetainedRangeDigits

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM ProtocolRAM
noncomputable section

/-- The scheduled reset uses the very same host and group in its candidate sheet, receiver and venue. -/
theorem scheduled_range_layout {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z oldLanes primitiveLanes : ℕ)
    (old : StageVenueTail.Date) (addr : ℕ→ℕ→Bank) (roster : Bank) (floor atFloor : ℕ) {w : ℕ}
    (u : (scheduled G S board k tail age p f gain drift degree h ordinary op s Z oldLanes primitiveLanes old addr roster floor).DateInputs atFloor w)
    (oldK : old.k=k) :
    let a:=scheduled G S board k tail age p f gain drift degree h ordinary op s Z oldLanes primitiveLanes old addr roster floor
    (DatePorts.reset a atFloor u).rangeLayout=a.successor.rangeLayout :=by
  dsimp only
  unfold DatePorts.rangeLayout ResetOutput.rangeLayout
  congr 1
  exact congrArg (2^·) oldK

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentRetainedRangeDigits DescentDatedPriorOperand DescentDatedAddressBook
open DescentLocalArchiveOrder DescentKernelHistory Computability.VPVNP.BurstRAM ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
    {k wire hist w : ℕ} {W₀ W : MarkedWorld F d P bits} {i₀ z₀ D₀ j z D : ℕ}
    {start : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist} {now : Reached W G q ε S k j z D wire hist}
    {p : ℕ} (hp : 0<p) (a : Archive W₀) (number : Local a.bit) (path : Path start now)
    (ports : ℕ→DatePorts) (memory : ℕ→Memory w)
    (room : ∀{U : MarkedWorld F d P bits} {i g C : ℕ} {r : Reached U G q ε S k i g C wire hist},
      ∀(prefix_ : Path start r) (wh : prefix_.whole p),
        (∃suffix_ : Path r now,prefix_.append suffix_=path) → RangeRoom (ports i) r (prefix_.archive p hp a wh).bit)
    (whole : path.whole p) (v : ResetOutput) (base : ℕ)
    (archive : (ports j).archive=PriorResetArchive.reset v base)
    (layout : (ports j).rangeLayout=v.rangeLayout) (bitsAt : (ports j).operandBits=v.nodeBits)
local notation "okAt" => room path whole ⟨.here,rfl⟩
local notation "regLayout" => (ports j).rangeLayout
local notation "occupant" x => Reached.NodeCells.coordinate now (x).1
local notation "cellOrder" => trajectory p hp a number path whole
local notation "siteType" => NodeOrder.All (path.archive p hp a whole).bit

include archive bitsAt in
/-- The archive, bit width, block, host, group and original primitive number all agree at final return. -/
theorem registeredPages_final_reset :
    registeredPages hp a number path ports memory room path whole =
      fromRAM (PriorResetArchive.reset v base) v.rangeLayout v.nodeBits (memory j)
        (by rw [←congrArg Layout.lanes layout]; exact (okAt).positive)
        (fun x : siteType=>((occupant x).2.2.cast (congrArg (2^·) (okAt).radix)).cast (congrArg Layout.blocks layout))
        (fun x : siteType=>(⟨(occupant x).1.val,(okAt).hosts x.1⟩:Fin (regLayout).hosts).cast (congrArg Layout.hosts layout))
        (fun x : siteType=>((occupant x).2.1.cast (okAt).groups).cast (congrArg Layout.groups layout))
        (fun x : siteType=>(((cellOrder x.1 x.2).castLE ((okAt).capacity x.1)):Fin (regLayout).nodes).cast (congrArg Layout.nodes layout)) :=by
  rw [registeredPages_at hp a number path ports memory room path .here rfl whole]
  unfold rangeRegister
  rw [archive,bitsAt]
  apply fromRAM_layout
  exact layout

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
