import OAI.Hierarchy.DescentResetTerminalRegisterLayout
import OAI.Hierarchy.DescentRangeRegisterRAM
import OAI.Hierarchy.DescentTerminalResetDatedFields

namespace OAI
/-! # The literal scalar register after the final scatter at a reset date -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentKernelHistory DescentLocalArchiveOrder
open DescentSIMDLookup DescentPackedColony DescentRetainedRangeDigits DescentDatedPriorOperand
open Computability.VPVNP.BurstRAM ProtocolRAM
noncomputable section
open scoped Classical Fin.CommRing
variable (v : ResetOutput)
local notation "A" => v.receiver

private theorem bankFromLayout (l : Layout) (floor fieldBits : ℕ) (block : Fin l.blocks)
    (pg : DescentOperandStateBanks.Pages l.operands) :
    let names := (7*l.operands)*l.blocks
    previousBank l (DescentResetNodeBooks.output floor names l.nodes l.hosts l.groups fieldBits l.lanes) block pg =
      DescentResetNodeBooks.bank floor names l.nodes l.hosts l.groups fieldBits l.lanes (finProdFinEquiv (pg,block)) := by
  simp only [previousBank,DescentResetNodeBooks.bank,finProdFinEquiv_apply_val,Layout.rows,DescentResetNodeBooks.rows]
  congr 1
  ring

theorem range_bank (base : ℕ) (x : Fin (A).blocks) (j : Fin v.argumentSlots) (f : Fin 3) :
    previousBank v.rangeLayout (PriorResetArchive.reset v base).arguments x (DescentOperandStateBanks.page (page f) j)=
    v.terminalField base (page f) j x :=
  bankFromLayout v.rangeLayout (v.scalarEnd base) v.nodeBits x (DescentOperandStateBanks.page (page f) j)

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {world : MarkedWorld F d P bits}
    {B : BitDescription world} {w : ℕ} (base : ℕ) (dst : Memory w) (pos : 0<v.receiver.lanes)
    (block : NodeOrder.All B→Fin v.receiver.blocks) (host : NodeOrder.All B→Fin v.receiver.hosts)
    (groupOf : NodeOrder.All B→Fin v.receiver.groups) (number : NodeOrder.All B→Fin v.nodes)
local notation "reg" => fromRAM (PriorResetArchive.reset v base) v.rangeLayout v.nodeBits dst pos block host groupOf number

/-- The `PhysicalReset.dated_fields` receipt supplies this observed packed column on the
original full `.date` return. The mixed-radix extraction recovers precisely the earlier scalar
candidate at the requested host, group and occupied local node. -/
theorem issued_range (u : NodeOrder.All B) (j : Fin v.argumentSlots) (f : Fin 3)
    (scalar : Fin v.nodes→Fin (A).hosts→Fin (A).groups→Cell v.nodeBits)
    (seen : Reads (v.terminalField base (page f) j (block u))
      (fun h g=>encode v.nodeBits v.nodes fun n=>scalar n h g) (A).lanes dst)
    (fit : v.nodeBits*v.nodes*(A).lanes≤w) :
    (reg).word u j.val f=(scalar (number u) (host u) (groupOf u)).val := by
  have posted : Reads (previousBank v.rangeLayout (PriorResetArchive.reset v base).arguments (block u)
       (DescentOperandStateBanks.page (page f) j))
       (fun h g => encode v.nodeBits v.nodes fun n => scalar n h g) v.receiver.lanes dst := by
    rw [range_bank]
    exact seen
  exact (word_read (PriorResetArchive.reset v base) v.rangeLayout v.nodeBits dst pos block host groupOf number u j f _ posted fit).trans
    (congrArg (fun cells : Fin v.nodes → Cell v.nodeBits => (cells (number u)).val)
      ((encode v.nodeBits v.nodes).symm_apply_apply (fun n => scalar n (host u) (groupOf u))))

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
