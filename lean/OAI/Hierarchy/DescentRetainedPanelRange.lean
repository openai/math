import OAI.Hierarchy.DescentArchiveCellReads
import OAI.Hierarchy.DescentResetRetainedIssue
import OAI.Hierarchy.DescentResetRetainedPriorBanks
import OAI.Hierarchy.DescentOrdinaryHostPad

namespace OAI
/-! # The prior registered range word at the genuine inverse-remixed reset donor -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.PackedFlow.Channels
open DescentGL DescentColonies DescentOrdinaryHostPad DescentRetainedRangeDigits DescentSixParty DescentKernelHistory
open DescentDatedPriorOperand DescentDatedAddressBook ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : DescentResetRetainedSetup.Layout) (size : 2^(v.high+v.low)=v.groups*v.blocks)
    (cut : v.cut≤v.high+v.low) (matrix : DescentGL.Layout (v.high+v.low)) (data : v.Values)
    (h : Fin v.hosts) (hi : Block v.cut) (d : Fin v.donors)
local notation "physical" => v.site (fun j=>blockValues cut (v.before size data j) matrix) h hi
local notation "source_" => (rearrange matrix).symm (DescentIssuedFallbackPanel.join cut hi d)
local notation "coords" => (finProdFinEquiv.symm (Fin.cast size source_) : Fin v.groups × Fin v.blocks)
variable {w H : ℕ} {F P : Type} [Field F] {e : ℕ} {bits : P→ℕ} {W : MarkedWorld F e P bits}
    {B : BitDescription W} (archive : PriorResetArchive) (mem : Memory w) (pos : 0<v.previousLanes)
    (block : NodeOrder.All B→Fin v.blocks) (host : NodeOrder.All B→Fin H)
    (groupOf : NodeOrder.All B→Fin v.groups) (number : NodeOrder.All B→Fin v.previousNodes)
local notation "old" => ({v.previousLayout with hosts:=H} : DescentDatedPriorOperand.Layout)
local notation "registered" => fromRAM archive old v.bits mem pos block host groupOf number

/-- The source bank is read at its smaller, original host rectangle. The
actual reset may pad this to any larger host count before the shuffle. -/
theorem issued_prior_range (y : NodeOrder.All B) (j : Fin v.previousArgs) (f : Fin 3)
    (cells : Fin H→Fin v.groups→Cell (v.bits*v.previousNodes))
    (read : Reads (previousBank old archive.arguments (block y) (DescentOperandStateBanks.page (page f) j))
      cells v.previousLanes mem)
    (width : v.bits*v.previousNodes*v.previousLanes≤w)
    (padded : data (v.sourceID (v.operandField (page f) j) (block y))=extend v.hosts cells)
    (hosted : h.val=(host y).val) (located : coords=(groupOf y,block y)) :
    (v.entry physical d (number y) (v.operandField (page f) j)).val=(registered).word y j.val f := by
  rw [v.prior_digit data size cut matrix h hi d (number y) (v.operandField (page f) j)]
  rw [located,padded,word_of_cell archive old v.bits mem pos block host groupOf number y j.val f]
  rw [cell_of_read archive old v.bits mem pos block host groupOf number y j f cells read width]
  have present : h.val<H:=by rw [hosted];exact (host y).isLt
  simp only [extend,dite_eq_left present]
  have same : (⟨h.val,present⟩:Fin H)=host y:=Fin.ext hosted
  rw [same]
  rfl

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
