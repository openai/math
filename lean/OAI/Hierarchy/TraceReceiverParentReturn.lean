import OAI.Hierarchy.TraceReceiverMapReturn
import OAI.Hierarchy.TraceReceiverPreparationRoom
import OAI.Hierarchy.TraceReceiverDecodedTask
import OAI.Hierarchy.TraceResourceMount

namespace OAI
/-! # The issued parent, final S18 amount totals and both gather cursor words -/

noncomputable section
namespace Hierarchy.TraceReceiverForward
open ThreeFlat Diagonal PhysicalStage RAM
open Computability.VPVNP.BurstRAM PrivateRAM HistoryCommandTable TraceFactorReceiver
open scoped Fin.CommRing BigOperators Classical

variable {F Pins : Type} [Field F] [Fintype F] {w u p suffix n d l : ℕ}
variable (P : Source F Pins w u p suffix n d l)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "B" => GridReceiverBanks.base w
local notation "G" => GridReceiverBanks.gap w
local notation "D" => GridReceiverBanks.tasks w
local notation "cmd" => GridReceiverBanks.commands w
local notation "ctrl" => GridReceiverBanks.cursor w
local notation "count" => TickWorkspace.base u 18+1
local notation "ranged" => TraceReceiverTasks.rangeImage (D).current count cmd 0 7 (P.images n)
local notation "issued" => Issued.image ctrl cmd (D).tasks n ranged

/-- The four words consumed by the command issuer come from the parent's
native mount before the S13 scans and from the actual final map image. -/
theorem Source.parent_node (elected : Memory W)
    (boot : P.initial=TraceReceiverTasks.beforeImage D count (GridReceiverBanks.limit w)
      (GridReceiverBanks.width w) n
      (TraceAdmission.Resources.mounted (D).parent [TickWorkspace.base u 9,p,0,0] elected)) :
    readNode ranged ((D).parent:Word W)=⟨(TickWorkspace.base u 9:Word W),p,0,0⟩ := by
  let xs : List ℕ := [TickWorkspace.base u 9,p,0,0]
  let input:=TraceAdmission.Resources.mounted (D).parent xs elected
  obtain ⟨_,roof,gap⟩:=Gather.grid_window P.large P.age
  have addr : (D).parent=B+16 := rfl
  have fits : (D).parent+4≤2^W := by rw [addr];omega
  have word (j : Fin 4) : ranged ((D).parent+j.val)=(xs[j.val]:Word W) := by
    rw [P.ranged_parent j,boot]
    exact (TraceReceiverTasks.before_parent_frame (n:=n) P.large input j count).trans
      (TraceAdmission.Resources.mounted_at (D).parent xs elected j fits)
  refine Issued.read_node (D).parent (TickWorkspace.base u 9) p 0 0 ranged (by omega) ?_ ?_ ?_ ?_
  · exact word 0
  · exact word 1
  · exact word 2
  · exact word 3

include P in
private theorem Source.control_below (j : Fin 4) : TickWorkspace.base u 18+j.val<B := by
  obtain ⟨bank,_,_⟩:=Gather.grid_window P.large P.age
  have pos : 0<TickWorkspace.stride u := by unfold TickWorkspace.stride;positivity
  have endPage : TickWorkspace.base u 18+4≤TickWorkspace.base u 45 := by
    change 19*TickWorkspace.stride u+4≤46*TickWorkspace.stride u
    omega
  have hj:=j.isLt
  omega

/-- The range initializer reads the same two totals produced by the
terminal control loop, including when it selects zero roots. -/
theorem Source.ranged_totals :
    (ranged (TickWorkspace.base u 18+2)).val=∑ i,P.rows i ∧
      (ranged (TickWorkspace.base u 18+3)).val=∑ i,P.bits i := by
  have same (j : Fin 4) := P.ranged_low (TickWorkspace.base u 18+j.val) (P.control_below j)
  exact ⟨(congrArg Fin.val (same 2)).trans P.final_observations.2.2.1,
    (congrArg Fin.val (same 3)).trans P.final_observations.2.2.2.1⟩

/-- Issuing the final seven-word commands and writing the cursor and last
word preserves the S18 row and private-bit totals. -/
theorem Source.returned_totals :
    (issued (TickWorkspace.base u 18+2)).val=∑ i,P.rows i ∧
      (issued (TickWorkspace.base u 18+3)).val=∑ i,P.bits i := by
  have same (j : Fin 4) : issued (TickWorkspace.base u 18+j.val)=ranged (TickWorkspace.base u 18+j.val) := by
    have low:=P.control_below j
    apply Issued.frame ctrl cmd (D).tasks n _ ranged (Or.inl ?_) (Or.inl ?_)
    · change TickWorkspace.base u 18+j.val<B+32;omega
    · change TickWorkspace.base u 18+j.val<B+9*G;omega
  exact ⟨(congrArg Fin.val (same 2)).trans P.ranged_totals.1,
    (congrArg Fin.val (same 3)).trans P.ranged_totals.2⟩

/-- Both pointers are initialized by the native two-word cursor writer. -/
theorem Source.returned_cursor :
    issued ctrl=(cmd:Word W) ∧ issued (ctrl+1)=((cmd+7*n:ℕ):Word W) := by
  let out:=Commands.output cmd (D).tasks n ranged
  have written:=Cursor.words ctrl cmd n out
  exact ⟨written.1,written.2.1⟩

end Hierarchy.TraceReceiverForward

end
end OAI
