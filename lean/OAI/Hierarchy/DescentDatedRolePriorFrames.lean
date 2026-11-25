import OAI.Hierarchy.DescentDatedRetainedRoleSource
import OAI.Hierarchy.DescentPhysicalResetDateOutput

namespace OAI
/-! # Saved old primitives, matrix packets and elected bases at the physical movement -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentSixParty.Chronology DescentGLPacked DescentColonies DescentCompiler DescentPlainTerminal.Suffix
open DescentSIMDLookup DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : FinalInputs u)
local notation "P₀" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "rc" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "lo" => (v).finalEnd b
local notation "hi" => (v).fullEnd b
local notation "move" => (v).roleTransfer
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "headTime" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "stencil" => a.throughStencil u.shape floor u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "stencilTime" => a.throughStencilTicks u.shape floor u.count u.hub u.g u.Y u.sourceRows u.oldDegree w

theorem venue_prior_frame (fit : z.Room) (mid : Memory w) (j : ℕ) (early : j<lo) : z.venueImage mid j=mid j:=by
  have done_:=z.tail_result fit mid
  have order:=(v).complete_after b
  exact (done_.2.2.2 j (early.trans_le (order.1.trans order.2))).symm.trans (done_.2.2.1 j (.inl early))

theorem previous_primitive_reads {before mid dst : Memory w} (ready : u.Ready) (fit : z.Room)
    (operands : u.throughOperandDate.Runs before mid) (run : (date z).Runs before dst)
    (X : Fin (move).transfer.blocks→Fin (move).transfer.hosts→Fin (move).transfer.groups→Cell (move).transfer.wholeWord)
    (oldFits : ∀j,(z.previousRoles j).Fits w floor)
    (capacity : ∀j,(move).transfer.hosts*chunks (move).transfer.groups (move).transfer.previousLanes≤(z.previousRoles j).size)
    (old : ∀j,Reads (z.previousRoles j) (X j) (move).transfer.previousLanes before) (j) :
    Reads (z.previousRoles j) (X j) (move).transfer.previousLanes (z.venueImage mid):=by
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ready.ordered
  have low : floor≤lo:=by omega
  have end_:=z.tail_result fit mid
  have agreed:=date_image z fit run operands
  intro p
  have addr:(z.previousRoles j).base+(row _ _ _ p).val<floor:=
    (Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le (capacity j)) _).trans_le (oldFits j).2.2
  have full:=(v).complete_after b
  have here:=end_.2.2.2 _ (addr.trans_le (low.trans (full.1.trans full.2)))
  exact here.symm.trans ((congrFun agreed _).symm.trans ((date_output_below z ready fit run _ (.inl addr)).trans (old j p)))

theorem original_matrix_source {before roots mid : Memory w} (ready : u.Ready) (fit : z.Room)
    (rootRun : (head).Exec before roots headTime) (operands : u.throughOperandDate.Runs before mid)
    (Y : Fin (move).transfer.hosts→Fin (move).control.groups→Cell (move).control.rootWidth)
    (issued : Source (oldMatrix u) Y (move).rootLanes roots) :
    Source (oldMatrix u) Y (move).rootLanes (z.venueImage mid):=by
  have early:(rc).preparedEnd u.book≤lo:=by
    rw [ready.rootEnd]
    obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ready.ordered
    omega
  have bound : (oldMatrix u).Fits w ((rc).preparedEnd u.book):=(rc).gathered_fits u.book u.bookFits _
  apply fun p=>(eval_below (oldMatrix u) _ roots (z.venueImage mid) bound (fun j hj=>
    (z.venue_prior_frame fit mid j (hj.trans_le early)).trans (u.prefix_unchanged ready rootRun operands j hj))).trans (issued p)

theorem original_basis {before measured mid dst : Memory w} (ready : u.Ready) (fit : z.Room)
    (scan : (stencil).Exec before measured stencilTime) (run : (date z).Runs before dst)
    (operands : u.throughOperandDate.Runs before mid) :
    z.venueImage mid (P₀).saved=measured (P₀).saved:=by
  have saved:=fit.roleMove.saved
  have early : (P₀).saved<hi:=by
    change (⟨(P₀).saved,0⟩ : Bank).base<hi
    have pos:=saved.1;have limit:=saved.2.2;omega
  have old:=(z.tail_result fit mid).2.2.2 _ early
  exact old.symm.trans ((congrFun (date_image z fit run operands) _).symm.trans
    (date_stencil_below z ready fit run scan _ (stencil_saved_before (u:=u))))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
