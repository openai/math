import OAI.Hierarchy.TraceReceiverMapExecution
import OAI.Hierarchy.TraceReceiverTerminalIssued

namespace OAI
/-! # Framing live input pins and physical task/node words through the terminal writer -/
noncomputable section
namespace Hierarchy.TraceReceiverForward
open ThreeFlat Diagonal PhysicalStage RAM
open Computability.VPVNP.BurstRAM PrivateRAM HistoryContraction TickTerminalRoot HistoryTerminalTape
open HistoryStageBody.Physical HistoryCommandTable
open TraceFactorReceiver
open scoped Fin.CommRing Classical BigOperators

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

/-- All dense weighted-evaluator inputs are below S9, including its unused
hidden-bit scratch before the separate evaluation starts. -/
theorem Source.low_pins (a : ℕ) (below : a<TickWorkspace.base u 9) :
    P.images n a=P.initial a := by
  obtain ⟨bank,roof,gap⟩:=Gather.grid_window P.large P.age
  have older:=TickWorkspace.apart (u:=u) (by decide : 9<18)
  have lower:=TickWorkspace.apart (u:=u) (by decide : 18<45)
  have cv := P.countdown_val
  apply TraceReceiverTasks.maps_frame (start:=0) (stop:=n) P.arena (D).tasks
    (GridReceiverBanks.mapHeader w) P.dst P.len P.initial (Nat.zero_le _) (by rw [cv];omega)
    (Or.inl (by change a<B+24;omega))
  · intro k _ _
    apply Or.inl
    change a<B+2*G+scanned P.ports k
    omega
  · intro k _ hk
    exact TraceReceiverRootBounds.kept_before (P.iteration ⟨k,hk⟩).2.2.1 P.page a
      (by change a<TickWorkspace.base u 9+4*_;omega)

theorem Source.ranged_low (a : ℕ) (below : a<B) : ranged a=P.images n a :=
  Issued.header_frame (D).current count cmd (P.images n) (Or.inl below)

theorem Source.ranged_parent (j : Fin 4) :
    ranged ((D).parent+j.val)=P.initial ((D).parent+j.val) := by
  have jj:=j.isLt
  have a : (D).parent=B+16:=rfl
  refine (Issued.header_frame (D).current count cmd (P.images n) (Or.inr (by change B+7≤B+16+j.val;omega))).trans ?_
  apply P.final_observations.2.2.2.2
  exact Or.inr (Or.inl (by rw [a];omega))

theorem Source.ranged_task (i : Fin n) :
    readTask ranged (((D).tasks+5*i.val:ℕ):Word W)=readTask P.initial (((D).tasks+5*i.val:ℕ):Word W) := by
  obtain ⟨_,roof,gap⟩:=Gather.grid_window P.large P.age
  have job:=P.jobs
  have ii:=i.isLt
  have eqn (j : Fin 5) :
      ranged (((((D).tasks+5*i.val:ℕ):Word W)+(j.val:Word W)).val)=
        P.initial (((((D).tasks+5*i.val:ℕ):Word W)+(j.val:Word W)).val) := by
    have jj:=j.isLt
    have tbl : (D).tasks=B+G:=rfl
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by rw [tbl];omega)]
    apply (Issued.header_frame (D).current count cmd (P.images n) (Or.inr (by change B+7≤(D).tasks+5*i.val+j.val;rw [tbl];omega))).trans
    apply P.final_observations.2.2.2.2 _ (Or.inr (Or.inr ?_))
    constructor <;> omega
  unfold readTask
  congr 1
  · exact eqn 0
  · exact eqn 1
  · exact eqn 2
  · exact eqn 3
  · exact eqn 4

theorem Source.returned_low (a : ℕ) (below : a<TickWorkspace.base u 9) :
    Issued.image ctrl cmd (D).tasks n ranged a=P.initial a := by
  obtain ⟨bank,roof,gap⟩:=Gather.grid_window P.large P.age
  have lower:=TickWorkspace.apart (u:=u) (by decide : 9<45)
  exact (Issued.frame ctrl cmd (D).tasks n a ranged (Or.inl (by change a<B+32;omega))
    (Or.inl (by change a<B+9*G;omega))).trans ((P.ranged_low a (by omega)).trans (P.low_pins a below))

end Hierarchy.TraceReceiverForward
end

end OAI
