import OAI.Hierarchy.TaggedWideOriginalSweep
import OAI.Hierarchy.TaggedWideRolePageRun

namespace OAI
/-! # Retaining every actual dated role field through the original sequence -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles ReportSockets
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
variable {T N W native h k jobs : ℕ} (g : Dated T) (rom work : ℕ)
    (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (mark : Marks h W k jobs) (unique : Exclusive mark) (rows : Fin N≃Source S π depth mark)
    (qty : Fin (T+1)→Fin N→ℕ) (id : Fin N→ℕ)
    (volume : g.roleWords=(siteLast h (2^W) k+1)*HistoryRoles.stride k S.degree jobs)

def Dated.roleResult (t : Fin (T+1)) (f : Fin 3) : PageResult native (g.rolePage rom work t f) where
  holds m:=DatedRoleSheets.roleFact g.physical S π depth mark unique rows (g.roleStart work t) (qty t) id m f
  localize:=g.roleFact_local rom work S π depth mark unique rows qty id volume t f

theorem Dated.role_issued (m : Memory native) (source : Fin g.physical→Option (Fin N)) (side : Fin N→Bool→Bool)
    (ready : ∀t,DatedRoleSheets.Reads g.physical g.chart g.sockets (g.siteStride rom) (g.amount t) g.ordinal
      S π depth mark unique rows m (qty t) id source side)
    (fits : ∀t,DatedRoleSheets.Fits g.physical g.chart g.sockets (g.siteStride rom) (g.amount t) g.ordinal native work)
    (room : g.rolesEnd work<2^native) (t : Fin (T+1)) (f : Fin 3) :
    (g.roleResult rom work S π depth mark unique rows qty id volume t f).Issued work m := by
  intro now low
  obtain ⟨out,run,observed,frame⟩:=g.run_role rom work S π depth mark unique rows qty id source side volume
    m now t f work (Nat.le_add_right ..) (fits t) (ready t) low room
  exact ⟨out,run,observed,fun a ha=>frame a (.inl ha)⟩

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
