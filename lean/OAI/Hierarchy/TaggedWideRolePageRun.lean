import OAI.Hierarchy.TaggedWideRoleSheetRun
import OAI.Hierarchy.TaggedWideScatterOrder

namespace OAI
/-! # Each sparse width, ordinal and peer scan in the literal dated program -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles ReportSockets
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {T N n W h k jobs : ℕ} (g : Dated T) (rom work : ℕ)
    (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (mark : Marks h W k jobs) (unique : Exclusive mark) (rows : Fin N≃Source S π depth mark)
local notation "size" => (siteLast h (2^W) k+1)*HistoryRoles.stride k S.degree jobs
variable (qty : Fin (T+1)→Fin N→ℕ) (id : Fin N→ℕ)
    (source : Fin g.physical→Option (Fin N)) (side : Fin N→Bool→Bool)

theorem Dated.run_role {native : ℕ} (volume : g.roleWords=size) (old now : Memory native)
    (t : Fin (T+1)) (f : Fin 3) (scope : ℕ) («scoped» : scope≤g.roleStart work t)
    (fits : DatedRoleSheets.Fits g.physical g.chart g.sockets (g.siteStride rom) (g.amount t) g.ordinal native scope)
    (ready : DatedRoleSheets.Reads g.physical g.chart g.sockets (g.siteStride rom) (g.amount t) g.ordinal
      S π depth mark unique rows old (qty t) id source side)
    (preserved : ∀a,a<scope→now a=old a)
    (limit : g.rolesEnd work<2^native) :
    let page:=g.rolePage rom work t f
    ∃out,(page.code native).Exec now out page.ticks ∧
      DatedRoleSheets.roleFact g.physical S π depth mark unique rows (g.roleStart work t) (qty t) id out f ∧
      ∀a,a<page.floor ∨ page.stop≤a→ out a=now a := by
  intro page
  have room : g.roleStart work t+3*DatedRoleSheets.span size g.physical<2^native := by
    apply lt_of_le_of_lt _ limit
    change work+t.val*(3*g.roleSpan)+3*DatedRoleSheets.span size g.physical≤work+(T+1)*(3*g.roleSpan)
    rw [←volume]
    change work+t.val*(3*g.roleSpan)+3*g.roleSpan≤_
    rw [Nat.add_assoc,←Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ t.isLt) _
  obtain ⟨out,run,observed,frame⟩:=DatedRoleSheets.step_from g.physical g.chart g.sockets (g.siteStride rom)
    (g.amount t) g.ordinal S π depth mark unique rows (g.roleStart work t) old (qty t) id source side
    scope «scoped» fits ready room f now preserved
  refine ⟨out,?_,observed,?_⟩
  · change (DatedRoleSheets.leaf g.physical g.chart g.sockets (g.siteStride rom) (g.amount t)
        g.ordinal native (g.roleStart work t) g.roleWords f).Exec now out
        (DatedRoleSheets.leafWork g.physical g.chart g.sockets (g.siteStride rom) (g.amount t)
          g.ordinal (g.roleStart work t) g.roleWords f)
    rw [volume]
    exact @run
  · intro a h
    apply frame
    simpa only [page,Dated.rolePage,Scatter.floor,Scatter.stop,DatedRoleSheets.sheet,Nat.add_sub_cancel,
      DatedRoleSheets.span,volume,Nat.add_assoc] using h

theorem Dated.roleFact_local {native : ℕ} (volume : g.roleWords=size) (t : Fin (T+1)) (f : Fin 3)
    (a b : Memory native)
    (same : ∀x,(g.rolePage rom work t f).floor≤x→x<(g.rolePage rom work t f).stop→b x=a x)
    (seen : DatedRoleSheets.roleFact g.physical S π depth mark unique rows (g.roleStart work t) (qty t) id a f) :
    DatedRoleSheets.roleFact g.physical S π depth mark unique rows (g.roleStart work t) (qty t) id b f := by
  intro q
  rw [←seen q]
  apply same
  · simp only [Dated.rolePage,Scatter.floor,DatedRoleSheets.sheet,volume,Nat.add_sub_cancel];omega
  · have h:=q.isLt
    simp only [Dated.rolePage,Scatter.stop,volume];omega

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
