import OAI.Hierarchy.TaggedWideOriginalRoleShelf
import OAI.Hierarchy.TaggedWideRoleScatter
import OAI.Hierarchy.TaggedWideTimeOccupancy
import OAI.Hierarchy.TaggedWireRoleROM

namespace OAI
/-! # Reading every priced historical width from its immutable physical role -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open AdaptiveProbe ReportSockets ProtocolRAM WireTelescope
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {h W k attempts : ℕ} (S : PurchaseSampler)

variable {width n physical : ℕ} (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) (unique : Exclusive marked)
    (rows : Fin n≃Source S π depth marked) (amount : Fin n→ℕ)
    (cap : Public S h W k attempts→ℕ)
    (room : ∀i b,amount i ≤ cap (named S π depth marked unique rows (i,b)))

/-- Actual native sparse publication for the two ends of all ordinary
and catalytic source rows. The real RAM offset is assembled from the same
site-stride table and the existing local role code as the terminal barrel. -/
theorem scatter (base scratch sink : ℕ) (size siteCode roleCode : Expr) (siteTable : Bank)
    (m : Memory width) (source : Fin physical → Option (Fin n×Bool))
    (covers : ∀i b,0<amount i→∃j,source j=some (i,b))
    (fits : ∀i,amount i<2^width)
    (sizeRoom : size.Fits width base)
    (addrRoom : (RoleWidths.destination base sink size (RoleWidths.offset siteTable siteCode roleCode)).Fits width base)
    (bigger : base+(siteLast h (2^W) k+1)*stride k S.degree attempts ≤ scratch)
    (scratchRoom : scratch+physical+physical<2^width) (sinkRoom : sink<base)
    (native : ∀j,size.eval m (j.val:Word width)=((source j).elim 0 (fun x=>amount x.1):ℕ))
    (siteRead : ∀j i b,source j=some (i,b)→0<amount i→
      siteTable.read m (siteCode.eval m (j.val:Word width))=
        (((name (site S (named S π depth marked unique rows (i,b)))).val*stride k S.degree attempts:ℕ):Word width))
    (roleRead : ∀j i b,source j=some (i,b)→0<amount i → roleCode.eval m (j.val:Word width)=
      (code S (named S π depth marked unique rows (i,b)):Word width)) :
    let L := (siteLast h (2^W) k+1)*stride k S.degree attempts
    let dst := RoleWidths.destination base sink size (RoleWidths.offset siteTable siteCode roleCode)
    ∃ out,(ProtocolRAMTurnReplay.program width base L scratch physical dst size).Exec m out
      (ProtocolRAMTurnReplay.work L physical dst size) ∧
      (∀q : (p : Public S h W k attempts) × Fin (cap p),
        q∈Set.range (statePlace S π depth marked unique rows amount cap room) ↔
          q.2.val<(out (base+(shelfSlot S q.1).val)).val) ∧
      ∀t,(t<base ∨ base+L ≤ t) → (t<scratch ∨ scratch+physical+physical ≤ t) → t≠sink → out t=m t := by
  intro L dst
  let key := named S π depth marked unique rows
  obtain ⟨out,run,stored,frame⟩ := RoleWidths.run key (shelfSlot S) (fun z=>amount z.1)
    base scratch sink size (RoleWidths.offset siteTable siteCode roleCode) m source
    (fun ⟨i,b⟩=>covers i b) (fun z=>fits z.1) sizeRoom addrRoom bigger scratchRoom sinkRoom native
    (fun j ⟨i,b⟩ seen pos=>by rw [shelf_index]; apply RoleWidths.offset_at _ _ _ _ _ _ _ _
                                (siteRead j i b seen pos) (roleRead j i b seen pos))
  refine ⟨out,run,fun q=>?_,frame⟩
  apply NamedAperture.range_read _ amount key cap room (fun p=>(out (base+(shelfSlot S p).val)).val) _ _ q
  · intro i side
    rw [stored,RoleWidths.shelf_live]
    exact Fin.val_cast_of_lt (fits i)
  · intro p none
    rw [stored,RoleWidths.shelf_blank _ _ _ _ none]
    rfl

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
