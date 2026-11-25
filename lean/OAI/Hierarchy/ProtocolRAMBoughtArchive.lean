import OAI.Hierarchy.ProtocolRAMCalendarLiveCount

namespace OAI
/-! # Permanent purchase bits after all subsequent calendar operations -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseStage PurchaseFrozen
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k q goods r edges : ℕ}

theorem priced_flag_archive (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr)
    (ids : Attempt→Fin goods→Expr) (mem : Shelf.Mem z d) (p h total : ℕ) (tail : List Event) :
    let C:=pricedInstalled c finish prices format feeds sink idBase role ids
    let a:=Attempt.outer p h
    let v:=(format a).atTime c finish prices a
    let current:=trialState C mem p h
    let first:=after C (.attempt a) current
    let frozen:=v.failures.pass.apply ((guard C a).apply current)
    ArchiveRoom C mem total → p<total → h<c.outerFuel → v.rows≤2^(format a).batch.decisionBits →
    mounted C tail first → ∀u : Fin v.rows,
      (∀e∈tail,protected C ((repair C a).purchaseOut+u.val) e) →
      run C tail first ((repair C a).purchaseOut+u.val)=if observedMode C mem p h=3 then
        v.shelf.result v.sampler k v.depth frozen (v.flags+u.val) else 0 := by
  intro C a v current first frozen archive hp hh padded tailReady u safe
  obtain ⟨mounted,_,board,_⟩:=archive.outerHead p hp h hh
  have readyMarket : v.ready ((guard C a).apply current) := mounted.2.1
  obtain ⟨_,_,_,room,_,_,input,_⟩:=readyMarket
  have four : 4≤v.flags:=v.shelf.flags_four v.sampler z d k v.depth input.afterCT
  have base : decisionBase (C.layout a)=v.flags:=decisionBase_postLayout v.flags v.rows four
  have written := purchase_flag_mode C mem p h mounted board archive.wide (by
    change decisionBase (C.layout a)+v.rows≤_ ∧ _
    rw [base]
    exact ⟨room.le,(format a).purchase_lanes padded⟩) u
  have image : prepared C a current=v.shelf.result v.sampler k v.depth frozen := rfl
  change first ((repair C a).purchaseOut+u.val) =
    (if observedMode C mem p h=3 then prepared C a current (decisionBase (C.layout a)+u.val) else 0) at written
  rw [base,image] at written
  exact (run_frame C tail first _ tailReady safe).trans written

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
