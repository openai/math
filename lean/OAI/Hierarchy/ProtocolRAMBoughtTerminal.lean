import OAI.Hierarchy.ProtocolRAMCalendarRemainders
import OAI.Hierarchy.ProtocolRAMBoughtArchive
import OAI.Hierarchy.ProtocolRAMBoughtPortLifetime
import OAI.Hierarchy.ProtocolRAMCalendarFeedLifetime

namespace OAI
/-! # Read the archived outer purchase in the final chronological RAM state -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section

variable {z d k q goods r edges N : ℕ}

theorem priced_flag_terminal (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (arena : Arena) (F : Attempt→Format z d k q goods) (initial width cap : ℕ)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (order : ∀ a,arena.base c (.attempt a)≤(F a).market.failures.base ∧
      arena.base c (.attempt a)≤(F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤(F a).testsStart)
    (mem : Shelf.Mem z d) (p h : ℕ) (ph : p<c.inject+c.cool) (hh : h<c.outerFuel) :
    let C:=pricedInstalled c finish prices F (feedColumns (N:=N) c arena F initial width cap) sink idBase role ids
    let a:=Attempt.outer p h
    let v:=(F a).atTime c finish prices a
    let frozen:=v.failures.pass.apply ((guard C a).apply (trialState C mem p h))
    mounted C (events c) mem → ArchiveRoom C mem (c.inject+c.cool) → v.rows≤2^(F a).batch.decisionBits →
    (repair C a).purchaseOut+v.rows≤arena.base c (.attempt a)+arena.stride →
    ∀j : Fin v.rows,run C (events c) mem ((repair C a).purchaseOut+j.val)=if observedMode C mem p h=3 then
      v.shelf.result v.sampler k v.depth frozen (v.flags+j.val) else 0 := by
  intro C a v frozen mountedAll archive padded fits j
  obtain ⟨tail,final,ready,afterward⟩:=outer_remainder C mem p h ph hh mountedAll
  refine (congrFun final ((repair C a).purchaseOut+j.val)).trans ?_
  apply priced_flag_archive c finish prices F _ sink idBase role ids mem p h _ tail archive ph hh padded ready j
  intro e he
  exact (priced_event_floor_for (N:=N) c finish prices arena F initial width cap sink idBase role ids order e _
    ((Nat.add_lt_add_left j.isLt _).trans_le (fits.trans (arena.apart c (afterward e he))))).1

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
