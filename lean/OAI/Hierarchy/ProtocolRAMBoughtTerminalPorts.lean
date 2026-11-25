import OAI.Hierarchy.ProtocolRAMPricedMarketFrame
import OAI.Hierarchy.ProtocolRAMBoughtTerminal

namespace OAI
/-! # The final calendar memory contains each outer event's actual DFS paths -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage PurchaseCT
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k q goods r edges N : ℕ}

theorem priced_portData_terminal (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (arena : Arena) (F : Attempt→Format z d k q goods) (initial width cap : ℕ)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (order : ∀a,arena.base c (.attempt a)≤(F a).market.failures.base ∧
      arena.base c (.attempt a)≤(F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤(F a).testsStart)
    (mem : Shelf.Mem z d) (p h : ℕ) (ph : p<c.inject+c.cool) (hh : h<c.outerFuel) :
    let C:=pricedInstalled c finish prices F (feedColumns (N:=N) c arena F initial width cap) sink idBase role ids
    let a:=Attempt.outer p h
    let v:=(F a).atTime c finish prices a
    let current:=trialState C mem p h
    let frozen:=v.failures.pass.apply ((guard C a).apply current)
    ∀ (π : Equiv.Perm (Fin (2^z))) (fixture : Shelf.Mem z d),
    v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind frozen →
    (∀i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i frozen) →
    mounted C (events c) mem → (F a).testsStart≤arena.base c (.attempt a)+arena.stride →
      ∀i : Key z d k,v.shelf.PortData v.sampler π v.depth i (run C (events c) mem) := by
  intro C a v current frozen π fixture incoming rom runAll fits i
  have head := outer_head_ready runAll ph hh
  have start : v.ready ((guard C a).apply current) := head.2.1
  obtain ⟨_,_,hd,space,_⟩:=start
  have base:=v.shelf.portData v.sampler π v.depth hd v.phase v.temperature v.kind frozen fixture incoming rom space i
  obtain ⟨tail,final,tailReady,later⟩:=outer_remainder C mem p h ph hh runAll
  have endBelow := (v.shelf.end_le v.sampler v.depth i hd).trans (v.shelf.final_after v.sampler v.depth i)
  change _<2^wordBits z d Native.copies at space
  apply base.of_frame (incoming.dimensions i).room
  intro x used
  have under : x<(F a).testsStart := by
    have order₀ := incoming.afterCT
    change x<v.shelf.flagsBase v.sampler z d k v.depth+v.rows
    dsimp only [Shelf.flagsBase]
    rcases used with ct|slab
    · omega
    · exact slab.2.trans_le (by omega)
  have suffix := run_frame C tail (after C (.attempt a) current) x tailReady (fun e he=>
    (priced_event_floor_for (N:=N) c finish prices arena F initial width cap sink idBase role ids order e x
      (under.trans_le (fits.trans (arena.apart c (later e he))))).1)
  exact (congrFun final x).trans (suffix.trans
    (priced_preserves_market c finish prices F _ sink idBase role ids a current x under head))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
