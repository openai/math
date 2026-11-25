import OAI.Hierarchy.ProtocolRAMCatalystPurchasedBirth
import OAI.Hierarchy.ProtocolRAMPricedMarketFrame
import OAI.Hierarchy.ProtocolRAMCalendarSegments

namespace OAI
/-! # The original market's shelf and signed decisions at its first reserve boundary -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen StripDirectory
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
variable {z d k q goods r edges : ℕ}

theorem priced_purchase_after (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (F : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (current : Shelf.Mem z d)
    (p h start : ℕ) (π : Equiv.Perm (Fin (2^z))) (fixture : Shelf.Mem z d) :
    let C:=pricedInstalled c finish prices F feeds sink idBase role ids
    let a:=Attempt.outer p h
    let v:=(F a).atTime c finish prices a
    let frozen:=v.failures.pass.apply ((guard C a).apply current)
    let header:=stratumHeader z d k v.sampler.degree v.depth start
    ready C (.attempt a) current →
    v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind frozen →
    (∀i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i frozen) →
    header.stop≤ v.shelf.firstBase → header.Loaded frozen →
    ArchiveReads v.shelf v.sampler π v.depth start v.phase v.temperature v.kind frozen
      (after C (.attempt a) current) k := by
  intro C a v frozen header head incoming rom hLow loaded
  have readyMarket : v.ready ((guard C a).apply current) := head.2.1
  obtain ⟨_,_,hd,room,_⟩:=readyMarket
  have run:=v.shelf.run v.sampler π v.depth hd v.phase v.temperature v.kind frozen fixture incoming rom room
  have under (x : ℕ) (low : x<(F a).testsStart) :
      after C (.attempt a) current x=v.shelf.result v.sampler k v.depth frozen x := by
    exact priced_preserves_market c finish prices F feeds sink idBase role ids a current x low head
  constructor
  · intro key row node
    let L := v.shelf.L v.sampler v.depth key
    let address := L.source.base + (node.val * L.candidates + row.val)
    have cell : address < L.endAddress := (L.source_range row node).2
    have stop : L.endAddress ≤ v.shelf.firstBase + count z d k * blockSize z d v.sampler.degree v.depth :=
      (v.shelf.end_le v.sampler v.depth key hd).trans (v.shelf.final_after v.sampler v.depth key)
    have early : address < (F a).testsStart := by
      change address < v.shelf.firstBase + count z d k * blockSize z d v.sampler.degree v.depth +
        2*(paths z v.sampler.degree v.depth+1) + v.rows
      omega
    exact (under address early).trans ((run.2.2.1 key).tiles row node)
  · intro key i
    rw [under]
    · exact run.2.2.2 key i
    · let span := paths z v.sampler.degree v.depth
      have last : (key.val + 1) * span ≤ count z d k * span :=
        Nat.mul_le_mul_right span key.isLt
      have field : key.val * span + i.val < count z d k * span := by
        exact (Nat.add_lt_add_left i.isLt (key.val * span)).trans_le (Nat.succ_mul key.val span ▸ last)
      change v.shelf.flagsBase v.sampler z d k v.depth + key.val * span + i.val <
        v.shelf.flagsBase v.sampler z d k v.depth + count z d k * span
      rw [Nat.add_assoc]
      exact Nat.add_lt_add_left field _
  · apply loaded.frame
    intro x _ hi
    have below:=hi.trans_le hLow
    have flags : v.shelf.firstBase≤ v.shelf.flagsBase v.sampler z d k v.depth := by
      dsimp only [Shelf.flagsBase]
      omega
    exact (under x ((below.trans_le flags).trans_le (Nat.le_add_right ..))).trans (run.2.1 x (.inl below))

theorem priced_purchase_archive (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (F : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (mem : Shelf.Mem z d)
    (p h start : ℕ) (π : Equiv.Perm (Fin (2^z))) (fixture : Shelf.Mem z d) :
    let C:=pricedInstalled c finish prices F feeds sink idBase role ids
    let a:=Attempt.outer p h
    let v:=(F a).atTime c finish prices a
    let current:=trialState C mem p h
    let frozen:=v.failures.pass.apply ((guard C a).apply current)
    let header:=stratumHeader z d k v.sampler.degree v.depth start
    ready C (.attempt a) current →
    v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind frozen →
    (∀i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i frozen) →
    header.stop≤ v.shelf.firstBase → header.Loaded frozen →
    ArchiveReads v.shelf v.sampler π v.depth start v.phase v.temperature v.kind frozen
      (reserveState C mem p h 0) k := by
  intro C a v current frozen header
  exact priced_purchase_after c finish prices F feeds sink idBase role ids current p h start π fixture

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
