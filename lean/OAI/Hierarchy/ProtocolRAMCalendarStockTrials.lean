import OAI.Hierarchy.ProtocolRAMCalendarStockBound
import OAI.Hierarchy.ProtocolRAMCalendarInventory
import OAI.Hierarchy.ProtocolRAMCalendarRemainders

namespace OAI
/-! # Stock ceilings at actual trial entry and at every saved outer purchase -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockBound
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe
variable {w q goods z N k ceiling : ℕ} {C : Chart w q goods} {b : Banks} {start : Memory w}

theorem Run.mounted_all (r : Run C b start z N k ceiling) : mounted C (events C.mesh) start := by
  simpa using (r (events C.mesh).length le_rfl).1

theorem Run.event_inputs (r : Run C b start z N k ceiling) (e : Event) (live : e∈events C.mesh) :
    let m := state C start (position C.mesh e)
    Bounded z N k (b.previous C.mesh e) ceiling m ∧ Bounded z N k (b.reserve e) ceiling m := by
  obtain ⟨j,hj,eq⟩ := List.getElem_of_mem live
  have order := position_at C.mesh hj
  rw [eq] at order
  have cap := b.inputs C.mesh ⟨j,hj⟩ (r j hj.le).2
  change Bounded z N k (b.previous C.mesh ((events C.mesh)[j])) ceiling (state C start j) ∧
    Bounded z N k (b.reserve ((events C.mesh)[j])) ceiling (state C start j) at cap
  simpa only [eq,order] using cap

theorem Run.archive (r : Run C b start z N k ceiling) (e : Event) (live : e∈events C.mesh)
    (j : ℕ) (past : position C.mesh e< j) (bound : j≤(events C.mesh).length)
    (base : ℕ) (receipt : base∈b.publications e) : Bounded z N k base ceiling (state C start j) := by
  obtain ⟨u,hu,eq⟩ := List.getElem_of_mem live
  have prev := position_at C.mesh hu
  rw [eq] at prev
  exact (r j bound).2.2.2 ⟨u,hu⟩ (prev▸past) base (by simpa only [eq] using receipt)

theorem Run.terminal (r : Run C b start z N k ceiling) (A : AccountColumns (Commodity (Fin (2^z)) N k))
    (a : Attempt) (last : position C.mesh (.attempt a)=(events C.mesh).length)
    (atStock : ∀i,A.stockAt a i=b.previous C.mesh (.attempt a)+PurchaseInventory.slot i)
    (i : Commodity (Fin (2^z)) N k) : (A.read a (run C (events C.mesh) start)).bits i≤ ceiling := by
  have cap := b.previous_at C.mesh (.attempt a) last (r (events C.mesh).length le_rfl).2 i
  change ((run C (events C.mesh) start) (A.stockAt a i)).val≤ ceiling
  rw [atStock]
  simpa only [state, List.take_length, PurchaseInventory.stock] using cap

theorem Run.slot (r : Run C b start z N k ceiling) {e : Event} {prior tail : List Event} {m : Memory w}
    (atEntry : Slot C start e prior tail m) :
    Bounded z N k (b.previous C.mesh e) ceiling m ∧ Bounded z N k (b.reserve e) ceiling m := by
  have hit : prior.length< (events C.mesh).length := by rw [atEntry.events];simp
  have key : (events C.mesh)[prior.length]=e := by simp [atEntry.events,List.getElem_append_right (Nat.le_refl prior.length)]
  have cur : state C start prior.length=m := by
    unfold state
    rw [atEntry.events,List.take_left]
    exact atEntry.entry
  have «prefix» := (r prior.length hit.le).2
  have seen := b.inputs C.mesh ⟨prior.length,hit⟩ «prefix»
  change Bounded z N k (b.previous C.mesh ((events C.mesh)[prior.length])) ceiling (state C start prior.length) ∧
    Bounded z N k (b.reserve ((events C.mesh)[prior.length])) ceiling (state C start prior.length) at seen
  rwa [key,cur] at seen

theorem Run.trial (r : Run C b start z N k ceiling) (A : AccountColumns (Commodity (Fin (2^z)) N k))
    (p h : ℕ) (phase : p< C.mesh.inject+C.mesh.cool) (trial : h< C.mesh.outerFuel)
    (atStock : ∀i,A.stockAt (.outer p h) i=b.previous C.mesh (.attempt (.outer p h))+PurchaseInventory.slot i)
    (i : Commodity (Fin (2^z)) N k) : (A.trial C start p h).bits i≤ ceiling := by
  obtain ⟨_,cut⟩ := outer_slot C start p h phase trial r.mounted_all
  change ((trialState C start p h) (A.stockAt _ i)).val≤ ceiling
  rw [atStock]
  exact (r.slot cut).1 i

theorem Run.inner (r : Run C b start z N k ceiling) (A : AccountColumns (Commodity (Fin (2^z)) N k))
    (p h j t : ℕ) (phase : p< C.mesh.inject+C.mesh.cool) (trial : h< C.mesh.outerFuel)
    (slice : j< C.mesh.reserveSteps) (live : t< C.mesh.innerFuel)
    (atStock : ∀i,A.stockAt (.inner p h j t) i=b.previous C.mesh (.attempt (.inner p h j t))+PurchaseInventory.slot i)
    (i : Commodity (Fin (2^z)) N k) : (A.inner C start p h j t).bits i≤ ceiling := by
  obtain ⟨_,cut⟩ := inner_slot C start p h j t phase trial slice live r.mounted_all
  change ((innerState C start p h j t) (A.stockAt _ i)).val≤ ceiling
  rw [atStock]
  exact (r.slot cut).1 i

theorem Run.trial_end (r : Run C b start z N k ceiling) (A : AccountColumns (Commodity (Fin (2^z)) N k))
    (p : ℕ) (phase : p< C.mesh.inject+C.mesh.cool)
    (stock : ∀i,A.stockAt (.outer p C.mesh.outerFuel) i=b.previous C.mesh (.feed (.outer p))+PurchaseInventory.slot i)
    (i : Commodity (Fin (2^z)) N k) : (A.trial C start p C.mesh.outerFuel).bits i≤ ceiling := by
  obtain ⟨_,cut⟩ := outer_feed_slot C start p phase r.mounted_all
  change ((trialState C start p C.mesh.outerFuel) (A.stockAt _ i)).val≤ ceiling
  rw [stock]
  exact (r.slot cut).1 i

theorem Run.inner_end (r : Run C b start z N k ceiling) (A : AccountColumns (Commodity (Fin (2^z)) N k))
    (p h j : ℕ) (phase : p< C.mesh.inject+C.mesh.cool) (trial : h< C.mesh.outerFuel) (slice : j< C.mesh.reserveSteps)
    (stock : ∀i,A.stockAt (.inner p h j C.mesh.innerFuel) i=b.previous C.mesh (.feed (.inner p h j))+PurchaseInventory.slot i)
    (i : Commodity (Fin (2^z)) N k) : (A.inner C start p h j C.mesh.innerFuel).bits i≤ ceiling := by
  obtain ⟨_,cut⟩ := inner_feed_slot C start p h j phase trial slice r.mounted_all
  change ((innerState C start p h j C.mesh.innerFuel) (A.stockAt _ i)).val≤ ceiling
  rw [stock]
  exact (r.slot cut).1 i

end Hierarchy.ProtocolRAM.Calendar.StockBound
end

end OAI
