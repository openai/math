import OAI.Hierarchy.ProbeCoreCongestion
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices
import OAI.Hierarchy.ProtocolRAMCalendarHeldStock

namespace OAI
/-! # Static widths for earlier spill rows and held commodity rows at every calendar prefix -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage
open scoped BigOperators Fin.CommRing Classical
noncomputable section
variable {w h d k n edges q goods : ℕ} {S : PurchaseSampler}

theorem occurrences_map {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A ↪ B) (xs : List A) (a : A) :
    CoreBoard.occurrences (f a) (xs.map f)=CoreBoard.occurrences a xs :=
  List.count_map_of_injective xs _ f.injective a

/-- A typed core walk is placed inside the full physical reporter, which may
also contain purchased rows. The measured upper bound is zero on every row
outside the embedded core. The source bank can be any numbering of commodities. -/
theorem mapped_core_bound (π : Equiv.Perm (Fin (2^h))) (label : CoreBoard.Edges S h d k ↪ Fin edges)
    (idx : Fin n ≃ Commodity (Fin (2^h)) (CoreBoard.Stages h d) k) (bits : Fin n→ℕ) (B : ℕ)
    (bound : ∀i,bits i≤B) (e : Fin edges) :
    routeLoad (fun j=>(CoreBoard.commodityWalk (S:=S) π (idx j)).map label) bits e≤
      (1+CoreBoard.Stages h d*(2*k))*((2*CoreBoard.Stages h d+2)*B) := by
  by_cases inCore : ∃ b,label b=e
  · obtain ⟨b,rfl⟩ := inCore
    have measured := CoreBoard.core_load_bound π b (fun i=>bits (idx.symm i)) B (fun i=>bound _)
    unfold routeLoad at measured ⊢
    change (∑ j,CoreBoard.occurrences (label b) ((CoreBoard.commodityWalk (S:=S) π (idx j)).map label)*bits j)≤_
    have same := idx.sum_comp (fun i=>CoreBoard.occurrences b (CoreBoard.commodityWalk (S:=S) π i)*bits (idx.symm i))
    simp only [Equiv.symm_apply_apply] at same
    simp only [occurrences_map,same]
    exact measured
  · have zero (i : Fin n) : e∉(CoreBoard.commodityWalk (S:=S) π (idx i)).map label := by
      intro yes; obtain ⟨a,_,eq⟩ := List.mem_map.mp yes; exact inCore ⟨a,eq⟩
    simp [routeLoad,fun i=>List.count_eq_zero.mpr (zero i)]

/-- Native price-out spill load measured at the actual runtime core-edge row. -/
theorem Traversals.core_spill_bound (t : Traversals) (a : StockCommit.Area) (m : Memory w) (e : Fin edges)
    (π : Equiv.Perm (Fin (2^h))) (label : CoreBoard.Edges S h d k ↪ Fin edges)
    (idx : Fin a.goods ≃ Commodity (Fin (2^h)) (CoreBoard.Stages h d) k) (B : ℕ)
    (locations : t.Reads m (fun j=>(CoreBoard.commodityWalk (S:=S) π (idx j)).map label))
    (cap : ∀i:Fin a.goods,(m (a.output+a.goods+a.goods+i.val)).val≤B) :
    (PaidWidths.paidSpill a t.positions t.owner t.parity t.edge t.sourceRow).load m e≤
      (1+CoreBoard.Stages h d*(2*k))*((2*CoreBoard.Stages h d+2)*B) := by
  let walk := fun i : Fin a.goods=>(CoreBoard.commodityWalk (S:=S) π (idx i)).map label
  let bit := fun i : Fin a.goods=>(m (a.output+a.goods+a.goods+i.val)).val
  have read (i : Fin t.positions) := congrArg Fin.val
    (PaidWidths.paidSpill_bits a t.positions t.owner t.parity t.edge t.sourceRow m (i.val:Word w) (locations.enum i).1 (locations.ownerAt i))
  rw [PaidWidths.walks_load _ m e walk bit locations.enum locations.edgeAt read]
  exact mapped_core_bound π label idx bit B cap e

/-- All affordable calendar lengths precede the input width. This is a bound on
one physical edge's running archive, including any prefix ending at a feed. -/
theorem paid_history_prefix (mesh : Mesh) (slices : Event→List PaidWidths.Slice) (m : Memory w)
    (e : Fin edges) (C width stop : ℕ) (per : ∀t∈events mesh,PaidWidths.total (slices t) m e≤C*width) :
    PaidWidths.total (((events mesh).take stop).flatMap slices) m e ≤
      ((mesh.inject+mesh.cool)*(mesh.outerFuel*(1+mesh.reserveSteps*(mesh.innerFuel+1))+1)*C)*width := by
  have scan (xs : List Event) (inside : ∀t∈xs,t∈events mesh) :
      PaidWidths.total (xs.flatMap slices) m e≤xs.length*(C*width) := by
    induction xs with
    | nil => simp [PaidWidths.total]
    | cons t rest ih =>
      have now := per t (inside _ (by simp))
      have later := ih (fun u hu=>inside _ (by simp [hu]))
      change _ ≤ (rest.length+1)*(C*width)
      simpa only [List.flatMap_cons,PaidWidths.total,List.map_append,List.sum_append,Nat.succ_mul,Nat.add_comm (C*width)] using Nat.add_le_add now later
  have bound := scan ((events mesh).take stop) fun t ht=>List.mem_of_mem_take ht
  have len : ((events mesh).take stop).length≤(events mesh).length := by simp
  have full := bound.trans (Nat.mul_le_mul_right _ len)
  simpa only [event_count,Nat.mul_assoc] using full

/-- Maximum pre-feed commodity aperture. The calendar can hold the as-yet
uninjected payload and the undelivered reserve simultaneously with the current
active stock. Only one original reserve is held, regardless of remaining slices. -/
theorem commodity_held_cap (mesh : Mesh) (width cap p j a reserve : ℕ) (i : Commodity (Fin (2^h)) n k)
    (buy : Bool) (ac : a≤cap*width) (rc : reserve≤cap*width) :
    a+held mesh.inject width p*payloadUnit i+(if buy then held mesh.reserveSteps reserve j else 0)≤(2*cap+1)*width := by
  have initial : held mesh.inject width p≤width := Nat.sub_le ..
  have remaining : held mesh.reserveSteps reserve j≤cap*width := (Nat.sub_le ..).trans rc
  rw [Nat.add_mul,Nat.one_mul,show 2*cap*width=cap*width+cap*width by ring]
  rcases i with b|a <;> cases buy <;> simp [payloadUnit] <;> omega

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
