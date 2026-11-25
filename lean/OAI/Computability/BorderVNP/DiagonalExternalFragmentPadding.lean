import OAI.Computability.BorderVNP.DiagonalExternalFragmentRestore
import OAI.Computability.BorderVNP.DiagonalExternalFragmentCables

/-! # Grouped port coverage in the complete physical sparse stream

Crossing-cable words precede every grouped external port in a cell. Hence the
live delivery pass completely determines which lanes of a grouped port are
represented, and the private sparse decoder inserts zero in every other lane.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.Directory Packing.CellAddresses BorderVNP.Cube RoutingISA.SparseExterior
open private end_le_start from OAI.Computability.BorderVNP.PackedCellSlabs
open scoped Classical

variable {D R V g C m n : ℕ} (N : Network D (FreeBlock R V) (fun _ => g))
    (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)
    {lp : ℕ → ℕ × ℕ} (place : LivePlacement N cell edgeID portID lp)

include place in
/-- In the actual bank a crossing word is completely before any grouped port
attached to that same cell, for either orientation. -/
theorem endpoint_before_free (side : Bool) (e : N.CrossingEdge cell) (a : FreeBlock R V)
    (here : endpointCell N cell side e = cell (N.attach a)) :
    endpointRow N cell edgeID portID side e+N.width e.val ≤ (lp (a.1.val*V+a.2.val)).2 := by
  let c := cell (N.attach a)
  let first := endpointWord N cell c side e here
  let last : Supplied N cell c := .inr ⟨a,rfl⟩
  have order : suppliedRow N cell c edgeID portID first < suppliedRow N cell c edgeID portID last := by
    rw [endpointWord_id]
    change (if side then m else 0)+(edgeID e.val).val < (m+m)+(portID a).val
    have := (edgeID e.val).isLt
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  rw [endpointRow_at N cell edgeID portID c side e here,place a]
  exact end_le_start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) order

variable {l : HostScatter.Layout} {mem : ℕ → ℕ} (rows : CableRows N cell edgeID portID l mem)

include place rows in
/-- A bit in either physical cable pass cannot alias a bit of a free word. -/
theorem cable_not_free_lane (side : Bool) {q : Quad} (hq : q ∈ (List.range l.count).filterMap (cable l mem side))
    (i : Fin q.width) (a : Σ _ : FreeBlock R V, Fin g) : q.atBit i ≠ laneAddress lp a := by
  obtain ⟨k,hk,lookup⟩ := List.mem_filterMap.mp hq
  obtain ⟨e,_,_,rfl⟩ := (cable_some_iff rows (List.mem_range.mp hk) side q).mp lookup
  intro hit
  have hc := congrArg Prod.fst hit
  change (endpointCell N cell side e).val = (lp (a.1.1.val*V+a.1.2.val)).1 at hc
  have source := congrArg Prod.fst (place a.1)
  have here := Fin.ext (hc.trans source)
  have hprior := endpoint_before_free N cell edgeID portID place side e a.1 here
  have hs := congrArg Prod.snd hit
  change endpointRow N cell edgeID portID side e+i.val = (lp (a.1.1.val*V+a.1.2.val)).2+a.2.val at hs
  have hi : i.val < N.width e.val := i.isLt
  omega

variable {r w link entries desc : ℕ}
local notation "dir" => freeDirectory R r w link V g entries desc

include rows in
/-- In the complete three-pass stream a grouped lane is present if and only
if it is a physical literal or pin port. -/
theorem stream_lane_iff (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (pp suppliedCell : ℕ → ℕ × ℕ) (livePlace : LivePlacement N cell edgeID portID suppliedCell)
    (supplied : ℕ → ℕ) (counts : ∀ c : Fin C, supplied c.val = suppliedSize N cell c)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (a : Σ _ : FreeBlock R V, Fin g) :
    (∃ q ∈ stream l mem supplied ((dir).directory pp suppliedCell), ∃ i : Fin q.width,
      q.atBit i = laneAddress suppliedCell a) ↔ ∃ z : FreePort R r w, freeLane hg room z = a := by
  let base := fun c => mem (l.cells+2*c+1)
  have data := liveQuads_lane_iff (desc := desc) N cell edgeID portID hg room pp suppliedCell supplied base
    privateAfter livePlace counts a
  constructor
  · rintro ⟨q,memq,i,h⟩
    rcases List.mem_append.mp memq with hc | hd
    · rcases List.mem_append.mp hc with hs | ht
      · exact ((cable_not_free_lane N cell edgeID portID livePlace rows false hs i a) h).elim
      · exact ((cable_not_free_lane N cell edgeID portID livePlace rows true ht i a) h).elim
    · exact data.mp ⟨q,hd,i,h⟩
  · intro h
    obtain ⟨q,hq,i,eq⟩ := data.mpr h
    exact ⟨q,List.mem_append_right _ hq,i,eq⟩

/-- Stable bucketing retains exactly the bit positions at the selected cell. -/
theorem spans_atBit_iff (qs : List Quad) (data : ℕ → ℕ → Bool) (addr : ℕ × ℕ) :
    (∃ s ∈ spans qs data addr.1, ∃ i : Fin s.bits.length, s.start+i.val = addr.2) ↔
      ∃ q ∈ qs, ∃ j : Fin q.width, q.atBit j = addr := by
  constructor
  · rintro ⟨s,mems,i,hi⟩
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp mems
    obtain ⟨member,atCell⟩ := List.mem_filter.mp hq
    exact ⟨q,member,⟨i.val,by simpa [Quad.span] using i.isLt⟩,Prod.ext (of_decide_eq_true atCell) hi⟩
  · rintro ⟨q,hq,j,eq⟩
    have c := congrArg Prod.fst eq
    change q.cell = addr.1 at c
    refine ⟨q.span data,List.mem_map.mpr ⟨q,List.mem_filter.mpr ⟨hq,by simp [c]⟩,rfl⟩,
      ⟨j.val,by simp [Quad.span]⟩,?_⟩
    exact congrArg Prod.snd eq

include rows in
/-- After the actual sparse decoder has expanded the full physical stream,
all omitted lanes of the grouped words read zero, including exterior-field
gaps and the unused end of the final tile. -/
theorem expand_unused_lane (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (pp suppliedCell : ℕ → ℕ × ℕ) (livePlace : LivePlacement N cell edgeID portID suppliedCell)
    (supplied : ℕ → ℕ) (counts : ∀ c : Fin C, supplied c.val = suppliedSize N cell c)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (data : ℕ → ℕ → Bool) (tail : List Bool) (a : Σ _ : FreeBlock R V, Fin g)
    (unused : a ∉ Set.range (freeLane hg room)) :
    let addr := laneAddress suppliedCell a
    let qs := stream l mem supplied ((dir).directory pp suppliedCell)
    let ss := spans qs data addr.1
    Ordered (supplied addr.1) 0 ss → (expand (supplied addr.1) tail 0 ss)[addr.2]? = some false := by
  intro addr qs ss order
  have noSpan : ¬∃ s ∈ ss, ∃ i : Fin s.bits.length, s.start+i.val = addr.2 := by
    rw [spans_atBit_iff qs data addr,stream_lane_iff (desc := desc) N cell edgeID portID rows hg room
      pp suppliedCell livePlace supplied counts privateAfter a]
    exact unused
  have cap := live_base_fits N cell edgeID portID livePlace supplied counts a.1
  have hi : addr.2 < supplied addr.1 := (Nat.add_lt_add_left a.2.isLt _).trans_le cap
  have missed (s : Span) (hs : s ∈ ss) : ¬(s.start ≤ addr.2 ∧ addr.2 < s.stop) := by
    rintro ⟨lo,upper⟩
    change addr.2 < s.start+s.bits.length at upper
    exact noSpan ⟨s,hs,⟨addr.2-s.start,by omega⟩,Nat.add_sub_of_le lo⟩
  simpa only [Nat.sub_zero] using expand_gap_read (supplied addr.1) tail order (Nat.zero_le addr.2) hi missed

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
