import OAI.Computability.BorderVNP.DiagonalExternalFragmentChronology
import OAI.Computability.BorderVNP.DiagonalExternalFragmentPadding

/-! # The complete physical interval stream in dense cell-argument order

After stable bucketing each selected cell contains exactly the source
crossings, destination crossings, and positive literal or pin pieces of
its own supplied bank, ordered at their genuine dense offsets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses Packing.Directory BorderVNP.Cube RoutingISA.SparseExterior
open scoped Classical

variable {D C m R r w link V g entries desc : ℕ}
    (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m)
    (pp lp : ℕ → ℕ × ℕ) (placement : LivePlacement N cell edgeID finProdFinEquiv.toEmbedding lp)
    (supplied : ℕ → ℕ) (counts : ∀ c : Fin C, supplied c.val = suppliedSize N cell c)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    {l : HostScatter.Layout} {mem : ℕ → ℕ} (wires : CableRows N cell edgeID finProdFinEquiv.toEmbedding l mem)
local notation "dir" => freeDirectory R r w link V g entries desc
local notation "base" => fun c => mem (l.cells+2*c+1)
local notation "loads" => Layout.directory (freeDirectory R r w link V g entries desc) pp lp

include placement privateAfter hg room in
private theorem live_placed {q : Quad} (hq : q ∈ liveQuads (dir) pp lp supplied base) :
    ∃ a : FreeBlock R V, let dst := lp (a.1.val*V+a.2.val)
      q.cell = (cell (N.attach a)).val ∧ dst.2 ≤ q.start ∧ q.start+q.width ≤ dst.2+g := by
  obtain ⟨row,hr,hq'⟩ := List.mem_filterMap.mp hq
  obtain ⟨i,hi,hrow,_⟩ := ((dir).mem_directory_iff pp lp row).mp hr
  rw [← hrow] at hq'
  obtain ⟨u,p,f,k,_,rfl'⟩ := retained_live_candidate (dir) pp lp supplied base privateAfter ⟨i,hi⟩ hq'
  rw [rfl'] at hq'
  obtain ⟨site,_,hc,hs,hw,_,hfit⟩ := located_live N cell edgeID lp placement hg room supplied base u p f k hq'
  refine ⟨(u,site),hc,?_,?_⟩
  · rw [placement (u,site),hs]; exact Nat.le_add_right ..
  · rw [placement (u,site),hs,hw]
    change portStart N cell edgeID _ (u,site) rfl+_+_ ≤ portStart N cell edgeID _ (u,site) rfl+g
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left hfit _

include placement privateAfter hg room wires in
private theorem end_before_live (side : Bool) {a b : Quad}
    (ha : a ∈ (List.range l.count).filterMap (cable l mem side))
    (hb : b ∈ liveQuads (dir) pp lp supplied base) (same : a.cell=b.cell) : a.start+a.width ≤ b.start := by
  obtain ⟨i,hi,hq⟩ := List.mem_filterMap.mp ha
  obtain ⟨e,_,_,rfl⟩ := (cable_some_iff wires (List.mem_range.mp hi) side a).mp hq
  obtain ⟨p,hc,hs,_⟩ := live_placed N cell edgeID pp lp placement supplied privateAfter hg room hb
  exact (endpoint_before_free N cell edgeID finProdFinEquiv.toEmbedding placement side e p
    (Fin.ext (same.trans hc))).trans hs

include placement privateAfter hg room wires in
/-- The emitted quadruples in a cell's stable bucket are in the native dense
slab order. Every true cable interval ends before any following live data. -/
theorem stream_ordered (c : ℕ) : (stream l mem supplied loads).Pairwise
    (fun a b => a.cell = c → b.cell = c → a.start+a.width ≤ b.start) := by
  unfold stream
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨cablePass_ordered wires false c,cablePass_ordered wires true c,?_⟩,
    livePass_ordered N cell edgeID pp lp placement supplied base privateAfter hg room c,?_⟩
  · exact fun a ha b hb ac bc => source_dest_ordered wires c ha hb ac bc
  · intro a ha b hb ac bc
    rcases List.mem_append.mp ha with ha | ha
    · exact end_before_live N cell edgeID pp lp placement supplied privateAfter hg room wires false ha hb (ac.trans bc.symm)
    · exact end_before_live N cell edgeID pp lp placement supplied privateAfter hg room wires true ha hb (ac.trans bc.symm)

include placement counts privateAfter hg room wires in
/-- The exact argument of the sparse encoder is ordered and lies within its
real cell's supplied width. In particular an empty cell requires no record. -/
theorem physical_spans_ordered (data : ℕ → ℕ → Bool) (c : Fin C) :
    Ordered (suppliedSize N cell c) 0 (spans (stream l mem supplied loads) data c.val) := by
  apply spans_ordered _ (stream_ordered N cell edgeID pp lp placement supplied privateAfter hg room wires c.val)
  intro q hq hcell
  have endpoint (side : Bool) (hq : q ∈ (List.range l.count).filterMap (cable l mem side)) :
      q.start+q.width ≤ suppliedSize N cell c := by
    obtain ⟨i,hi,hr⟩ := List.mem_filterMap.mp hq
    obtain ⟨e,_,_,he⟩ := (cable_some_iff wires (List.mem_range.mp hi) side q).mp hr
    have atCell : endpointCell N cell side e = c := Fin.ext ((congrArg Quad.cell he).symm.trans hcell)
    rw [he,← atCell]
    exact endpointRow_fits N cell edgeID finProdFinEquiv.toEmbedding side e
  rcases List.mem_append.mp hq with ends | datum
  · rcases List.mem_append.mp ends with h | h
    · exact endpoint false h
    · exact endpoint true h
  · obtain ⟨a,hc,_,hs⟩ := live_placed N cell edgeID pp lp placement supplied privateAfter hg room datum
    have cap := live_base_fits N cell edgeID finProdFinEquiv.toEmbedding placement supplied counts a
    have placed := placement a
    have placeCell : (lp (a.1.val*V+a.2.val)).1 = c.val := (congrArg Prod.fst placed).trans (hc.symm.trans hcell)
    dsimp only at cap
    rw [placeCell,counts] at cap
    exact hs.trans cap

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
