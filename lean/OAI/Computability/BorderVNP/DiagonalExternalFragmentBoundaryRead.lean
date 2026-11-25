import OAI.Computability.BorderVNP.DiagonalExternalFragmentCableMemory
import OAI.Computability.BorderVNP.DiagonalExternalFragmentRestore

/-! # Decoding every actual crossing-wire lane of a supplied cell

The native fragment has an absolute pointer to the same bit whose local
address is the canonical typed supplied ordinal of the evaluator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.Directory Packing.CellAddresses BorderVNP.Cube RoutingISA.SparseExterior
open private ordinal_val from OAI.Computability.BorderVNP.DiagonalExternalFragmentCables
open scoped Classical

variable {D C m n : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} {cell : N.Site → Fin C} {edgeID : N.Edge ↪ Fin m} {portID : P ↪ Fin n}
    {l : HostScatter.Layout} {mem : ℕ → ℕ} (rows : CableRows N cell edgeID portID l mem)
    (supplied : ℕ → ℕ) (deliveries : List Row) (data : ℕ → ℕ → Bool)

include rows

/-- Each actual crossing bit occurs in the complete three-pass stream of
its cell, at its evaluator ordinal and at the host's absolute data pointer. -/
theorem spans_boundary_lane (c : Fin C) (u : Boundary N cell c) (j : Fin (N.width u.val.val)) :
    let pos := (suppliedOrdinal N cell c edgeID portID (.inl u) j).val
    ∃ s ∈ spans (stream l mem supplied deliveries) data c.val, ∃ i : Fin s.bits.length,
      s.start+i.val = pos ∧ s.source+i.val = mem (l.cells+2*c.val+1)+pos ∧ s.bits[i.val] = data c.val pos := by
  intro pos
  obtain ⟨side,here⟩ : ∃ side : Bool, endpointCell N cell side u.val = c := by
    rcases u.property with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  let q := actualQuad N cell edgeID portID l mem side u.val
  have hq := cablePass_cover rows side u.val (Nat.zero_lt_of_lt j.isLt)
  have member : q ∈ stream l mem supplied deliveries := by
    apply List.mem_append_left
    cases side
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ hq
  have atCell : q.cell = c.val := congrArg Fin.val here
  have atBit : q.start+j.val = pos := by
    rw [show q.start = endpointRow N cell edgeID portID side u.val from rfl,
      endpointRow_at N cell edgeID portID c side u.val here]
    exact (ordinal_val N cell edgeID portID c (.inl u) j).symm
  have len : (q.span data).bits.length = q.width := by simp [Quad.span]
  have loc := (stream_located l mem supplied deliveries q member).2
  refine ⟨q.span data,List.mem_map.mpr ⟨q,List.mem_filter.mpr ⟨member,by simp [atCell]⟩,rfl⟩,
    ⟨j.val,j.isLt.trans_eq len.symm⟩,atBit,?_,?_⟩
  · change q.source+j.val = _
    rw [loc,atCell,Nat.add_assoc,atBit]
  · simp [Quad.span,atCell,atBit]

/-- Reading the private expanded bank at a crossing lane yields exactly
the bit supplied to the physical evaluator at that typed address. -/
theorem expand_boundary_lane_read (c : Fin C) (u : Boundary N cell c) (j : Fin (N.width u.val.val))
    (tail : List Bool) :
    let pos := (suppliedOrdinal N cell c edgeID portID (.inl u) j).val
    let ss := spans (stream l mem supplied deliveries) data c.val
    Ordered (supplied c.val) 0 ss → (expand (supplied c.val) tail 0 ss)[pos]? = some (data c.val pos) := by
  intro pos ss order
  obtain ⟨s,hs,i,addr,_,bit⟩ := spans_boundary_lane rows supplied deliveries data c u j
  have read := expand_span_read (supplied c.val) tail order (show s ∈ ss from hs) i
  simpa only [Nat.sub_zero,addr,bit] using read

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
