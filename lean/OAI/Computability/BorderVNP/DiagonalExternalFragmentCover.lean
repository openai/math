import OAI.Computability.BorderVNP.DiagonalExternalFragmentLanes

/-! # Exact coverage of the live literal and secondary-pin fragment pass

The compact delivery scan visits every genuinely used free lane. Its surviving
rows cover only these lanes: reserved private metadata, exterior-field gaps,
and the unused suffix of the last site block supply no fragment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.Directory Packing.CellAddresses BorderVNP.Cube RoutingISA RoutingISA.SparseExterior
open scoped Classical

/-- Logical bit position in the final cell's supplied interval. -/
def Quad.atBit (q : Quad) (i : Fin q.width) : ℕ × ℕ := (q.cell,q.start+i.val)

variable {R r w link V g entries desc : ℕ}
local notation "D" => freeDirectory R r w link V g entries desc

/-- The third pass of the physical stream, after removing private descriptions. -/
def liveQuads (d : Layout) (pp lp : ℕ → ℕ × ℕ) (supplied base : ℕ → ℕ) :=
  (d.directory pp lp).filterMap (live supplied base)

private theorem cover_field (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (pp lp : ℕ → ℕ × ℕ) (supplied base : ℕ → ℕ)
    (fit : ∀ a : FreeBlock R V, let dest := lp (a.1.val*V+a.2.val); dest.2+g ≤ supplied dest.1)
    (t : Fin (R+1)) (p : Fin r) (f : Fin 2) (j : Fin w) :
    ∃ q ∈ liveQuads D pp lp supplied base, ∃ i : Fin q.width,
      q.atBit i = laneAddress lp (freeLane hg room (fromField t p f j)) := by
  let a := freeLane hg room (fromField t p f j)
  let dest := lp (a.1.1.val*V+a.1.2.val)
  obtain ⟨row,member,e,he,_,_,_,_,hc,hs⟩ := freeLane_delivered hg room entries desc pp lp t p f j
  change row.cell = dest.1 at hc
  change row.slot+e = dest.2+a.2.val at hs
  have fits : dest.2+g ≤ supplied dest.1 := fit a.1
  have hslot : row.slot < supplied row.cell := by
    rw [hc]
    have := a.2.isLt
    omega
  let q : Quad := ⟨row.cell,row.slot,base row.cell+row.slot,row.width⟩
  have accepted : live supplied base row = some q := ite_eq_left ⟨hslot,Nat.zero_lt_of_lt he⟩
  exact ⟨q,List.mem_filterMap.mpr ⟨row,member,accepted⟩,⟨e,he⟩,Prod.ext hc hs⟩

/-- The compact scan contains a fragment for every original surviving argument. -/
theorem cover_free (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (pp lp : ℕ → ℕ × ℕ) (supplied base : ℕ → ℕ)
    (fit : ∀ a : FreeBlock R V, let dest := lp (a.1.val*V+a.2.val); dest.2+g ≤ supplied dest.1)
    (z : FreePort R r w) :
    ∃ q ∈ liveQuads D pp lp supplied base, ∃ i : Fin q.width,
      q.atBit i = laneAddress lp (freeLane hg room z) := by
  rcases z with ⟨t,p,j|j⟩
  · exact cover_field hg room pp lp supplied base fit t p 0 j
  · exact cover_field hg room pp lp supplied base fit t p 1 j

/-- An address is emitted by the populated delivery pass exactly when it is
the address of a surviving literal or pin bit. -/
theorem liveQuads_atBit_iff (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (pp lp : ℕ → ℕ × ℕ) (supplied base : ℕ → ℕ)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (fit : ∀ a : FreeBlock R V, let dest := lp (a.1.val*V+a.2.val); dest.2+g ≤ supplied dest.1)
    (y : ℕ × ℕ) :
    (∃ q ∈ liveQuads D pp lp supplied base, ∃ i : Fin q.width, q.atBit i = y) ↔
      ∃ z : FreePort R r w, laneAddress lp (freeLane hg room z) = y := by
  constructor
  · rintro ⟨q,hq,i,rfl⟩
    obtain ⟨row,member,accepted⟩ := List.mem_filterMap.mp hq
    obtain ⟨index,hi,hrow,_⟩ := ((D).mem_directory_iff pp lp row).mp member
    let n : Fin (D).candidates := ⟨index,hi⟩
    have eq : (D).row pp lp n = row := hrow
    have h := retained_live_candidate D pp lp supplied base privateAfter n (eq ▸ accepted)
    obtain ⟨t,p,f,k,_,source⟩ := h
    obtain rfl := (eq.symm.trans source)
    unfold live at accepted
    split at accepted
    · obtain rfl := Option.some.inj accepted
      obtain ⟨j,_,pos⟩ := live_row_lane (entries := entries) (desc := desc) hg room lp t p f k i
      exact ⟨fromField t p f j,pos.symm⟩
    · cases accepted
  · rintro ⟨z,rfl⟩
    exact cover_free hg room pp lp supplied base fit z

variable {dim C m n : ℕ} (N : Network dim (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)

/-- At the true live placement even a padded grouped word that shares a cell
with many other words has fragments precisely on the lanes in the free-port
embedding. -/
theorem liveQuads_lane_iff (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (pp lp : ℕ → ℕ × ℕ) (supplied base : ℕ → ℕ)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (place : LivePlacement N cell edgeID portID lp)
    (counts : ∀ c : Fin C, supplied c.val = suppliedSize N cell c) (a : Σ _ : FreeBlock R V, Fin g) :
    (∃ q ∈ liveQuads D pp lp supplied base, ∃ i : Fin q.width, q.atBit i = laneAddress lp a) ↔
      ∃ z : FreePort R r w, freeLane hg room z = a := by
  rw [liveQuads_atBit_iff hg room pp lp supplied base privateAfter
    (live_base_fits N cell edgeID portID place supplied counts)]
  exact exists_congr fun z => (laneAddress_injective N cell edgeID portID place).eq_iff

/-- Specialization to the actual native private-table image. Its owner and slot words
supply the separation required by the filter. -/
theorem liveQuads_native_lane_iff {W : ℕ} (l : PrivatePlacement.Layout) (before after : ℕ → ℕ)
    (image : l.Image before l.entries after) (valid : l.Fits W before)
    (oldCell : Fin l.entries → Fin C)
    (owners : ∀ j : Fin l.entries, l.owner before j.val = (oldCell j).val)
    (stored : ∀ c : Fin C, before (l.supplied+c.val) = suppliedSize N cell c)
    (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g) (lp : ℕ → ℕ × ℕ) (supplied base : ℕ → ℕ)
    (place : LivePlacement N cell edgeID portID lp)
    (counts : ∀ c : Fin C, supplied c.val = suppliedSize N cell c) (a : Σ _ : FreeBlock R V, Fin g) :
    (∃ q ∈ liveQuads (freeDirectory R r w link V g l.entries l.desc) (ISA.placement after l.raw) lp supplied base,
      ∃ i : Fin q.width, q.atBit i = laneAddress lp a) ↔ ∃ z : FreePort R r w, freeLane hg room z = a := by
  exact liveQuads_lane_iff N cell edgeID portID hg room _ lp supplied base
    (private_after_of_image l before after supplied image valid (fun j => by rw [owners j,stored,counts]))
    place counts a

/-- Every used free lane occurs in the stable per-cell span list extracted from
the full three-pass stream. Its fragment reads the addressed bit of the dense
received data at the cell's actual absolute bank pointer. -/
theorem spans_free_lane (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (pp lp : ℕ → ℕ × ℕ) (supplied : ℕ → ℕ)
    (fit : ∀ a : FreeBlock R V, let dest := lp (a.1.val*V+a.2.val); dest.2+g ≤ supplied dest.1)
    (l : HostScatter.Layout) (m : ℕ → ℕ) (data : ℕ → ℕ → Bool) (z : FreePort R r w) :
    let pos := laneAddress lp (freeLane hg room z)
    ∃ s ∈ spans (stream l m supplied ((D).directory pp lp)) data pos.1, ∃ i : Fin s.bits.length,
      s.start+i.val = pos.2 ∧ s.source+i.val = m (l.cells+2*pos.1+1)+pos.2 ∧
      s.bits[i.val] = data pos.1 pos.2 := by
  intro pos
  let base := fun c => m (l.cells+2*c+1)
  obtain ⟨q,hq,i,he⟩ := cover_free (entries := entries) (desc := desc) hg room pp lp supplied base fit z
  change q.atBit i = pos at he
  have mem : q ∈ stream l m supplied ((D).directory pp lp) := List.mem_append_right _ hq
  have located := (stream_located l m supplied _ q mem).2
  have hc : q.cell = pos.1 := congrArg Prod.fst he
  have hs : q.start+i.val = pos.2 := congrArg Prod.snd he
  have len : (q.span data).bits.length = q.width := by simp [Quad.span]
  refine ⟨q.span data,List.mem_map.mpr ⟨q,List.mem_filter.mpr ⟨mem,by simp [hc]⟩,rfl⟩,
    ⟨i.val,i.isLt.trans_eq len.symm⟩,hs,?_,?_⟩
  · change q.source+i.val = _
    rw [located,hc,Nat.add_assoc,hs]
  · simp [Quad.span,hc,hs]

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
