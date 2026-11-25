import OAI.Computability.BorderVNP.DiagonalExternalFragmentEndData

/-! # Reading the actual sparse source operands in the receiving team's memory

The physical directory uses one absolute source pointer per interval. Crossing
bits at that pointer must be the selected end of the routed assignment; the
two free fields must be the actual substituted bit and programmed literal.
Each owner only reads the spans of its assigned cells.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses Packing.Directory BorderVNP.Cube Cube.Physical
open RoutingISA RoutingISA.SparseExterior VPVNP.BurstRAM
open scoped Classical

variable {D R r w link V g C m n : ℕ} (N : Network D (FreeBlock R V) (fun _ => g))
    (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)
    (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g) (lp : ℕ → ℕ × ℕ)
    (origin stride : ℕ) (input : FreePort R r w → Bool) (ends : Bool → LiveBit N cell → Bool)

/-- Physical source-word readback at the actual owner of each cell. Only bits
present in the chronological fragment stream require a memory read. -/
structure SourceWords (mem : Fin C → ℕ → ℕ) : Prop where
  crossing : ∀ (side : Bool) (e : N.CrossingEdge cell) (j : Fin (N.width e.val)),
    let c := endpointCell N cell side e
    mem c (origin+c.val*stride+endpointRow N cell edgeID portID side e+j.val) = (ends side ⟨e,j⟩).toNat
  free : ∀ z : FreePort R r w,
    let a := freeLane hg room z
    let c := cell (N.attach a.1)
    mem c (origin+c.val*stride+(laneAddress lp a).2) = (input z).toNat

local notation "bank" => fillFree hg room input (fun _ => false)
local notation "data" => endData N cell edgeID portID bank ends

/-- Protected subsequent stores transport true source readbacks without
requiring any protected address in another team's memory. -/
theorem SourceWords.protected {before after : Fin C → ℕ → ℕ}
    (words : SourceWords N cell edgeID portID hg room lp origin stride input ends before)
    (placement : LivePlacement N cell edgeID portID lp)
    (keep : ∀ c, ∀ j < suppliedSize N cell c, after c (origin+c.val*stride+j) = before c (origin+c.val*stride+j)) :
    SourceWords N cell edgeID portID hg room lp origin stride input ends after := by
  constructor
  · intro side e j c
    let k := endpointRow N cell edgeID portID side e
    have hk : k+j.val < suppliedSize N cell c :=
      (Nat.add_lt_add_left j.isLt _).trans_le (endpointRow_fits N cell edgeID portID side e)
    have move := keep c (k+j.val) hk
    rw [←Nat.add_assoc] at move
    exact move.trans (words.crossing side e j)
  · intro z a c
    have addr := placedOrdinal N cell edgeID portID placement c ⟨a.1,rfl⟩ a.2
    have fit : (laneAddress lp a).2 < suppliedSize N cell c := by rw [addr]; exact Fin.isLt _
    exact (keep c _ fit).trans (words.free z)

variable {W entries desc : ℕ} (pp : ℕ → ℕ × ℕ) (supplied : ℕ → ℕ)
    (placement : LivePlacement N cell edgeID portID lp)
    (counts : ∀ c : Fin C, supplied c.val = suppliedSize N cell c)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    {l : HostScatter.Layout} {geo : ℕ → ℕ} (rows : CableRows N cell edgeID portID l geo)
    (bases : ∀ c : Fin C, geo (l.cells+2*c.val+1) = origin+c.val*stride)
    {actual : Fin C → Memory W}
    (words : SourceWords N cell edgeID portID hg room lp origin stride input ends (fun c => readings (actual c)))

local notation "dir" => freeDirectory R r w link V g entries desc
local notation "quads" => stream l geo supplied (Layout.directory dir pp lp)

include rows placement counts privateAfter bases words in
/-- Every physical source word in a selected cell's span list contains the
Boolean bit of that cell's canonical supplied evaluator operand. -/
theorem spans_source_reads (c : Fin C) : ∀ s ∈ spans quads data c.val, s.Reads (actual c) := by
  intro s mems
  obtain ⟨q,mq,rfl⟩ := List.mem_map.mp mems
  obtain ⟨hit,own⟩ := List.mem_filter.mp mq
  have hc : q.cell = c.val := of_decide_eq_true own
  apply Quad.span_reads
  intro j
  have cross (side : Bool) (inPass : q ∈ (List.range l.count).filterMap (cable l geo side)) :
      (actual c (q.source+j.val)).val = ((data) q.cell (q.start+j.val)).toNat := by
    obtain ⟨k,hk,source⟩ := List.mem_filterMap.mp inPass
    obtain ⟨e,_,_,eq⟩ := (cable_some_iff rows (List.mem_range.mp hk) side q).mp source
    subst q
    let v := endpointCell N cell side e
    have name : v = c := Fin.ext hc
    subst c
    change readings (actual v) (geo (l.cells+2*v.val+1)+endpointRow N cell edgeID portID side e+j.val) =
      ((data) v.val (endpointRow N cell edgeID portID side e+j.val)).toNat
    rw [bases]
    exact (words.crossing side e j).trans (congrArg Bool.toNat (endData_endpoint N cell edgeID portID bank ends side e j).symm)
  rcases List.mem_append.mp hit with h | h
  · rcases List.mem_append.mp h with h | h
    · exact cross false h
    · exact cross true h
  · let base := fun c => geo (l.cells+2*c+1)
    have loc := (stream_located l geo supplied (Layout.directory dir pp lp) q (List.mem_append_right _ h)).2
    obtain ⟨z,address⟩ := (liveQuads_atBit_iff hg room pp lp supplied base privateAfter
      (live_base_fits N cell edgeID portID placement supplied counts) (q.atBit j)).mp
      ⟨q,(show q ∈ liveQuads (dir) pp lp supplied base from h),j,rfl⟩
    let a := freeLane hg room z
    let v := cell (N.attach a.1)
    have owner := congrArg Prod.fst address
    have disp := congrArg Prod.snd address
    change (lp (a.1.1.val*V+a.1.2.val)).1 = q.cell at owner
    change (laneAddress lp a).2 = q.start+j.val at disp
    have hv := congrArg Prod.fst (placement a.1)
    change (lp (a.1.1.val*V+a.1.2.val)).1 = v.val at hv
    have hcell := Fin.ext ((hv.symm.trans owner).trans hc)
    have atBit := endData_group N cell edgeID portID placement bank ends a
    rw [address] at atBit
    change (data) q.cell (q.start+j.val) = (bank) a.1 a.2 at atBit
    have bit := fillFree_read hg room input (fun _ => false) z
    change (bank) a.1 a.2 = input z at bit
    rw [atBit,bit,loc,hc,bases,Nat.add_assoc,←disp,←hcell]
    exact words.free z

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
