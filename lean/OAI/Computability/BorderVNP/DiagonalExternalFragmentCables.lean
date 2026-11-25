import OAI.Computability.BorderVNP.DiagonalExternalFragmentCableOrder
import OAI.Computability.BorderVNP.PackedRoutingImage
import OAI.Computability.BorderVNP.PackedCablePhysical

/-! # The actual crossing cables in the public fragment stream

A positive cable triple at a sparse ID is read on each of the two passes.
Its relative address is the start of the corresponding supplied word in
that endpoint's cell. The absolute data address uses the cell-bank base
in the current host memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical
open Packing.RoutingOutputs BorderVNP.Cube RoutingISA ParseBatchSort
open scoped Classical

variable {D C m n : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (l : HostScatter.Layout) (mem : ℕ → ℕ)

/-- The four words of a real crossing-end descriptor, at the actual native
base for its receiving cell. -/
noncomputable def actualQuad (side : Bool) (e : N.CrossingEdge cell) : Quad :=
  let c := (endpointCell N cell side e).val
  let start := endpointRow N cell edgeID portID side e
  ⟨c,start,mem (l.cells+2*c+1)+start,N.width e.val⟩

/-- Geometry semantics of the two cable passes on a concrete post-write
memory. Every occupied and vacant sparse ordinal is accounted for. -/
structure CableRows : Prop where
  /-- The loops visit the complete sparse geometry rectangle. -/
  count : l.count = m
  /-- Each real crossing end reads its true ordinal, span and bank pointer. -/
  crossing : ∀ side (e : N.CrossingEdge cell), cable l mem side (edgeID e.val).val =
    if 0 < N.width e.val then some (actualQuad N cell edgeID portID l mem side e) else none
  /-- Internal wires and vacant ordinals contribute no fragment. -/
  unused : ∀ side (i : Fin m), i ∉ Set.range (CableTriples.wireOrd N cell edgeID) →
    cable l mem side i.val = none

variable {s d k w J A : ℕ} (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ) {x : σ → Bool}
    {old : Fin J → Fin s} {ports : Fin A → Fin n} {origin : ℕ} {geo : ℕ → ℕ}

private theorem ordinal_val (c : Fin C) (u : Supplied N cell c) (j : Fin (suppliedWidth N cell c u)) :
    (suppliedOrdinal N cell c edgeID portID u j).val =
      CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) u + j.val := by
  dsimp only [suppliedOrdinal,CellSlabs.ordinal,Equiv.ofBijective,Equiv.coe_fn_mk,CellSlabs.start]
  apply congrArg (· + j.val)
  exact Finset.sum_congr (Finset.ext fun _ => by simp) (fun _ _ => rfl)

/-- The full typed cable image follows from the exported geometry fields and
preservation of their five cable words per sparse slot through later writes. -/
theorem CableRows.ofImage (rep : Represents N cell aux siteID edgeID portID F x)
    (codes : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (img : Image F old ports x origin geo) (triples : l.cables = origin)
    (ends : l.relative = (bases origin m C J).ends) (count : l.count = m)
    (keep : ∀ a, origin ≤ a → a < origin+5*m → mem a = geo a) :
    CableRows N cell edgeID portID l mem := by
  have col (i : Fin m) (j : Fin 3) :
      mem (l.cables+3*i.val+j.val) = CableTriples.get (CableTriples.row F x i) j := by
    rw [triples,Nat.mul_comm 3,keep _ (by omega) (by have := i.isLt; have := j.isLt; omega)]
    exact img.cable i j
  have off (i : Fin m) (j : Fin 2) :
      mem (l.relative+2*i.val+j.val) =
        value fun b => (SuppliedOffsets.frame F).eval x (.inl (endpoint i j),b) := by
    rw [ends,Nat.mul_comm 2,keep _ (by dsimp [bases]; omega) (by dsimp [bases]; have := i.isLt; have := j.isLt; omega)]
    exact img.endAt i j
  refine ⟨count,?_,?_⟩
  · intro side e
    let i := edgeID e.val
    have raw := CableTriples.row_crossing N cell aux siteID edgeID portID F rep codes e
    change CableTriples.row F x i = _ at raw
    have wid : l.width mem i.val = (CableTriples.row F x i).width := col i 2
    by_cases nz : 0 < N.width e.val
    · rw [ite_eq_left nz]
      rw [ite_eq_right (Nat.ne_of_gt nz)] at raw
      have src : l.cell mem i.val false = (cell (N.src e.val)).val :=
        (col i 0).trans (congrArg (fun z => CableTriples.get z 0) raw)
      have dst : l.cell mem i.val true = (cell (N.dst e.val)).val :=
        (col i 1).trans (congrArg (fun z => CableTriples.get z 1) raw)
      have width : l.width mem i.val = N.width e.val := wid.trans (congrArg Cube.LabelIndex.Cable.width raw)
      have ne : l.cell mem i.val false ≠ l.cell mem i.val true := by
        rw [src,dst]
        exact fun h => e.property (Fin.ext h)
      have atCell : l.cell mem i.val side = (endpointCell N cell side e).val := by cases side; exact src; exact dst
      let z : Fin (N.width e.val) := ⟨0,nz⟩
      have atStart : mem (l.relative+2*i.val+side.toNat) = endpointRow N cell edgeID portID side e := by
        cases side
        · refine (off i 0).trans ?_
          exact Nat.add_right_cancel ((SuppliedOffsets.source_lane N cell aux siteID edgeID portID F rep fit e z).trans
            (ordinal_val N cell edgeID portID _ (.inl ⟨e,.inl rfl⟩) z))
        · refine (off i 1).trans ?_
          exact Nat.add_right_cancel ((SuppliedOffsets.dest_lane N cell aux siteID edgeID portID F rep fit e z).trans
            (ordinal_val N cell edgeID portID _ (.inl ⟨e,.inr rfl⟩) z))
      change cable l mem side i.val = _
      simp only [cable,ne,width,Nat.ne_of_gt nz,false_or,ite_false,HostScatter.Layout.dest,atCell,atStart,actualQuad]
    · have zero : N.width e.val = 0 := Nat.eq_zero_of_not_pos nz
      rw [ite_eq_left zero] at raw
      have h : l.width mem i.val = 0 := wid.trans (congrArg Cube.LabelIndex.Cable.width raw)
      change cable l mem side i.val = _
      simp [cable,h,nz]
  · intro side i empty
    have h := CableTriples.row_unused N cell aux siteID edgeID portID F rep codes i empty
    have zero : l.width mem i.val = 0 := (col i 2).trans (congrArg (fun z => CableTriples.get z 2) h)
    simp [cable,zero]

variable {N cell edgeID portID l mem}
variable (rows : CableRows N cell edgeID portID l mem)

include rows

/-- In the bounded loop a positive fragment is equivalent to one genuine
crossing cable at that sparse ID, with its exact supplied data pointer. -/
theorem cable_some_iff {i : ℕ} (hi : i < l.count) (side : Bool) (q : Quad) :
    cable l mem side i = some q ↔ ∃ e : N.CrossingEdge cell,
      (edgeID e.val).val = i ∧ 0 < N.width e.val ∧ q = actualQuad N cell edgeID portID l mem side e := by
  let j : Fin m := ⟨i,rows.count ▸ hi⟩
  constructor
  · intro found
    by_cases hit : j ∈ Set.range (CableTriples.wireOrd N cell edgeID)
    · obtain ⟨e,he⟩ := hit
      have idEq : (edgeID e.val).val = i := congrArg Fin.val he
      have lookup := rows.crossing side e
      rw [idEq,found] at lookup
      split at lookup <;> rename_i nz
      · exact ⟨e,idEq,nz,Option.some.inj lookup⟩
      · contradiction
    · exact False.elim (by have dead := rows.unused side j hit; change cable l mem side i = none at dead; rw [found] at dead; contradiction)
  · rintro ⟨e,rfl,h,rfl⟩
    rw [rows.crossing,ite_eq_left h]

/-- Every positive physical cable end occurs in its pass, at exactly its
true slab start and current cell-bank base. -/
theorem cablePass_cover (side : Bool) (e : N.CrossingEdge cell) (nz : 0 < N.width e.val) :
    actualQuad N cell edgeID portID l mem side e ∈ (List.range l.count).filterMap (cable l mem side) := by
  apply List.mem_filterMap.mpr
  exact ⟨(edgeID e.val).val,List.mem_range.mpr (rows.count ▸ (edgeID e.val).isLt),
    (rows.crossing side e).trans (ite_eq_left nz)⟩

/-- The selected endpoints are visited in sparse cable order in each pass.
Inside any receiving cell their entire bit intervals are ordered. -/
theorem cablePass_ordered (side : Bool) (c : ℕ) :
    ((List.range l.count).filterMap (cable l mem side)).Pairwise
      (fun a b => a.cell = c → b.cell = c → a.start+a.width ≤ b.start) := by
  apply List.pairwise_filterMap.mpr
  apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
  intro i j hi hj lt a ha b hb ac bc
  obtain ⟨e,ei,_,rfl⟩ := (cable_some_iff rows (List.mem_range.mp hi) side a).mp ha
  obtain ⟨f,fj,_,rfl⟩ := (cable_some_iff rows (List.mem_range.mp hj) side b).mp hb
  apply endpointRow_le N cell edgeID portID side side e f (Fin.ext (ac.trans bc.symm))
  exact Nat.add_lt_add_left ((ei.trans_lt lt).trans_eq fj.symm) _

/-- Every source fragment precedes every destination fragment that enters
the same receiving cell, independently of their sparse edge IDs. -/
theorem source_dest_ordered (c : ℕ) {a b : Quad}
    (ha : a ∈ (List.range l.count).filterMap (cable l mem false))
    (hb : b ∈ (List.range l.count).filterMap (cable l mem true))
    (ac : a.cell = c) (bc : b.cell = c) : a.start+a.width ≤ b.start := by
  obtain ⟨i,hi,hi'⟩ := List.mem_filterMap.mp ha
  obtain ⟨j,hj,hj'⟩ := List.mem_filterMap.mp hb
  obtain ⟨e,_,_,rfl⟩ := (cable_some_iff rows (List.mem_range.mp hi) false a).mp hi'
  obtain ⟨f,_,_,rfl⟩ := (cable_some_iff rows (List.mem_range.mp hj) true b).mp hj'
  exact endpoint_source_before_dest N cell edgeID portID e f (Fin.ext (ac.trans bc.symm))

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
