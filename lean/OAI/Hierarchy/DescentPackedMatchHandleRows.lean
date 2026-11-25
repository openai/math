import OAI.Hierarchy.DescentPackedMatchHandles

namespace OAI
/-! # Exact local packed triple at the old global sort's typed pool offset -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentOldOccurrenceRAM
open scoped Classical BigOperators
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
local notation "T" => nativeTraffic N W.core home
local notation "n" => binCount (2^k) A.degree
private theorem row_of_inventory {I Q : Type} [Fintype I] (selected : I → Prop)
    (xs : List Q) (ptr : {i // selected i} ↪ Q) (r : Q → Q → Prop)
    (keyA keyB keyC : I → ℕ) (e : {i // selected i}) (absolute start : ℕ)
    (inventory : ∀ z, z ∈ xs ↔ ∃ i, ptr i = z) (sortedRows : xs.Pairwise r)
    (asymm : ∀ a b, r a b → ¬ r b a)
    (compare : ∀ f, r (ptr f) (ptr e) ↔ lex3 keyA keyB keyC f.val e.val)
    (offset : absolute = start +
      count (fun f => selected f ∧ keyA f < keyA e.val) +
      count (fun f => selected f ∧ keyA f = keyA e.val ∧ keyB f < keyB e.val) +
      count (fun f => selected f ∧ keyA f = keyA e.val ∧ keyB f = keyB e.val ∧ keyC f < keyC e.val)) :
    ∃ j : Fin xs.length, xs.get j = ptr e ∧ absolute = start + j.val := by
  have member (f) : ptr f ∈ xs := (inventory _).mpr ⟨f, rfl⟩
  have covers (z) (hz : z ∈ xs) := (inventory z).mp hz
  let j := streamRank ptr member covers sortedRows asymm e
  refine ⟨j, streamRank_get ptr member covers sortedRows asymm e, ?_⟩
  have relative : j.val = count (fun f : {i // selected i} => lex3 keyA keyB keyC f.val e.val) :=
    (streamRank_count ptr member covers sortedRows asymm e).trans (count_congr compare)
  rw [relative, lex_count selected keyA keyB keyC e.val, ←Nat.add_assoc, ←Nat.add_assoc]
  exact offset

omit [Field F] in
private theorem old_offset {C : Type} [Fintype C] [DecidableEq C] (world : MarkedWorld F d P bits)
    (loc : world.graph.Site → C) (shade : world.graph.Site → Bool) (side : Bool) (group : C)
    (e : world.graph.Edge) (keep : e ∈ world.core) (atGroup : loc (world.graph.src e) = group)
    (atSide : shade (world.graph.src e) = side) :
    let first := fun f : world.graph.Edge =>
      if side then PositiveAperture.rank (loc (world.graph.dst f)) else originalId world.graph.Site (world.graph.src f)
    let second := fun f : world.graph.Edge =>
      if side then originalId world.graph.Site (world.graph.src f) else PositiveAperture.rank (loc (world.graph.dst f))
    let selected := active world.graph world.core loc shade group side
    ((DescentOldOccurrenceRAM.order world loc shade side).symm (Fintype.equivFin world.graph.Edge e)).val =
      globalStart world loc shade side group +
      count (fun f => selected f ∧ first f < first e) +
      count (fun f => selected f ∧ first f = first e ∧ second f < second e) +
      count (fun f => selected f ∧ first f = first e ∧ second f = second e ∧
        originalId world.graph.Edge f < originalId world.graph.Edge e) := by
  subst group
  exact DescentOldOccurrenceRAM.position world loc shade side e keep atSide

variable (rank : (J×V)↪ℕ) (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + (scanColorAt he A.stage u).toNat)
    (sorted : RosterSorted A next rank) (route : Routes A native S ready names next) (df : A.degree<2^short)
    (edgeOrder : ∀ e f : W.graph.Edge, native e < native f ↔ originalId W.graph.Edge e < originalId W.graph.Edge f)
set_option maxRecDepth 4096 in
include rank coord named fit winner sorted route df edgeOrder in
theorem original_rows (c : ScanColonies he A.stage) (side : Bool) (e : Active A he c side) :
    let u:=panel (addr c).1;let ptr:=handle A native S ready he c side
    let xs:=stream u n (heap (addr c).2) side
    ∃j : Fin xs.length,xs.get j=ptr e ∧
      ((DescentOldOccurrenceRAM.order W home color side).symm (Fintype.equivFin (N).Edge e.val)).val=
        globalStart W home color side c+j.val := by
  intro u ptr xs
  let a := primary u side
  let b := secondary u side
  let w := fun z : Port (2^k) (2*A.cap) => z.2.val
  refine row_of_inventory (I := W.graph.Edge) (Q := Port (2^k) (2*A.cap))
    (active W.graph W.core home color c side) xs ptr (lex3 a b w)
    (originalA A he side) (originalB A he side) (originalId W.graph.Edge) e
    ((DescentOldOccurrenceRAM.order W home color side).symm (Fintype.equivFin W.graph.Edge e.val)).val
    (globalStart W home color side c)
    (handle_mem (short := short) A native S ready names win next he coord fit winner route df c side)
    (stream_ordered u n (heap (addr c).2) side) (lex_asymm a b w)
    (fun f => handle_order (short := short) A native S ready names win next he rank coord named
      fit winner sorted route df edgeOrder c side f e) ?_
  have absolute := old_offset (C := ScanColonies he A.stage) W home color side c e.val
    e.property.1 e.property.2.1 e.property.2.2
  dsimp only at absolute
  unfold originalA originalB
  exact absolute

def rawTriple (c : ScanColonies he A.stage) (side : Bool) (e : Active A he c side) : Fin 3→ℕ :=
  let q:=event A he c side e
  let v:=target A native S ready names ((addr c).1,q.1) q.2
  let s:=address A native S ready ((addr c).1,q.1) q.2
  ![q.1.val*(2*A.cap)+s.val,q.1.val,v.val*2^k+q.1.val]

include rank coord named fit winner sorted route df edgeOrder in
theorem original_triple (c : ScanColonies he A.stage) (side : Bool) (e : Active A he c side) (off : ℕ)
    (position : ((DescentOldOccurrenceRAM.order W home color side).symm (Fintype.equivFin (N).Edge e.val)).val=globalStart W home color side c+off) :
    ∀f : Fin 3,triple (panel (addr c).1) (stream (panel (addr c).1) n (heap (addr c).2) side) off f=rawTriple A native S ready names he c side e f := by
  obtain ⟨j,row,abs⟩:=original_rows A native S ready names win next he rank coord named fit winner sorted route df edgeOrder c side e
  have eqn : off = j.val := Nat.add_left_cancel (position.symm.trans abs)
  intro f;rw [eqn,triple_at _ _ j,row]
  let q:=event A he c side e
  have seen:=peer_at A native S ready names win next ((addr c).1,q.1) q.2 df
  change peer (panel (addr c).1) (handle A native S ready he c side e).1 (handle A native S ready he c side e).2=some _ at seen
  simp only [details,seen,Option.map_some,Option.getD_some,rawTriple]
  rfl


end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
