import OAI.Hierarchy.DescentPackedMatchHandleRows

namespace OAI
/-! # Read the actual old thin and thick wires at the original pair's local offsets -/
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
variable (c : ScanColonies he A.stage)
local notation "thin" => thinList home color c
local notation "thick" => thickList home color c
local notation "pk" => slabPacking T A.cap thin thick
local notation "Pair" => Matched T A.cap thin thick

section Pool
variable {C : Type} [Fintype C] [DecidableEq C] (world : MarkedWorld F d P bits)
    (loc : world.graph.Site → C) (shade : world.graph.Site → Bool) (B : ℕ) (colony : C)
local notation "traffic₀" => nativeTraffic world.graph world.core loc
local notation "thin₀" => thinList loc shade colony
local notation "thick₀" => thickList loc shade colony
local notation "pack₀" => slabPacking traffic₀ B thin₀ thick₀
local notation "pair₀" => Matched traffic₀ B thin₀ thick₀

private def poolPick (e : pair₀) (side : Bool) : {e : world.graph.Edge // active world.graph world.core loc shade colony side e} := by
  cases side with
  | false =>
    let atom := thinAtom traffic₀ e
    have seen := thinAtom_in traffic₀ e
    have atSite := (mem_colorSites (U := world.graph.Site) loc shade false colony atom.1).mp seen
    have src := original_src world loc atom
    exact ⟨PairRAM.original world.graph world.core loc atom, original_mem world loc atom,
      (congrArg loc src).trans atSite.1, (congrArg shade src).trans atSite.2⟩
  | true =>
    let atom := thickAtom traffic₀ e
    have seen : atom.1 ∈ thick₀ := List.get_mem thick₀ (oldThick traffic₀ B thin₀ thick₀ e).2.1
    have atSite := (mem_colorSites (U := world.graph.Site) loc shade true colony atom.1).mp seen
    have src := original_src world loc atom
    exact ⟨PairRAM.original world.graph world.core loc atom, original_mem world loc atom,
      (congrArg loc src).trans atSite.1, (congrArg shade src).trans atSite.2⟩

omit [Field F] in
private theorem poolPick_old (e : pair₀) (side : Bool) :
    (poolPick world loc shade B colony e side).val =
      colorPick world.graph world.core loc shade B (⟨colony,e⟩,if side then 0 else 1) := by
  cases side <;> rfl

private def poolOffset (e : pair₀) (side : Bool) : ℕ := if side then
  PairRAM.thickOffset world.graph world.core loc shade colony e.1+(thickEnd pack₀ e).2.val else
  PairRAM.rawOffset world.graph world.core loc shade B colony e.2.1.val+e.2.2.val

omit [Field F] in
private theorem poolPosition (e : pair₀) (side : Bool) :
    ((DescentOldOccurrenceRAM.order world loc shade side).symm (Fintype.equivFin world.graph.Edge (poolPick world loc shade B colony e side).val)).val=
        globalStart world loc shade side colony+poolOffset world loc shade B colony e side := by
  cases side with
  | false =>
    let j : Locations (pack₀).decisions := e.2.1.val
    let o : ThinPool traffic₀ ((pack₀).decisions.get j).1 := (oldThin traffic₀ B thin₀ thick₀ e).2
    let xs := ((pack₀).decisions.get j).1
    let unit := finCongr (thinPool_card traffic₀ xs).symm e.2.2
    have index : (thinPoolOrder traffic₀ xs o).val = e.2.2.val :=
      congrArg Fin.val ((thinPoolOrder traffic₀ xs).apply_symm_apply unit)
    have pos := thin_position (C:=C) world loc shade colony B j o
    let start := globalStart world loc shade false colony
    let off := PairRAM.rawOffset world.graph world.core loc shade B colony j
    exact pos.trans ((congrArg (fun i => start + off + i) index).trans (Nat.add_assoc start off e.2.2.val))
  | true =>
    let o : ThickPool traffic₀ thick₀ e.1 := (oldThick traffic₀ B thin₀ thick₀ e).2
    have index : (thickPoolOrder traffic₀ thick₀ e.1 o).val = (thickEnd pack₀ e).2.val :=
      congrArg Fin.val ((thickPoolOrder traffic₀ thick₀ e.1).apply_symm_apply (thickEnd pack₀ e).2)
    have pos := thick_position (C:=C) world loc shade colony e.1 o
    let start := globalStart world loc shade true colony
    let off := PairRAM.thickOffset world.graph world.core loc shade colony e.1
    exact pos.trans ((congrArg (fun i => start + off + i) index).trans (Nat.add_assoc start off (thickEnd pack₀ e).2.val))

end Pool

def picked (e : Pair) (side : Bool) : Active A he c side :=
  poolPick (C := ScanColonies he A.stage) W home color A.cap c e side

theorem picked_old (e : Pair) (side : Bool) :
    (picked A he c e side).val=colorPick N W.core home color A.cap (⟨c,e⟩,if side then 0 else 1) :=
  poolPick_old (C := ScanColonies he A.stage) W home color A.cap c e side

def oldOffset (e : Pair) (side : Bool) : ℕ :=
  poolOffset (C := ScanColonies he A.stage) W home color A.cap c e side

set_option maxRecDepth 4096 in
theorem picked_position (e : Pair) (side : Bool) :
    ((DescentOldOccurrenceRAM.order W home color side).symm (Fintype.equivFin (N).Edge (picked A he c e side).val)).val=
        globalStart W home color side c+oldOffset A he c e side := by
  unfold picked oldOffset
  exact poolPosition (C := ScanColonies he A.stage) W home color A.cap c e side

variable (rank : (J×V)↪ℕ) (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + (scanColorAt he A.stage u).toNat)
    (sorted : RosterSorted A next rank) (route : Routes A native S ready names next) (df : A.degree<2^short)
    (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)

include rank coord named fit winner sorted route df edgeOrder in
theorem picked_wire (e : Pair) (side : Bool) :
    let u:=panel (addr c).1;let xs:=stream u n (heap (addr c).2) side
    oldOffset A he c e side<xs.length ∧ ∀f,triple u xs (oldOffset A he c e side) f=rawTriple A native S ready names he c side (picked A he c e side) f := by
  intro u xs
  have position := picked_position A he c e side
  obtain ⟨j, _, cmp⟩ := original_rows (short := short) (a := a) A native S ready names win next he
    rank coord named fit winner sorted route df edgeOrder c side (picked A he c e side)
  have offset : oldOffset A he c e side = j.val :=
    Nat.add_left_cancel (position.symm.trans cmp)
  exact ⟨offset.le.trans_lt j.isLt,
    original_triple (short := short) (a := a) A native S ready names win next he rank coord named
      fit winner sorted route df edgeOrder c side (picked A he c e side) _ position⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
