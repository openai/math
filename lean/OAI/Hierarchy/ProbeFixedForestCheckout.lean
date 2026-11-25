import OAI.Hierarchy.ProbeFixedPaidEconomicRows

namespace OAI
/-! # The chronological strip forest at the actual paid-width checkout -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open CatalogueRows StripChart StripDirectory StockCommit BoughtSockets
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
set_option quotPrecheck false
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "H" => v.publicHeader P z width
local notation "site" => v.located (v.seed P z width) P width
local notation "rows" => treeRows site v.mesh P.catalogue P.routes F
local notation "payload" => PayloadStrip.edgeCount (Stages z (2^v.W))

private theorem fetched (base n : ℕ) (a : Attempt) (occurs : Event.attempt a∈events v.mesh) :
    let table:=treePage site v.mesh P.catalogue P.routes F base n
    let i : Fin (events v.mesh).length:=⟨(events v.mesh).idxOf (.attempt a),List.idxOf_lt_length_of_mem occurs⟩
    table.header i=treeHeader (pageStart table v.mesh a) (rows a) n k := by
  intro table i
  have date : (events v.mesh)[i]=Event.attempt a:=List.getElem_idxOf i.isLt
  have atRow : table.rows i=rows a := by
    change (match (events v.mesh)[i] with | .attempt t=>rows t | .feed _=>0)=_
    rw [date]
  change PortHeader.mk _ (table.rows i) _=_
  rw [atRow]; rfl

/-- The true arena prefix survives the protocol run and the final latch write. -/
theorem paid_forest_checkout (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (flag : ℕ) (m : Memory W) (ready : Calendar.mounted (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) m)
    (after : (G).first≤flag) (x : ℕ) (hx : x<(G).first) :
    checkedOut (v.nativeChart P z width r banks src tab dst owners) flag m x=m x := by
  let C:=v.nativeChart P z width r banks src tab dst owners
  change (checkedOut C flag m) x=_
  rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image flag 1 _ _ x (.inl (hx.trans_le after))]
  apply run_frame C _ m x ready
  intro e _
  exact (v.event_prefix P z width r banks src tab dst owners e x (hx.trans_le (Nat.le_add_right (G).first _))).1

private theorem reads_of_columns {n edges ww : ℕ} (t₁ t₂ : Traversals) (mem : Memory ww)
    (walk : Fin n → List (Fin edges)) (positions : t₁.positions = t₂.positions)
    (edge : t₁.edge = t₂.edge) (sourceRow : t₁.sourceRow = t₂.sourceRow) :
    t₁.Reads mem walk → t₂.Reads mem walk := by
  rcases t₁ with ⟨p₁, owner₁, parity₁, e₁, r₁, mate₁⟩
  rcases t₂ with ⟨p₂, owner₂, parity₂, e₂, r₂, mate₂⟩
  change p₁ = p₂ at positions
  change e₁ = e₂ at edge
  change r₁ = r₂ at sourceRow
  subst p₂
  subst e₂
  subst r₂
  intro h
  obtain ⟨enum, edgesRead, rowsRead⟩ := h
  exact ⟨enum, edgesRead, rowsRead⟩

private theorem guarded_tree_reads {n edges ww : ℕ} (b : CatalogueRows.Board) (old : Traversals)
    (first next : Expr × Expr) (mem : Memory ww) (walk : Fin n → List (Fin edges)) :
    (b.guardWalk {old with catalystMate := some first}).Reads mem walk →
      (b.guardWalk {old with catalystMate := some next}).Reads mem walk :=
  reads_of_columns _ _ mem walk rfl rfl rfl

set_option maxHeartbeats 1200000 in
/-- The native walk is read through its position count, edge, and source-row
columns. Both header choices preserve those columns on the same original tree. -/
private theorem reads_at_header {h exponent k₀ q₀ depth numRows edges ww : ℕ}
    (s : StripChart.Boards h (2^exponent) k₀ q₀ depth) (c : Mesh)
    (b : CatalogueRows.Board) (routes : PortBanks ((c.inject+c.cool)*c.outerFuel))
    (old : Traversals) (a : Attempt) (first next : PortHeader)
    (mem : Memory ww) (walk : Fin numRows → List (Fin edges)) :
    (forestAtHeader s c b routes first old a).Reads mem walk →
      (forestAtHeader s c b routes next old a).Reads mem walk := by
  let capacity := max (Fintype.card (PayloadRole (Stages h (2^exponent)) k₀))
    (Fintype.card (PurchasedRole depth k₀))
  let fields (r : PortHeader) : Expr × Expr :=
    (chooseField capacity 0 (catalystFlag (z := h) («W» := exponent) (k := k₀) (depth := depth) a) r.fieldTerm,
      chooseField capacity 0 (fun i => (radiusMate s c b routes a i).atRow r.ballTerm) r.fieldTerm)
  exact guarded_tree_reads b old (fields first) (fields next) mem walk

set_option maxHeartbeats 800000 in
/-- The public archive names both fixed finite traversals at every installed attempt. -/
theorem native_forest_resident (final : Memory W) (pub : (H).Resident final)
    (a : Attempt) (occurs : Event.attempt a∈events v.mesh) (room : P.catalogue.rows<2^W)
    (pos : 0<P.catalogue.coreRows) (rowRoom : rows a≤2^W)
    (payloadRoom : Fintype.card (Strip.TreeLink payload k)≤2^W)
    (boughtRoom : Fintype.card (Strip.TreeLink (ChainStrip.edgeCount v.depth) k)≤2^W) :
    (v.nativeTrees P z width a).Reads final (fun j : Fin (rows a)=>treeWalk site v.mesh P.catalogue P.routes a final j.val pos) := by
  let i : Fin (events v.mesh).length:=⟨(events v.mesh).idxOf (.attempt a),List.idxOf_lt_length_of_mem occurs⟩
  let page:=payloadPage site v.mesh P.catalogue P.routes F (H).payloadTree.base
  have pageEq : page=(H).payloadTree := paidTreePage_eq v P z width (H).payloadTree.base payload
  have secondEq : boughtPage site v.mesh P.catalogue P.routes F (H).payloadTree.base=(H).boughtTree := by
    change treePage site v.mesh P.catalogue P.routes F page.stop _=_
    rw [pageEq]
    exact paidTreePage_eq v P z width (H).payloadTree.stop (ChainStrip.edgeCount v.depth)
  have atP:=fetched v P z width (H).payloadTree.base payload a occurs
  have atB:=fetched v P z width page.stop (ChainStrip.edgeCount v.depth) a occurs
  change page.header i=treeHeader (pageStart page v.mesh a) (rows a) payload k at atP
  change (boughtPage site v.mesh P.catalogue P.routes F (H).payloadTree.base).header i=
    treeHeader (pageStart (boughtPage site v.mesh P.catalogue P.routes F (H).payloadTree.base) v.mesh a)
      (rows a) (ChainStrip.edgeCount v.depth) k at atB
  let old := originalTree site v.mesh P.catalogue P.routes F (H).payloadTree.base a
  apply reads_at_header site v.mesh P.catalogue P.routes old a (StripChart.header F (withPorts site v.mesh P.catalogue P.routes) a)
    (StripChart.header F (v.mounted (v.seed P z width) P width) a) final _
  apply withTrees_reads site v.mesh P.catalogue P.routes F (H).payloadTree.base a final room pos rowRoom payloadRoom boughtRoom
  · exact ((congrArg (fun t : PortROM.Table (events v.mesh).length=>t.header i) pageEq).symm.trans atP) ▸ pub.payloadTree i
  · exact ((congrArg (fun t : PortROM.Table (events v.mesh).length=>t.header i) secondEq).symm.trans atB) ▸ pub.boughtTree i

/-- The entire tree walk is recovered from checked-out public header data
at every candidate, including inactive and padding candidates. -/
theorem native_forest_reads (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (flag : ℕ) (m : Memory W) (pub : (H).Resident m)
    (ready : Calendar.mounted (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) m)
    (after : (G).first≤flag) (a : Attempt) (occurs : Event.attempt a∈events v.mesh)
    (room : P.catalogue.rows<2^W) (pos : 0<P.catalogue.coreRows) (rowRoom : rows a≤2^W)
    (payloadRoom : Fintype.card (Strip.TreeLink payload k)≤2^W)
    (boughtRoom : Fintype.card (Strip.TreeLink (ChainStrip.edgeCount v.depth) k)≤2^W) :
    let final:=checkedOut (v.nativeChart P z width r banks src tab dst owners) flag m
    (v.nativeTrees P z width a).Reads final (fun j : Fin (rows a)=>treeWalk site v.mesh P.catalogue P.routes a final j.val pos) := by
  intro final
  have economic : (H).stop≤(G).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have ord : (H).Ordered:=economic_ordered F (v.sized (v.seed P z width) width) v.cost v.mesh
    P.joint P.catalogue P.routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  apply v.native_forest_resident P z width final (EconomicHeader.Resident.move (H) pub ord ?_) a occurs room pos rowRoom payloadRoom boughtRoom
  intro x low
  exact v.paid_forest_checkout P z width r banks src tab dst owners flag m ready after x (low.trans_le economic)

theorem native_forest_run_reads (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (m : Memory W) (pub : (H).Resident m)
    (ready : Calendar.mounted (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) m)
    (a : Attempt) (occurs : Event.attempt a∈events v.mesh) (room : P.catalogue.rows<2^W)
    (pos : 0<P.catalogue.coreRows) (rowRoom : rows a≤2^W)
    (payloadRoom : Fintype.card (Strip.TreeLink payload k)≤2^W)
    (boughtRoom : Fintype.card (Strip.TreeLink (ChainStrip.edgeCount v.depth) k)≤2^W) :
    let final:=run (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) m
    (v.nativeTrees P z width a).Reads final (fun j : Fin (rows a)=>treeWalk site v.mesh P.catalogue P.routes a final j.val pos) := by
  intro final
  have economic : (H).stop≤(G).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P z width)
  have ord : (H).Ordered:=economic_ordered F (v.sized (v.seed P z width) width) v.cost v.mesh
    P.joint P.catalogue P.routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  apply v.native_forest_resident P z width final (EconomicHeader.Resident.move (H) pub ord ?_) a occurs room pos rowRoom payloadRoom boughtRoom
  intro x low
  apply run_frame _ _ _ _ ready
  intro e _
  exact (v.event_prefix P z width r banks src tab dst owners e x ((low.trans_le economic).trans_le (Nat.le_add_right ..))).1

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
