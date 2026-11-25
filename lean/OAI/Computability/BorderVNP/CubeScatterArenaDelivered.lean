import OAI.Computability.BorderVNP.CubeScatterArenaAllocation
import OAI.Computability.BorderVNP.CubeScatterDeliveredStart
import OAI.Computability.BorderVNP.CubeScatterScheduledDeclaration

/-! # The delivered declaration and row streams at the actual owned scanner's ABI -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube CubeHeaderInstall

/-- The decoded secondary declaration array precedes all three arrays written by
the weight and group-owner passes. This gives the concrete separation for
reading the declared widths from the shared writer's source RAM. -/
theorem Layout.declaration_before_schedule (a : Layout) (axes : a.header.a = a.n+1) :
    a.header.header+13+a.header.entries+a.header.d*a.header.d*(a.n+1) ≤
      min a.groupWeights (min a.teamTotals a.ownerBase) := by
  have stat : a.header.header+13+a.header.entries+a.header.d*a.header.d*(a.n+1) ≤ a.header.packetBase := by
    simp only [Inputs.packetBase,Inputs.entries,axes]; omega
  have bp : a.header.packetBase ≤ a.packetEnd := Nat.le_add_right _ _
  obtain ⟨scratch,single,_,_,_,_⟩ := a.separated
  obtain ⟨power,_,_⟩ := a.source_order
  have vert : a.vertexBase ≤ a.publicBase := Nat.le_add_right _ _
  unfold Layout.groupWeights Layout.teamTotals Layout.ownerBase
  simp only [Layout.teamTotals,Layout.groupWeights]
  omega

/-- A length-only cube lookup arena installed at the first fresh address cannot
overwrite any of the actual directed symbol pair views. -/
theorem Layout.orderedViews_before_tables (a : Layout) :
    a.pairBase+a.pairStride*a.header.d^2 ≤ a.stop := by
  rw [Nat.mul_comm a.pairStride]
  exact a.separated.2.2.2.2.1.le.trans a.separated.2.2.2.2.2

end RoutingISA.CubeArena

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {a q blocks K h b s : ℕ}

/-- Every word needed by the row invariant survives the real signed installer,
using the same arena as the row's packet, singleton, and vertex directories. -/
theorem TeamHistory.install_scanner_source (hist : TeamHistory w) (ar : CubeArena.Layout)
    (team axis selectors : ℕ) (template : Frame) (id : TableEntry a b h K s → ℕ)
    (frameLow : readings hist.pub 0+112 ≤ ar.header.header) (axes : ar.header.a = ar.n+1) :
    let frame := CubeConstants.inArena template ar.stop a b h K s
    let idBase := CubeConstants.idBase ar.stop a b h K s
    let scan := ar.scanner (readings hist.pub 0) team axis selectors
    CubeConstants.Fits frame w (readings hist.pub 0) idBase id →
      CubeConstants.Fields frame (readings hist.pub 0) idBase (readings hist.history.val.2.2) →
      ∀ {es out mem}, Runs hist.pub hist.macros (CubeConstants.install id)
        hist.history.val.2.1 hist.history.val.2.2 es out mem →
      ∀ j ∈ TeamRowSources.source scan ar.powerBase ar.n, mem j = hist.history.val.2.2 j := by
  intro frame idBase scan fit fields es out mem run j hj
  exact TeamHistory.install_before hist frame idBase id fit fields run j
    (ar.scanner_source_lt _ team axis selectors frameLow axes hj)

variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
  {src : Fin (R+1) → ℕ → ℕ} {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

/-- Exact initial selector and crossing residency in the full protected source set
used by the physical strict-side program. This applies to either oriented view
of a co-located or remotely delivered symbol pair. -/
theorem SharedWriters.owned_sources (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) blocks K h decl group)
    (select : Packet a q blocks → Selector a K h) (pass : passesLengths b s select decl)
    (supply : (p : Packet a q blocks) → (e : Cube.Edge (a+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (single : SingleSlot a q blocks (h*b) → Bool)
    (emits : sharedWords decl ⟨⟨select,pass⟩,fun _ => rowCrossValue supply single⟩ = f.receivedRows g group)
    (p : Symbols q) (high : Bool) (ar : CubeArena.Layout) (template : Frame) (id : TableEntry a b h K s → ℕ)
    (banks : g.banks = ar.pairBase) (spacing : g.stride = ar.pairStride) (groups : g.groups = ar.header.d) :
    let team := if high then group p.val.2 else group p.val.1
    let base := if high then g.view p.val.2 p.val.1 else g.view p.val.1 p.val.2
    let hist := H team
    let sel := commonSelectors select decl.1 p
    let frame := CubeConstants.inArena template ar.stop a b h K s
    let idBase := CubeConstants.idBase ar.stop a b h K s
    let protectedWords := TeamRowSources.source (TeamRowPrepare.Layout.ofShared g team.val) ar.powerBase a
    CubeConstants.Fits frame w (readings hist.pub 0) idBase id →
      CubeConstants.Fields frame (readings hist.pub 0) idBase (readings hist.history.val.2.2) →
      ∀ {es out mem}, Runs hist.pub hist.macros (CubeConstants.install id)
        hist.history.val.2.1 hist.history.val.2.2 es out mem →
        Resident protectedWords mem base sel ∧
        Resident protectedWords mem (base+sel.length) (commonCrossings b decl.1 p select supply single) := by
  intro team base hist sel frame idBase protectedWords fit fields es out mem run
  have arena : g.banks+g.stride*g.groups^2 ≤ frame.zeroAddr := by
    simpa only [banks,spacing,groups,frame,CubeConstants.inArena] using ar.orderedViews_before_tables
  obtain ⟨sels,cross⟩ := writer.scanner_streams symbols select pass supply single emits p high frame idBase id
    arena fit fields run
  have lift {ptr : ℕ} {bs : List Bool} (read : Resident (pairRegion g) mem ptr bs) : Resident protectedWords mem ptr bs := by
    apply TeamRowSources.resident_views
    simpa only [pairRegion,TeamRowPrepare.Layout.ofShared,pow_two] using read
  exact ⟨lift sels,lift cross⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
