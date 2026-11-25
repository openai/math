import OAI.Computability.BorderVNP.CubeTeamRawPhysicalScans
import OAI.Computability.BorderVNP.CubeISAOwnedDeliveredPrefix
import OAI.Computability.BorderVNP.CubeTeamOwnedReplaySetup
import OAI.Computability.BorderVNP.CubeScatterArenaDelivered

/-! # Initializing the raw native traversal from the genuine delivered words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRowSources
open DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}

/-- The whole delivered row survives the actual constant installation on either owner,
without requiring its prefix or declaration to have passed any check. -/
theorem SharedWriters.raw_arena_views (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (team : Fin (R+1)) (template : Frame) (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (banks : g.banks = ar.pairBase) (spacing : g.stride = ar.pairStride) :
    let hist := H team
    let frame := CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s
    let idBase := CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s
    CubeConstants.Fits frame w (readings hist.pub 0) idBase id →
      CubeConstants.Fields frame (readings hist.pub 0) idBase (readings hist.history.val.2.2) →
      ∀ {es out mem}, Runs hist.pub hist.macros (CubeConstants.install id) hist.history.val.2.1 hist.history.val.2.2 es out mem →
        ar.RawViews (readings hist.pub 0) team.val decl.1.val (fun x => (group x).val) (f.receivedRows g group) mem := by
  intro hist frame idBase fit fields es out mem install p high owned
  let l := ar.scanner (readings hist.pub 0) team.val decl.1.val ar.rowSelectorBits
  have destination : (if high then group p.val.2 else group p.val.1) = team := by cases high <;> exact Fin.ext owned
  let base := if high then g.view p.val.2 p.val.1 else g.view p.val.1 p.val.2
  obtain ⟨_,_,_,lower,upper⟩ := writer.declaredRows symbols p
  have read : Resident (pairRegion g) hist.history.val.2.2 base (f.receivedRows g group p) := by
    change Resident _ (H team).history.val.2.2 _ _
    rw [←destination]
    cases high <;> first | exact lower | exact upper
  have arena : g.banks+g.stride*g.groups^2 ≤ frame.zeroAddr := by
    simpa only [banks,spacing,symbols.groups,frame,CubeConstants.inArena] using ar.orderedViews_before_tables
  have preserve x (hx : x ∈ pairRegion g) := TeamHistory.install_before hist frame idBase id fit fields install x (hx.2.trans_le arena)
  have region : Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d)) = pairRegion g := by
    simp only [l,CubeArena.Layout.scanner,pairRegion,banks,spacing,symbols.groups,pow_two]
  have pointer : l.view (key (oriented p high)) = base := by
    have shared : l.view (key (oriented p high)) = (TeamRowPrepare.Layout.ofShared g team.val).view (key (oriented p high)) := by
      simp only [l,CubeArena.Layout.scanner,TeamRowPrepare.Layout.view,TeamRowPrepare.Layout.ofShared,banks,spacing]
    rw [shared,TeamRowPrepare.Layout.ofShared_view,symbols.groups,(key_digits (oriented p high)).1,(key_digits (oriented p high)).2]
    cases high <;> rfl
  change Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) mem (l.view (key (oriented p high))) _
  rw [region,pointer]; exact read.congr preserve

/-- The raw directed rows yield the exact selector slices read by the native candidate loop. -/
theorem SharedWriters.raw_arena_prefixes (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group) (team : Fin (R+1))
    (mem : Memory w)
    (views : ar.RawViews (readings (H team).pub 0) team.val decl.1.val (fun x => (group x).val) (f.receivedRows g group) mem) :
    ar.RawPrefixes (readings (H team).pub 0) team.val decl (fun x => (group x).val)
      (fun p => (f.receivedRows g group p).take (rowSelectorBits ar.n ar.header.d ar.header.blocks ar.K ar.h decl.1 (Sym2.mk p.val.1 p.val.2))) mem := by
  intro p high owned
  let u := if high then group p.val.2 else group p.val.1
  let width := rowSelectorBits ar.n ar.header.d ar.header.blocks ar.K ar.h decl.1 (Sym2.mk p.val.1 p.val.2)
  have count := (writer.raw_prefix symbols p high ar.powerBase (H u).history.val.2.2 (fun _ _ => rfl)).1
  have read := resident_views (power := ar.powerBase) (n := ar.n) (views p high owned)
  exact ⟨count,by simpa only [rawChunk,List.drop_zero,Nat.add_zero] using read.chunk 0 width (Nat.zero_le _)⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
