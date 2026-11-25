import OAI.Computability.BorderVNP.CubeScatterRawArenaDelivery
import OAI.Computability.BorderVNP.CubeTeamOwnedScannerWords

/-! # The full unvalidated shared words at the owned-team replay entry

The returned transmission gives the same raw list in both directed buffers
of a strict symbol row. The table installer writes only after those buffers.
Consequently the input to each team's traversal contains its literal received
word, before any selector check, declaration validation, or private replay.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRowSources DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}

/-- At the actual handoff from installation to the owned-group loop, both the
scalar scanner metadata and all unvalidated row words are resident together.
The single installer trace supplies both conclusions on the same memory. -/
theorem SharedWriters.replayInputs_after_install (writer : SharedWriters f g src) (ar : CubeArena.Layout)
    (decl : LengthDeclaration ar.n ar.header.d) (group : Fin ar.header.d → Fin (R+1))
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (u : Fin (R+1)) (template : Frame) (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (count : ℕ)
    (banks : g.banks = ar.pairBase) (spacing : g.stride = ar.pairStride)
    (room : ar.ReplayRoom w (readings (H u).pub 0)) (table : f.table = ar.table (readings (H u).pub 0) count)
    (pFrame : g.frame = readings (H u).pub 0)
    (source : ar.ScannerWords (readings (H u).pub 0) u.val decl.1.val (fun x => (group x).val)
      (readings (H u).pub) (src u) decl.2) :
    let hist := H u
    let frame := CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s
    let idBase := CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s
    CubeConstants.Fits frame w (readings hist.pub 0) idBase id →
      CubeConstants.Fields frame (readings hist.pub 0) idBase (readings hist.history.val.2.2) →
      ∀ {es out mem}, Runs hist.pub hist.macros (CubeConstants.install id)
        hist.history.val.2.1 hist.history.val.2.2 es out mem →
      ar.ScannerWords (readings hist.pub 0) u.val decl.1.val (fun x => (group x).val)
        (readings hist.pub) (readings mem) decl.2 ∧
      ar.RawViews (readings hist.pub 0) u.val decl.1.val (fun x => (group x).val) (f.receivedRows g group) mem := by
  intro hist frame idBase fit fields es out mem install
  exact ⟨writer.scannerWords_after_install ar (readings hist.pub 0) count decl.1.val u _ decl.2 template id
      table pFrame room.primary room.axes source fit fields install,
    writer.raw_arena_views symbols u template id banks spacing fit fields install⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
