import OAI.Computability.BorderVNP.CubeScatterRawArenaDelivery
import OAI.Computability.BorderVNP.CubeTeamOwnedScannerWords
import OAI.Computability.BorderVNP.CubeScatterRawPayload

/-! # Actual native team histories give the distributed declaration checker -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}

/-- Raw declaration scans constructed from the successful shared writers, their
real received RAM, and the consecutive installer and owned-group returns on every
team. The only initial table is the decoded *advertised* declaration. -/
theorem SharedWriters.physical_scans (writer : SharedWriters f g src) (ar : CubeArena.Layout)
    (decl : LengthDeclaration ar.n ar.header.d) (group : Fin ar.header.d → Fin (R+1))
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (template : Frame) (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (count : ℕ)
    (banks : g.banks = ar.pairBase) (spacing : g.stride = ar.pairStride) (copies : 1 ≤ ar.K)
    (room : ∀ u, ar.ReplayRoom w (readings (H u).pub 0))
    (table : ∀ u, f.table = ar.table (readings (H u).pub 0) count)
    (atFrame : ∀ u, g.frame = readings (H u).pub 0)
    (words : ∀ u, ar.ScannerWords (readings (H u).pub 0) u.val decl.1.val (fun x => (group x).val) (readings (H u).pub) (src u) decl.2) :
    let layout := CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s
    let idBase := CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s
    (∀ u, CubeConstants.Fits layout w (readings (H u).pub 0) idBase id) →
    (∀ u, CubeConstants.Fields layout (readings (H u).pub 0) idBase (readings (H u).history.val.2.2)) →
    (∀ u, ∃ es out mem fs t mt, Runs (H u).pub (H u).macros (CubeConstants.install id)
      (H u).history.val.2.1 (H u).history.val.2.2 es out mem ∧
      Runs (H u).pub (H u).macros (ownedGroups ar.n ar.b ar.h ar.K ar.s) out mem fs t mt) →
    Nonempty (RawScans group (fun u => (H u).pub) (fun u => (H u).macros) decl
      (fun p => (f.receivedRows g group p).take (rowSelectorBits ar.n ar.header.d ar.header.blocks ar.K ar.h decl.1
        (Sym2.mk p.val.1 p.val.2))) ar.header.blocks ar.b ar.h ar.K ar.s) := by
  intro layout idBase fits fields stages
  choose es out mem fs t mt install scan using stages
  have initial (u : Fin (R+1)) := writer.scannerWords_after_install ar (readings (H u).pub 0) count decl.1.val u
    (fun x => (group x).val) decl.2 template id (table u) (atFrame u) (room u).primary (room u).axes (words u)
    (fits u) (fields u) (install u)
  have inputs (u : Fin (R+1)) := ar.rawInputs_of_words (readings (H u).pub 0) u.val decl copies
    (fun x => (group x).val) (H u).pub (mem u) (room u).axes (room u).alphabet (room u).payload
    (room u).positive (room u).primary (room u).stopFit (room u).fixedFit (room u).capFit (initial u)
  exact RawScans.of_physical inputs (fun u => writer.raw_arena_prefixes symbols u (mem u)
    (writer.raw_arena_views symbols u template id banks spacing (fits u) (fields u) (install u)))
    (fun u => ⟨out u,fs u,t u,mt u,scan u⟩)

end TeamContraction

end BorderVNP
end Computability
end OAI
