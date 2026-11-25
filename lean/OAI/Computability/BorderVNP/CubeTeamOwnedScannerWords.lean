import OAI.Computability.BorderVNP.CubeTeamOwnedArenaSetup
import OAI.Computability.BorderVNP.CubeScatterTransmissionInventory

/-! # Retaining the actual scanner inputs through shared transmission and lookup installation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM CubeHeaderInstall BorderVNP.Cube

/-- All metadata and the immutable declared row array are below the pair
directory. The shared writer may update the physical row count at frame 13. -/
theorem Layout.ScannerWords.transfer {a : Layout} {frame team axis : ℕ} {owner : Fin a.header.d → ℕ}
    {p : Arg → ℕ} {orig out : ℕ → ℕ} {rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ}
    (words : a.ScannerWords frame team axis owner p orig rows) (axes : a.header.a = a.n+1)
    (frameLow : frame+112 ≤ a.header.header)
    (same : ∀ x < a.pairDirectory, x ≠ frame+13 → out x = orig x) :
    a.ScannerWords frame team axis owner p out rows := by
  have bank := LocalRow.arenaExtents a
  have powers := a.source_order.2.1
  have dir : a.pairDirectory = a.ownerBase+a.header.d := rfl
  have cap : a.packetEnd+8+a.h ≤ a.powerBase := bank.2.1
  have H : a.header.header+13+2*a.header.entries+a.header.a = a.header.packetBase := rfl
  have primary (j : ℕ) (hj : j < 112) (different : j ≠ 13) : out (frame+j) = orig (frame+j) := by
    exact same _ (by omega) (by omega)
  have primary' (j : ℕ) (hj : j < 112) (different : j ≠ 13) :
      frameField p out j = frameField p orig j := by
    simp only [frameField,words.frameBase]
    exact primary _ hj different
  have hWord (j : ℕ) (hj : j < 13) : out (a.header.header+j) = orig (a.header.header+j) :=
    same _ (by omega) (by omega)
  have entry (s t : Fin a.header.d) (j : Fin (a.n+1)) :
      out (a.header.header+13+a.header.entries+(CubeLengths.entryOrder a.header.d (a.n+1) ((s,t),j)).val) =
      orig (a.header.header+13+a.header.entries+(CubeLengths.entryOrder a.header.d (a.n+1) ((s,t),j)).val) := by
    have hk := (CubeLengths.entryOrder a.header.d (a.n+1) ((s,t),j)).isLt
    change _ < a.header.d*a.header.d*(a.n+1) at hk
    have shape : a.header.d*a.header.d*(a.n+1) = a.header.entries := by simp [Inputs.entries,axes]
    have hke := hk.trans_le shape.le
    exact same _ (by omega) (by omega)
  have inputs := words.setup
  have loaded : (LocalRow.rowLayout a.header a.b a.h a.powerBase).Loaded a.n p out :=
    ⟨(primary' 59 (by decide) (by decide)).trans inputs.d,(primary' 60 (by decide) (by decide)).trans inputs.axes,
     (primary' 61 (by decide) (by decide)).trans inputs.bc,(primary' 62 (by decide) (by decide)).trans inputs.power,
     (primary' 63 (by decide) (by decide)).trans inputs.header,(hWord 7 (by decide)).trans inputs.blocks,
     (hWord 8 (by decide)).trans inputs.bank,fun j hj =>
       (same (a.powerBase+j) (by omega) (by omega)).trans (inputs.powers j hj)⟩
  exact ⟨words.frameBase,loaded,(hWord 0 (by decide)).trans words.actual,(hWord 1 (by decide)).trans words.claimed,
    fun u v j => (entry u v j).trans (words.table u v j),(primary 0 (by decide) (by decide)).trans words.teamID,
    (primary 56 (by decide) (by decide)).trans words.labelCount,(primary 77 (by decide) (by decide)).trans words.ownersBase,
    (primary 78 (by decide) (by decide)).trans words.triples,(primary 85 (by decide) (by decide)).trans words.views,
    (primary 86 (by decide) (by decide)).trans words.spacing,(primary 88 (by decide) (by decide)).trans words.singleBase,
    (hWord 5 (by decide)).trans words.chosen,(hWord 6 (by decide)).trans words.selectorCount,
    fun g => (same (a.ownerBase+g.val) (by have := g.isLt; omega) (by omega)).trans (words.owners g)⟩

end RoutingISA.CubeArena

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins}
  {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}

/-- A real returning team delivery and the following native lookup installation
preserve all the scanner metadata of the shared writer's physical input. -/
theorem SharedWriters.scannerWords_after_install (writer : SharedWriters f g src) (ar : CubeArena.Layout)
    (frame count axis : ℕ) (u : Fin (R+1)) (group : Fin ar.header.d → ℕ)
    (rows : Sym2 (Fin ar.header.d) → Fin (ar.n+1) → ℕ) (template : Frame)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (table : f.table = ar.table frame count)
    (physicalFrame : g.frame = frame) (frameLow : frame+112 ≤ ar.header.header)
    (axes : ar.header.a = ar.n+1)
    (source : ar.ScannerWords frame u.val axis group (readings (H u).pub) (src u) rows) :
    let layout := CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s
    let idBase := CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s
    CubeConstants.Fits layout w (readings (H u).pub 0) idBase id →
      CubeConstants.Fields layout (readings (H u).pub 0) idBase (readings (H u).history.val.2.2) →
      ∀ {es out mem}, Runs (H u).pub (H u).macros (CubeConstants.install id)
        (H u).history.val.2.1 (H u).history.val.2.2 es out mem →
        ar.ScannerWords frame u.val axis group (readings (H u).pub) (readings mem) rows := by
  intro layout idBase fit fields es out mem run
  apply source.transfer axes frameLow
  intro x hx different
  have records : ar.pairDirectory ≤ ar.records := by unfold CubeArena.Layout.records CubeArena.Layout.hostDirectory; omega
  have post : ar.pairDirectory ≤ ar.stop := by
    unfold CubeArena.Layout.stop CubeArena.Layout.cellBank CubeArena.Layout.pairBase TableLayout.reserveEnd
      CubeArena.Layout.records CubeArena.Layout.hostDirectory
    omega
  have kept := TeamHistory.install_before (H u) layout idBase id fit fields run x (hx.trans_le post)
  have prior := writer.returned_static ar frame count table u x (hx.trans_le records) (physicalFrame ▸ different)
  exact (congrArg Fin.val kept).trans prior

end TeamContraction

end BorderVNP
end Computability
end OAI
