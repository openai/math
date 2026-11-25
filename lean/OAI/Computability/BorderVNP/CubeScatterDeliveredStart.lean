import OAI.Computability.BorderVNP.CubeScatterTransmissionPayload
import OAI.Computability.BorderVNP.RoutingISACubeConstantArena
import OAI.Computability.BorderVNP.RoutingISACheckLoop
import OAI.Computability.BorderVNP.CubeISALocalRowFrame

/-! # Carrying the returned transmission words through the actual cube installation

The signed input stage installs the fixed cube tables before scanning its owned
groups. Both directed endpoint views survive those writes when the table arena
starts after the last pair buffer. The conclusion holds for the memory of every
returning native execution, so it can be used when reading a passing history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter DiagonalTallyPacketEmit

open private detOfUnsigned from OAI.Computability.BorderVNP.CubeISALocalRowFrame

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {a q blocks K h b s : ℕ}

/-- The actual return of the table installer leaves the input words below the
fresh pointer unchanged, including every ordered pair buffer and the extended frame. -/
theorem TeamHistory.install_before (hist : TeamHistory w) (frame : Frame)
    (idBase : ℕ) (id : TableEntry a b h K s → ℕ)
    (fit : CubeConstants.Fits frame w (readings hist.pub 0) idBase id)
    (fields : CubeConstants.Fields frame (readings hist.pub 0) idBase (readings hist.history.val.2.2))
    {es out mem} (run : Runs hist.pub hist.macros (CubeConstants.install id)
      hist.history.val.2.1 hist.history.val.2.2 es out mem) (j : ℕ) (below : j < frame.zeroAddr) :
    mem j = hist.history.val.2.2 j := by
  have ht := CubeConstants.install_run hist.pub hist.macros hist.history.val.2.1 hist.history.val.2.2 frame idBase id fit fields
  have hit := (ht.asTest (detOfUnsigned _ (CubeConstants.install_unsigned id).1)).sound run
  have eq := congrFun hit.2 j
  exact Fin.ext (eq.trans (CubeConstants.image_before frame idBase id _ fit j below))

/-- The actual signed input installer returns, for the same registers and RAM as
the completed transmission. Its exact slot bound carries through to all protected reads. -/
theorem TeamHistory.install_for_scan (hist : TeamHistory w) (frame : Frame) (idBase : ℕ)
    (id : TableEntry a b h K s → ℕ)
    (fit : CubeConstants.Fits frame w (readings hist.pub 0) idBase id)
    (fields : CubeConstants.Fields frame (readings hist.pub 0) idBase (readings hist.history.val.2.2)) :
    BoundedRun hist.pub hist.macros (CubeConstants.install id) hist.history.val.2.1 hist.history.val.2.2
      (CubeConstants.install id).slots (fun z => z.mem = CubeConstants.image frame idBase id (readings hist.history.val.2.2) ∧
        ∀ j < frame.zeroAddr, z.mem j = readings hist.history.val.2.2 j) :=
  (CubeConstants.install_run hist.pub hist.macros hist.history.val.2.1 hist.history.val.2.2 frame idBase id fit fields).mono
    le_rfl (fun _ eq => ⟨eq,fun j hj => (congrFun eq j).trans (CubeConstants.image_before frame idBase id _ fit j hj)⟩)

variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
  {src : Fin (R+1) → ℕ → ℕ} {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

/-- For any owned strict row, the scanner starts with the real decoded selector and
crossing words at the two correct pointers in the returned memory of the fixed-table installer. -/
theorem SharedWriters.scanner_streams (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) blocks K h decl group)
    (select : Packet a q blocks → Selector a K h) (pass : passesLengths b s select decl)
    (supply : (p : Packet a q blocks) → (e : Cube.Edge (a+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (single : SingleSlot a q blocks (h*b) → Bool)
    (emits : sharedWords decl ⟨⟨select,pass⟩,fun _ => rowCrossValue supply single⟩ = f.receivedRows g group)
    (p : Symbols q) (high : Bool) (frame : Frame) (idBase : ℕ) (id : TableEntry a b h K s → ℕ)
    (arena : g.banks+g.stride*g.groups^2 ≤ frame.zeroAddr) :
    let team := if high then group p.val.2 else group p.val.1
    let base := if high then g.view p.val.2 p.val.1 else g.view p.val.1 p.val.2
    let hist := H team
    let sel := commonSelectors select decl.1 p
    CubeConstants.Fits frame w (readings hist.pub 0) idBase id →
      CubeConstants.Fields frame (readings hist.pub 0) idBase (readings hist.history.val.2.2) →
      ∀ {es out mem}, Runs hist.pub hist.macros (CubeConstants.install id)
        hist.history.val.2.1 hist.history.val.2.2 es out mem →
        Resident (pairRegion g) mem base sel ∧
        Resident (pairRegion g) mem (base+sel.length) (commonCrossings b decl.1 p select supply single) := by
  intro team base hist sel fit fields es out mem run
  obtain ⟨prefixWords,suffixWords⟩ := writer.physical_streams symbols select pass supply single emits p high
  have preserved (j : ℕ) (hj : j ∈ pairRegion g) : mem j = hist.history.val.2.2 j :=
    TeamHistory.install_before hist frame idBase id fit fields run j (hj.2.trans_le arena)
  exact ⟨prefixWords.congr preserved,suffixWords.congr preserved⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
