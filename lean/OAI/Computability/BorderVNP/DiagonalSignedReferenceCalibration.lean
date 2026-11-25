import OAI.Computability.BorderVNP.DiagonalSignedCalibratedWriters
import OAI.Computability.BorderVNP.CubeRouteExteriorTables

/-! # The calibrated reference route on the common geometric cell owners -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open BorderVNP.Cube BorderVNP.Cube.Physical Tally LocalRow CubeHeaderInstall JointHeader PackedHistoryCircuit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {header : ℕ}
variable {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {frame : ℕ}
variable {pub : Fin (R+1) → Arg → Word w} {mac : Fin (R+1) → TeamOpcode.Macros w 8}
variable {startReg endReg : Fin (R+1) → Bank w} {initial final : Fin (R+1) → Memory w}
variable {log : Fin (R+1) → List (TeamRAM.Event w)} {dst ib hb sb : Fin (R+1) → ℕ}
variable {guess : Fin (R+1) → ℕ → Bool}

local notation "entries" => List.length (D.directory pp lp)
local notation "tab" => ar.table frame (List.length (D.directory pp lp)+ar.header.d.choose 2)
local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
local notation "PF" => fun u => G.processorFields u pin ext (ib u) (hb u) (sb u)
local notation "BF" => fun u => G.transferFrame u header (dst u)

set_option maxRecDepth 5000
set_option maxHeartbeats 1400000

/-- At a genuine reference return, use the geometric owner function on all valid physical cells.
The calibration follows the populated directory, so its capacity and word bounds extend to
this common representation, including headers with zero-width live rows. -/
theorem signed_reference_writer_layout {α ξ : ℝ} {scale : ℕ} (fit : Diagonal.RouteTableInputs ar D α ξ scale w frame link)
    (H : ∀ u, WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) (pub u) (mac u) (startReg u) (initial u)
      (log u) (endReg u) (final u))
    (base : ∀ u,(pub u 0).val=frame)
    (pointers : ∀ u,TablePointers tab (readings (initial u)))
    (sources : ∀ u,ProfileRouteInputs ((PF) u) ((BF) u) (pub u) (guess u) (initial u))
    (inputRoom : ∀ u,((PF) u).header.length≤frame)
    (subRoom : ∀ u,frame+13 < ib u ∧ ib u+((PL) u).count ≤ ar.header.header)
    (frameFit : ∀ u, ((BF) u).Fits w (pub u 0).val)
    {I : Type*} [Fintype I] (cell : I → Fin ar.cells) (id : I ↪ ℕ) (widths : I → ℕ)
    (slotted : Memory w) (dest : ℕ) (P : SlottedWriter ar D pp lp ((PL) 0) (pub 0) slotted dest cell id widths)
    (published : initial 0 = Packing.Directory.ISA.publish slotted (pub 0 0).val dest (D.directory pp lp))
    (processors : D.processors=r) (literal : D.literal=G.program.length+t) (sourceTeams : D.teams=R+1)
    (literalRoom : D.literal ≤ TeamScales.literal α scale) (headerRoom : (header:ℝ) ≤ r*(scale:ℝ)^(24/25:ℝ))
    (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell controls : ℕ) (profile : List Bool)
    (claims : List (List Bool)) (pad : ℕ) (word : Broadcast ar.n ar.header.d ar.header.cap)
    (room : SignedPrep.PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub 0) (slotted:=slotted)
      (base:=dest) ((BF) 0) old fresh gates outputs bitWidth off ell controls profile claims pad word R (TeamScales.exterior ξ r scale))
    (representative : ℕ → Fin (R+1)) (groups : Fin ar.header.d → Fin (R+1))
    (valid : declarationInRange word) (selected : Memory w) {es reg}
    (label : Runs (pub 0) (mac 0) (.seq LabelIndex.directoryProgram NativeIntervals.prepare) (startReg 0) (initial 0) es reg selected) :
    let axis := Fin.ofNat (ar.n+1) (readCode (ar.n+1) word.1)
    let decl : LengthDeclaration ar.n ar.header.d := ⟨axis,fun p j => readCode (ar.header.cap+1) (word.2 p j)⟩
    let input := powerHeaderImage ar ((BF) 0).dst (readings selected)
    let wl := weightLayout ar frame axis.val
    let group := fun j : Fin ar.header.d => TeamNative.owner R (wl.weight input) j.val
    let owner := ar.receivingOwner frame axis R input
        let row := RouteRecords.combinedRow (D.directory pp lp) representative ar.header.blocks ar.K ar.h decl groups
    (∀ c : Fin ar.cells, owner c.val=representative c.val) → group=groups →
    (∀ u, ReturnedWriters ar D pp lp representative decl groups ((PL) u) (H u)) →
    ∃ L : WireLayout (R+1) r link, L.header=header ∧
      SharedRoutePrepared G pin ext L D pp lp representative ar.cellBank ar.cellStride tab row pub final dst ib hb sb guess := by
  intro axis decl input wl group owner row owners groupEq done
  have physical (u : Fin (R+1)) : ReturnedWriters ar D pp lp owner decl group ((PL) u) (H u) :=
    (done u).congr_tables rfl P.placement P.destinations (fun c hc => (owners ⟨c,hc⟩).symm) groupEq.symm
  obtain ⟨L,head,_,prepared,_⟩ := signed_calibrated_writer_layout fit H base pointers sources inputRoom subRoom frameFit cell id
    widths slotted dest P published processors literal sourceTeams literalRoom headerRoom old fresh gates outputs bitWidth
    off ell controls profile claims pad word room valid selected label physical
  let physicalRow := RouteRecords.combinedRow (D.directory pp lp) owner ar.header.blocks ar.K ar.h decl group
  have eqn : physicalRow = row := RouteRecords.combinedRow_congr _ _ _ _ rfl
    (fun i => owners ⟨_,BankPlacement.populated_cell_lt P.placement P.destinations i⟩) groupEq
  dsimp only [physicalRow,row] at eqn
  refine ⟨L,head,?_⟩
  apply (SharedRoutePrepared.of_complete_schedules (wire:=L) H done room.teamArena.symm fit.teams
    (by rw [←eqn]; exact prepared.widths)
    (fit.tables pp lp).1 fit.ceiling (by rw [←eqn]; exact prepared.rowFit)
    (by rw [←eqn]; exact prepared.capacity) fit.frameBefore base pointers ?_ inputRoom subRoom
    ?_ cell id widths P.placement P.destinations P.slabs processors literal).1
  · simpa only [head] using sources
  · simpa only [head] using frameFit

end TeamContraction

end BorderVNP
end Computability
end OAI
