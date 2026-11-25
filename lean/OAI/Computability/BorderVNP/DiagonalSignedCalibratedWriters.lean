import OAI.Computability.BorderVNP.CubeRouteCalibratedPinned
import OAI.Computability.BorderVNP.DiagonalSelectedRouteTable
import OAI.Computability.BorderVNP.RoutingISASignedAdmittedWriters

/-! # Calibrating the signed shared wire at the actual published guard inputs -/

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

/-- The genuine signed raw-input certificate and selected route scale yield the
per-exterior layout required by the signed preparation frame. In particular its
link-capacity bounds are computed from the actual returned label memory of team zero. -/
theorem signed_calibrated_writer_layout {α ξ : ℝ} {scale : ℕ} (fit : Diagonal.RouteTableInputs ar D α ξ scale w frame link)
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
    (valid : declarationInRange word) (selected : Memory w) {es reg}
    (label : Runs (pub 0) (mac 0) (.seq LabelIndex.directoryProgram NativeIntervals.prepare) (startReg 0) (initial 0) es reg selected) :
    let axis := Fin.ofNat (ar.n+1) (readCode (ar.n+1) word.1)
    let decl : LengthDeclaration ar.n ar.header.d := ⟨axis,fun p j => readCode (ar.header.cap+1) (word.2 p j)⟩
    let input := powerHeaderImage ar ((BF) 0).dst (readings selected)
    let wl := weightLayout ar frame axis.val
    let group := fun j : Fin ar.header.d => TeamNative.owner R (wl.weight input) j.val
    let owner := ar.receivingOwner frame axis R input
    let g := ar.sharedRows frame axis.val entries
    let row := RouteRecords.combinedRow (D.directory pp lp) owner ar.header.blocks ar.K ar.h decl group
    (∀ u,ReturnedWriters ar D pp lp owner decl group ((PL) u) (H u)) →
    ∃ L : WireLayout (R+1) r link,L.header=header ∧ L.width=tableWidth tab row room.teamArena.symm ∧
      SharedRoutePrepared G pin ext L D pp lp owner ar.cellBank ar.cellStride tab row pub final dst ib hb sb guess ∧
      ∀ u, g.Emitted (readings (H u).sharedInput) (readings (final u)) ∧ g.Fits w (readings (H u).sharedInput) ∧
        SymbolFrame g (readings (H u).sharedInput) ar.header.blocks ar.K ar.h decl group := by
  intro axis decl input wl group owner g row done
  apply pinned_sharedRoutePrepared fit.links H room.teamArena.symm fit.teams (fit.tables pp lp).1 fit.ceiling
    fit.frameBefore base pointers sources inputRoom subRoom frameFit cell id widths slotted dest P published
    processors literal sourceTeams room.processors room.fields room.payload literalRoom fit.teamBound headerRoom
    fit.physicalLink old fresh gates outputs bitWidth off ell profile claims pad word selected label
  · rw [published]; exact room.boot
  · exact room.geometry
  · exact room.copied
  · exact Nat.zero_lt_of_lt room.alphabet
  · exact room.blocks
  · exact room.bank
  · rw [published,←base 0]; exact room.labels
  · rw [published,←base 0]; exact room.cells
  · exact room.budget
  · exact room.million
  · exact room.scaled
  · exact valid
  · exact room.rawSpace
  · exact done

end TeamContraction

end BorderVNP
end Computability
end OAI
