import OAI.Computability.BorderVNP.CubeRouteRawHistogram
import OAI.Computability.BorderVNP.CubeRouteCommonSchedules
import OAI.Computability.BorderVNP.CubeRouteCalibratedPreparation

/-! # Constructing the joint route on the actual pinned public schedule -/

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

/-- Bind the table's size, every receiving cell, the group histogram, its scaled guard, and the link
capacities to the real pre-scheduling word image at team zero. The canonical receipts of all teams
come from their actual eleven-stage returns. The only preliminary wire parameter is the length of
the common header. -/
theorem pinned_sharedRoutePrepared {α ξ : ℝ} {scale : ℕ} (calibrated : RouteRecords.FitsLinksAt α ξ scale)
    (H : ∀ u, WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) (pub u) (mac u) (startReg u) (initial u)
      (log u) (endReg u) (final u))
    (teamCount : R+1=ar.teams) (enough : 2 < ar.teams) (space : entries+ar.header.d.choose 2 ≤ ar.maxRows)
    (arenaFit : ar.stop < 2^w) (low : frame+112 ≤ ar.header.header) (base : ∀ u, (pub u 0).val=frame)
    (pointers : ∀ u, TablePointers tab (readings (initial u)))
    (sources : ∀ u, ProfileRouteInputs ((PF) u) ((BF) u) (pub u) (guess u) (initial u))
    (inputRoom : ∀ u, ((PF) u).header.length ≤ frame)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+((PL) u).count ≤ ar.header.header)
    (frameFit : ∀ u, ((BF) u).Fits w (pub u 0).val)
    {I : Type*} [Fintype I] (cell : I → Fin ar.cells) (id : I ↪ ℕ) (widths : I → ℕ)
    (slotted : Memory w) (dest : ℕ) (P : SlottedWriter ar D pp lp ((PL) 0) (pub 0) slotted dest cell id widths)
    (published : initial 0=Packing.Directory.ISA.publish slotted (pub 0 0).val dest (D.directory pp lp))
    (processors : D.processors=r) (literal : D.literal=G.program.length+t) (sourceTeams : D.teams=R+1)
    (procs : 0 < D.processors) (fieldBound : D.fields ≤ 2) (block : 0 < D.block)
    (literalRoom : D.literal ≤ TeamScales.literal α scale)
    (teamRoom : (ar.teams : ℝ) ≤ (scale:ℝ)^(2*α)) (headerRoom : (header : ℝ) ≤ r*(scale:ℝ)^(24/25:ℝ))
    (linkRoom : link=TeamScales.link ξ ar.teams scale)
    (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell : ℕ) (profile : List Bool) (claims : List (List Bool))
    (pad : ℕ) (rawDecl : Broadcast ar.n ar.header.d ar.header.cap) (selected : Memory w) {fs reg}
    (labelRun : Runs (pub 0) (mac 0) (.seq LabelIndex.directoryProgram NativeIntervals.prepare) (startReg 0) (initial 0) fs reg selected) :
    let f := (BF) 0
    let raw := padded (spelling (profile++DeclarationBits.spelling rawDecl) claims) pad
    let physical := geometryInputs fresh profile.length gates outputs bitWidth w ar.header.d ar.n ar.header.blocks ar.b ar.h ar.s
    let fields := jointFields (ar.extension old) fresh profile.length gates outputs bitWidth off ell
      ar.header.d ar.n ar.header.blocks ar.b ar.h ar.s
    let axis := Fin.ofNat (ar.n+1) (readCode (ar.n+1) rawDecl.1)
    let decl : LengthDeclaration ar.n ar.header.d := ⟨axis,fun p j => readCode (ar.header.cap+1) (rawDecl.2 p j)⟩
    let orig := powerHeaderImage ar f.dst (readings selected)
    let wl := weightLayout ar frame axis.val
    let group := fun g : Fin ar.header.d => TeamNative.owner R (wl.weight orig) g.val
    let owner := ar.receivingOwner frame axis R orig
    let g := ar.sharedRows frame axis.val entries
    let row := RouteRecords.combinedRow (D.directory pp lp) owner ar.header.blocks ar.K ar.h decl group
    BootPins (pub 0) f fields raw (initial 0) → ar.header=physical → f.dst+raw.length ≤ ar.header.header →
      0 < ar.header.d → 0 < ar.header.blocks → 0 < bankWidth ar.n ar.b ar.h ar.K ar.s →
      LabelPrefixFits frame w (readings (initial 0)) → readings (initial 0) (frame+11)=ar.cells →
      (old 0).val=TeamScales.exterior ξ r scale → 1000000 < 2^w → 1000000*TeamScales.exterior ξ r scale*(R+1) < 2^w →
      declarationInRange rawDecl → 1000000*(ar.stop+3*D.teams*(D.processors*D.literal))+2*ar.stop < 2^w →
      (∀ u, ReturnedWriters ar D pp lp owner decl group ((PL) u) (H u)) →
      ∃ L : WireLayout (R+1) r link, L.header=header ∧ L.width=tableWidth tab row teamCount ∧
        SharedRoutePrepared G pin ext L D pp lp owner ar.cellBank ar.cellStride tab row pub final dst ib hb sb guess ∧
        ∀ u, g.Emitted (readings (H u).sharedInput) (readings (final u)) ∧ g.Fits w (readings (H u).sharedInput) ∧
          SymbolFrame g (readings (H u).sharedInput) ar.header.blocks ar.K ar.h decl group := by
  intro f raw physical fields axis decl orig wl group owner g row pins shape copied groups blocks stride fit cellCount
    budget million scaled valid rawRoom done
  have columns := P.guard_columns arenaFit
  dsimp only at columns
  rw [← published] at columns
  have rawMass := P.raw_histogram_room f old fresh gates outputs bitWidth off ell (mac 0) (startReg 0)
    profile claims pad rawDecl
  dsimp only at rawMass
  rw [← published,base 0] at rawMass
  have mass : (∑ i ∈ Finset.range ar.header.d, wl.weight orig i) < 2^w := by
    change (∑ i ∈ Finset.range ar.header.d, (weightLayout ar frame axis.val).weight orig i) < 2^w
    have axisEq : axis.val=readCode (ar.n+1) rawDecl.1 := Nat.mod_eq_of_lt valid.1
    rw [axisEq]
    exact rawMass pins shape low copied groups blocks stride arenaFit fit cellCount procs block fieldBound rawRoom labelRun valid
  have native := native_guard_inventory (pub 0) f ar old fresh gates outputs bitWidth off ell (mac 0) (startReg 0)
    (initial 0) profile claims pad rawDecl R (TeamScales.exterior ξ r scale) (D.directory pp lp) selected labelRun
  dsimp only at native
  rw [base 0] at native columns
  obtain ⟨label,recv,image,setup,cells,accepted⟩ := native pins shape low copied groups blocks stride arenaFit fit
    cellCount rfl teamCount.symm budget million scaled valid mass columns.1 columns.2
  exact calibrated_sharedRoutePrepared calibrated H done teamCount enough space arenaFit low base pointers sources
    inputRoom subRoom frameFit cell id widths P.placement P.destinations P.slabs processors literal orig label recv
    (fun j : Fin entries => (D.directory pp lp)[j.val].width) image setup (Equiv.refl _) (fun _ => rfl)
    (fun i => (cells i).2) sourceTeams P.tailRoom procs P.fields fieldBound block literalRoom teamRoom headerRoom linkRoom accepted

end TeamContraction

end BorderVNP
end Computability
end OAI
