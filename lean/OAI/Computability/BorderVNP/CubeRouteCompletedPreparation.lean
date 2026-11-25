import OAI.Computability.BorderVNP.CubeRouteCompleteSchedule

/-! # Joint route preparation from completed native schedules -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube BorderVNP.Cube.Physical PackedHistoryCircuit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
variable {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}
variable {frame : ℕ} {pub : Fin (R+1) → Arg → Word w} {mac : Fin (R+1) → TeamOpcode.Macros w 8}
variable {startReg endReg : Fin (R+1) → Bank w} {initial final : Fin (R+1) → Memory w}
variable {log : Fin (R+1) → List (TeamRAM.Event w)} {dst ib hb sb : Fin (R+1) → ℕ}
variable {guess : Fin (R+1) → ℕ → Bool}
local notation "entries" => List.length (D.directory pp lp)
local notation "sharedLayout" => ar.sharedRows frame (Fin.val (Prod.fst decl)) (List.length (D.directory pp lp))
local notation "tab" => ar.table frame (List.length (D.directory pp lp)+ar.header.d.choose 2)
local notation "row" => RouteRecords.combinedRow (D.directory pp lp) owner ar.header.blocks ar.K ar.h decl group
local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
local notation "PF" => fun u => G.processorFields u pin ext (ib u) (hb u) (sb u)
local notation "BF" => fun u => G.transferFrame u wire.header (dst u)

/-- The native pre-scheduler certificate and the actual source words required by both
directions of the transmission theorem. All writer-entry fields come from the recovered histories. -/
theorem SharedRoutePrepared.of_complete_schedules
    (H : ∀ u, WriterHistory ar.n (Tally.selectorWidth ar.n ar.K ar.h) (pub u) (mac u)
      (startReg u) (initial u) (log u) (endReg u) (final u))
    (done : ∀ u, ReturnedWriters ar D pp lp owner decl group ((PL) u) (H u))
    (teamCount : R+1 = ar.teams) (enough : 2 < ar.teams) (widths : wire.width = tableWidth tab row teamCount)
    (space : entries+ar.header.d.choose 2 ≤ ar.maxRows) (arenaFit : ar.stop < 2^w) (rowFit : (tab).RowsFit w row)
    (capacity : ∀ u x y, wire.header+legLoad enough ((tab).widthMatrix row) x y+
      legLoad enough ((tab).widthMatrix row) y x ≤ ((BF) u).capacity)
    (low : frame+112 ≤ ar.header.header) (base : ∀ u, (pub u 0).val = frame)
    (pointers : ∀ u, TablePointers tab (readings (initial u)))
    (sources : ∀ u, ProfileRouteInputs ((PF) u) ((BF) u) (pub u) (guess u) (initial u))
    (inputRoom : ∀ u, ((PF) u).header.length ≤ frame)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+((PL) u).count ≤ ar.header.header)
    (frameFit : ∀ u, ((BF) u).Fits w (pub u 0).val)
    {I : Type*} [Fintype I] (cell : I → Fin ar.cells) (id : I ↪ ℕ) (width : I → ℕ)
    (placement : Packing.Directory.BankPlacement D pp lp I cell id width) (bounds : D.DestinationBounds)
    (slabs : ∀ c, Packing.Directory.DataSlabs.size cell width c ≤ ar.cellStride)
    (processors : D.processors = r) (literal : D.literal = G.program.length+t) :
    SharedRoutePrepared G pin ext wire D pp lp owner ar.cellBank ar.cellStride tab row pub final dst ib hb sb guess ∧
      ∀ u, Runs (pub u) (mac u) (scheduleGroups ar.n (Tally.selectorWidth ar.n ar.K ar.h))
        (startReg u) (initial u) (log u) (endReg u) (final u) ∧
        (sharedLayout).Emitted (readings (H u).sharedInput) (readings (final u)) ∧
        (sharedLayout).Fits w (readings (H u).sharedInput) ∧
        SymbolFrame sharedLayout (readings (H u).sharedInput) ar.header.blocks ar.K ar.h decl group := by
  have atWriter (u : Fin (R+1)) :
      (sharedLayout).Fields (readings (H u).sharedInput) ∧ (sharedLayout).Fits w (readings (H u).sharedInput) ∧
      SymbolFrame sharedLayout (readings (H u).sharedInput) ar.header.blocks ar.K ar.h decl group := by
    have eqn := (H u).dataImage (done u).emission.demand.ready
    rw [eqn,← base u]
    exact ⟨(done u).emission.sharedFields,(done u).emission.sharedFit,(done u).emission.symbols⟩
  obtain ⟨ready,rs⟩ := SharedRoutePrepared.of_scheduled_writers H (fun u => (done u).emission.demand)
    teamCount enough widths space arenaFit rowFit capacity low base (fun u => (done u).low) pointers sources inputRoom subRoom
    frameFit (fun u => (atWriter u).1) (fun u => (atWriter u).2.1) (fun u => (atWriter u).2.2)
    (fun u => (done u).emission.pinLayout) cell id width placement bounds slabs processors literal
  exact ⟨ready,fun u => ⟨(rs u).1,(rs u).2,(atWriter u).2⟩⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
