import OAI.Computability.BorderVNP.CubeRouteWriterReadback
import OAI.Computability.BorderVNP.CubeScatterTransmissionRealization

/-! # Joint transmission preparation at the return of the signed native schedule -/

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

/-- The group schedule's real consecutive writer returns populate a single common routing
table. Both data and shared records, every assigned receiving bank, the transfer operands,
and every original and substituted input word are certified on the returned memories. -/
theorem SharedRoutePrepared.of_scheduled_writers
    (H : ∀ u, WriterHistory ar.n (Tally.selectorWidth ar.n ar.K ar.h) (pub u) (mac u)
      (startReg u) (initial u) (log u) (endReg u) (final u))
    (demand : ∀ u, DemandInput ar D pp lp owner (pub u) (H u).dataInput)
    (teamCount : R+1 = ar.teams) (enough : 2 < ar.teams)
    (widths : wire.width = tableWidth tab row teamCount)
    (space : entries+ar.header.d.choose 2 ≤ ar.maxRows) (arenaFit : ar.stop < 2^w)
    (rowFit : (tab).RowsFit w row)
    (capacity : ∀ u x y, wire.header+legLoad enough ((tab).widthMatrix row) x y+
      legLoad enough ((tab).widthMatrix row) y x ≤ ((BF) u).capacity)
    (low : frame+112 ≤ ar.header.header) (base : ∀ u, (pub u 0).val = frame)
    (prior : ∀ u x, x < ar.header.header → (H u).dataInput x = initial u x)
    (ptr : ∀ u, TablePointers tab (readings (initial u)))
    (sources : ∀ u, ProfileRouteInputs ((PF) u) ((BF) u) (pub u) (guess u) (initial u))
    (inputLow : ∀ u, ((PF) u).header.length ≤ frame)
    (subLow : ∀ u, frame+13 < ib u ∧ ib u+((PL) u).count ≤ ar.header.header)
    (frameFit : ∀ u, ((BF) u).Fits w (pub u 0).val)
    (fields : ∀ u, (sharedLayout).Fields (readings (H u).sharedInput))
    (fitted : ∀ u, (sharedLayout).Fits w (readings (H u).sharedInput))
    (symbols : ∀ u, SymbolFrame sharedLayout (readings (H u).sharedInput) ar.header.blocks ar.K ar.h decl group)
    (pins : ∀ u, (DataWriter.layout (readings (pub u)) (readings (H u).dataInput)).pins = (PL) u)
    {I : Type*} [Fintype I] (cell : I → Fin ar.cells) (id : I ↪ ℕ) (width : I → ℕ)
    (placement : Packing.Directory.BankPlacement D pp lp I cell id width) (bounds : D.DestinationBounds)
    (slabs : ∀ c, Packing.Directory.DataSlabs.size cell width c ≤ ar.cellStride)
    (processors : D.processors = r) (literal : D.literal = G.program.length+t) :
    SharedRoutePrepared G pin ext wire D pp lp owner ar.cellBank ar.cellStride tab row pub final dst ib hb sb guess ∧
      ∀ u, Runs (pub u) (mac u) (scheduleGroups ar.n (Tally.selectorWidth ar.n ar.K ar.h))
        (startReg u) (initial u) (log u) (endReg u) (final u) ∧ (sharedLayout).Emitted (readings (H u).sharedInput) (readings (final u)) := by
  have below := secondary_le_records ar
  have fr : frame+31 ≤ ar.records := by omega
  have allocated := ar.table_allocated enough fr space arenaFit
  have recLow : ar.records ≤ ar.pairBase := by unfold CubeArena.Layout.pairBase TableLayout.reserveEnd; omega
  have pack (u : Fin (R+1)) := by
    let d := DataWriter.layout (readings (pub u)) (readings (H u).dataInput)
    have dp : D.processors = d.pins.processors := by rw [show d.pins = _ from pins u]; exact processors
    have dl : D.literal = d.pins.literal := by rw [show d.pins = _ from pins u]; exact literal
    have inp : d.pins.processors*d.pins.stride ≤ ar.pairBase := by
      rw [show d.pins = _ from pins u]
      have fit := (frameFit u).input
      have stride : ((PL) u).stride = ((BF) u).stride := by
        dsimp [Wiring.pinLayout,Wiring.transferFrame,Pins.Layout.stride,Pins.Layout.offset,BroadcastFrame.stride]
        omega
      rw [stride]
      exact fit.trans ((base u).symm ▸ ((Nat.le_add_right ..).trans (fr.trans recLow)))
    have sub : d.pins.ibase+d.pins.count ≤ ar.pairBase := by
      rw [show d.pins = _ from pins u]
      exact (subLow u).2.trans (below.trans recLow)
    exact (H u).placed (ar := ar) (g := sharedLayout) (decl := decl) (demand u) (base u) rfl rfl rfl rfl rfl rfl
      enough fr space arenaFit (fields u) (fitted u) (symbols u) cell id width placement bounds slabs dp dl inp sub
  have source (u : Fin (R+1)) := (H u).routeSources ar frame decl.1.val entries (demand u).ready (base u)
    (demand u).records (pack u).1 low (prior u) ((PL) u) ((BF) u) ((PF) u) (guess u) teamCount (inputLow u)
    (subLow u) (sources u) (ptr u)
  refine ⟨⟨teamCount,widths,allocated.1,TableLayout.reserve_ordered fr space,rowFit,base,
    fun u => (source u).1,fun u => (pack u).2.1,fun u => (source u).2.broadcast,frameFit,capacity,
    fun u => (source u).2.physical,fun u => (inputLow u).trans ((Nat.le_add_right ..).trans fr),
    fun u => ?_,fun u => (source u).2.substituted,fun u => (subLow u).2.trans below⟩,fun u => ⟨(H u).runs,(pack u).1⟩⟩
  have pinEq : (DataWriter.layout (readings (pub u)) (readings (H u).dataInput)).pins = G.pinLayout u (ib u) (hb u) (sb u) := pins u
  rw [← pinEq]
  exact (pack u).2.2

end TeamContraction

end BorderVNP
end Computability
end OAI
