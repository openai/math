import OAI.Computability.BorderVNP.CubeRouteCalibratedTable
import OAI.Computability.BorderVNP.CubeRouteCompletedPreparation

/-! # The physical wire layout obtained from the genuine guarded schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube BorderVNP.Cube.Physical PackedHistoryCircuit

/-- The common native table fixes both routed directions of every physical block.
The header length is chosen before scheduling and is independent of its payload. -/
def scheduledWire {N r link : ℕ} (tab : TableLayout) (row : ℕ → TableRow) (header : ℕ)
    (teams : N = tab.teams) (enough : 2 < tab.teams)
    (fits : ∀ x y, header+legLoad enough (tab.widthMatrix row) x y+legLoad enough (tab.widthMatrix row) y x ≤ r*link) :
    WireLayout N r link := by
  subst N
  exact ⟨enough,tab.widthMatrix row,header,fun b => fits b.val.1 b.val.2⟩

theorem scheduledWire_fields {N r link : ℕ} (tab : TableLayout) (row : ℕ → TableRow) (header : ℕ)
    (teams : N = tab.teams) (enough : 2 < tab.teams)
    (fits : ∀ x y, header+legLoad enough (tab.widthMatrix row) x y+legLoad enough (tab.widthMatrix row) y x ≤ r*link) :
    let L := scheduledWire tab row header teams enough fits
    L.header = header ∧ L.width = tableWidth tab row teams := by
  subst N
  exact ⟨rfl,rfl⟩

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {header : ℕ}
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
local notation "BF" => fun u => G.transferFrame u header (dst u)
local notation "weights" => LocalRow.weightLayout ar frame (Fin.val (Prod.fst decl))
local notation "teamLayout" => LocalRow.teamLayout ar R

/-- Recover the true wire allocation and a joint pre-route certificate from the physical public
schedules. The actual budget guard supplies its capacity. -/
theorem calibrated_sharedRoutePrepared {α ξ : ℝ} {scale : ℕ} (calibrated : RouteRecords.FitsLinksAt α ξ scale)
    (H : ∀ u, WriterHistory ar.n (Tally.selectorWidth ar.n ar.K ar.h) (pub u) (mac u)
      (startReg u) (initial u) (log u) (endReg u) (final u))
    (done : ∀ u, ReturnedWriters ar D pp lp owner decl group ((PL) u) (H u))
    (teamCount : R+1 = ar.teams) (enough : 2 < ar.teams)
    (space : entries+ar.header.d.choose 2 ≤ ar.maxRows) (arenaFit : ar.stop < 2^w)
    (low : frame+112 ≤ ar.header.header) (base : ∀ u, (pub u 0).val = frame)
    (pointers : ∀ u, TablePointers tab (readings (initial u)))
    (sources : ∀ u, ProfileRouteInputs ((PF) u) ((BF) u) (pub u) (guess u) (initial u))
    (inputRoom : ∀ u, ((PF) u).header.length ≤ frame)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+((PL) u).count ≤ ar.header.header)
    (frameFit : ∀ u, ((BF) u).Fits w (pub u 0).val)
    {I : Type*} [Fintype I] (cell : I → Fin ar.cells) (id : I ↪ ℕ) (width : I → ℕ)
    (placement : Packing.Directory.BankPlacement D pp lp I cell id width) (bounds : D.DestinationBounds)
    (slabs : ∀ c, Packing.Directory.DataSlabs.size cell width c ≤ ar.cellStride)
    (processors : D.processors = r) (literal : D.literal = G.program.length+t)
    (orig : ℕ → ℕ) {A : Type*} [Fintype A]
    (label : Fin ar.cells → Label (ar.n+1) ar.header.d) (recv : A → Fin ar.cells) (size : A → ℕ)
    (image : GroupWeights.PhysicalImage weights orig ar.header.blocks ar.b ar.K ar.h decl label recv size)
    (setup : GroupWeights.CheckedFrame weights teamLayout orig w (TeamScales.exterior ξ r scale))
    (order : Fin entries ≃ A) (sizes : ∀ i : Fin entries, (D.directory pp lp)[i.val].width = size (order i))
    (cells : ∀ i : Fin entries, owner (D.directory pp lp)[i.val].cell = group (label (recv (order i)) decl.1))
    (sourceTeams : D.teams = R+1) (storage : D.entries*D.description ≤ D.teams*D.processors*(D.literal/2))
    (procs : 0 < D.processors) (fields : 0 < D.fields) (fieldBound : D.fields ≤ 2) (block : 0 < D.block)
    (literalRoom : D.literal ≤ TeamScales.literal α scale)
    (teamRoom : (ar.teams : ℝ) ≤ (scale:ℝ)^(2*α)) (headerRoom : (header : ℝ) ≤ r*(scale:ℝ)^(24/25:ℝ))
    (linkRoom : link = TeamScales.link ξ ar.teams scale)
    (accepted : ∀ {v mv fs}, Runs (pub 0) (mac 0) (LocalRow.groupPrefix ar.n (Tally.selectorWidth ar.n ar.K ar.h))
      (startReg 0) (initial 0) fs v mv →
      GroupWeights.ScheduleResult weights teamLayout orig (readings mv) ∧
      ∀ x : Fin ar.header.d, readings mv (ar.ownerBase+x.val) = (group x).val) :
    ∃ L : WireLayout (R+1) r link, L.header = header ∧ L.width = tableWidth tab row teamCount ∧
      SharedRoutePrepared G pin ext L D pp lp owner ar.cellBank ar.cellStride tab row pub final dst ib hb sb guess ∧
      ∀ u, (sharedLayout).Emitted (readings (H u).sharedInput) (readings (final u)) ∧
        (sharedLayout).Fits w (readings (H u).sharedInput) ∧
        SymbolFrame sharedLayout (readings (H u).sharedInput) ar.header.blocks ar.K ar.h decl group := by
  obtain ⟨v,mv,fs,_,_,_,_,_,run,_,_,_⟩ := (H 0).groupBudget
  obtain ⟨sched,owners⟩ := accepted run
  obtain ⟨rowFit,capacity⟩ := RouteRecords.groupPrefix_table_room calibrated ((BF) 0) (base 0) setup run sched image
    D pp lp order sizes owner group cells owners tab rfl teamCount enough sourceTeams storage procs fields fieldBound
    block processors literalRoom teamRoom headerRoom linkRoom
  have cap : ∀ x y, header+legLoad enough ((tab).widthMatrix row) x y+legLoad enough ((tab).widthMatrix row) y x ≤ r*link := by
    intro x y
    rw [Nat.mul_comm r link]
    exact capacity x y
  let L := scheduledWire tab row header teamCount enough cap
  obtain ⟨length,wid⟩ := scheduledWire_fields tab row header teamCount enough cap
  have rooms (u : Fin (R+1)) (x y : Fin ar.teams) :
      L.header+legLoad enough ((tab).widthMatrix row) x y+legLoad enough ((tab).widthMatrix row) y x ≤
        (G.transferFrame u L.header (dst u)).capacity := by
    rw [length]
    change _ ≤ link*r
    rw [Nat.mul_comm link r]
    exact cap x y
  have physical (u : Fin (R+1)) : ProfileRouteInputs ((PF) u) (G.transferFrame u L.header (dst u))
      (pub u) (guess u) (initial u) := length.symm ▸ sources u
  have fit (u : Fin (R+1)) : (G.transferFrame u L.header (dst u)).Fits w (pub u 0).val := length.symm ▸ frameFit u
  obtain ⟨prepared,actual⟩ := SharedRoutePrepared.of_complete_schedules (wire := L) H done teamCount enough wid space
    arenaFit rowFit rooms low base pointers physical inputRoom subRoom fit cell id width placement bounds slabs processors literal
  exact ⟨L,length,wid,prepared,fun u => (actual u).2⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
