import OAI.Computability.BorderVNP.DiagonalSignedGlobalSparseLaunch
import OAI.Computability.BorderVNP.DiagonalSignedProducedSafety
import OAI.Computability.BorderVNP.DiagonalProducedArgumentCells
import OAI.Computability.BorderVNP.DiagonalProducedRoster
import OAI.Computability.BorderVNP.FragmentTaskDirectoryFields
import OAI.Computability.BorderVNP.DiagonalNativeArgumentRoster

/-! # The signed argument source on the attained sparse emission and task return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM Evaluator Evaluator.ScheduleClock SignedTaskArena CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder

variable {w n : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f orig fit cells) {team frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
    {Site : Type} {pub : Arg → Word w} (mac : TeamOpcode.Macros w 8) (s : Bank w)

set_option quotPrecheck false
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) Site (a.controlRows team frame offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a f orig data i.val)
local notation "src" => Batch.produced R raw patch.placed patch.geometry patch.extra
local notation "field" => SparseEmission.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live)
  (ports:=ports) e row
local notation "os" => fun i => field (idx i)
local notation "sl" => batchLayout a frame ctl num
local notation "task" => fun i => ((os) i).typed sl (src i).typed
local notation "logical" => fun c => SparseExterior.logicalCell (patch.placed c) (patch.extra c) (field c).field

set_option maxHeartbeats 1400000 in
/-- The canonical sparse argument input and its submitted logical cells are
chosen on the actual post-report RAM. Every consumed row is the one assigned
to this team's compact ordinal. The same sampled report bits, immutable
geometry, private clock and physical packed words feed the native evaluator. -/
theorem SparseEmission.signed_call_input {u v k : ℕ}
    (place : a.SparsePlacement frame ctl) (geo : SparseGeometry a f offsets ctl)
    (limit : a.endAddress w u v k<2^w) (fp : (pub 0).val=frame)
    (word : readings orig (frame+30)=w) (controls : ∀ i : Fin 37, readings orig (ctl+i.val)=a.controls i.val)
    (taskFields : (R).toLayout.Fields raw)
    (ownerOrder : ∀ i, (row i).number.val=idx i.val)
    (rank : ∀ c c' : Fin (R).cells, c<c' → raw ((R).sorted+(R).padded+((R).stops+c.val)) <
      raw ((R).sorted+(R).padded+c'.val))
    (publicEnd : ∀ c < (R).cells, (patch.placed c).publicBase+((patch.placed c).parts.flatMap Part.publicBuffer).length ≤ (R).sorted)
    (geometry : ∀ c < (R).cells, patch.geometry c=(patch.placed c).publicBase+
      ((prefixParts (patch.placed c)).flatMap Part.publicBuffer).length)
    (description : ℕ)
    (originals : ∀ c < (R).cells, ∀ j, Sum.inr j ∈ (patch.placed c).boxes →
      (R).sorted+(R).padded≤(patch.placed c).slot j ∧ (patch.placed c).slot j+description≤a.fragments.external ∧
      (patch.placed c).headerWidth+(boxBody ((patch.placed c).factors j)).length≤description)
    (sup : ∀ c < (R).cells, ((patch.extra c).flatMap record).length ≤ (R).stride)
    (stored : ∀ i < num, MergeFields (src i) (R).tasks (R).four i patch.built)
    (sizes : ∀ i < num, ((task) i).cell.payload.length≤a.p.scratchStride ∧ (((task) i).cell.burst w).length≤a.p.burstStride)
    (paid : ∀ c < (R).cells, (R).owner raw c=(R).team →
      (CompactFrame.pack w (Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes)).length ≤ TeamScales.width n (1/2) ∧
      ((logical) c).directory.ProfileWidths ∧ SparseExterior.clock w ((logical) c).directory ((logical) c).privateWires (field c).field ≤ n^25) :
    ∃ arg : SparseCallInput pub patch.built, ∃ decoded : SparseArgumentCells n arg,
      decoded.rows.cells=logical ∧
      decoded.rows.payload=(fun c => Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes) ∧
      ProducedRoster a R raw patch.placed patch.geometry patch.extra arg ∧
      arg.count=num ∧ arg.owned=os ∧ arg.tasks=task ∧ (∀ i : Fin num, arg.owned i.val=(row i).owned (fit:=fit) (cells:=cells)) ∧
      ∀ r : Returns (.block [CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]) pub mac s patch.built,
        ∃ result : GeneratedCells SparseExterior.driver n pub r.val.2.2,
          result.cell=logical ∧ result.payload=decoded.rows.payload ∧
          let f := CellDispatch.Frame.ofMemory pub r.val.2.2
          f.base+3*f.count≤2^w := by
  let p := patch.placed
  let gs := patch.geometry
  let extra := patch.extra
  have bounds := e.globalCells_bounds row ownerOrder
  have receipt := e.globalCells_initial row ownerOrder patch place geo limit
  have span := patch.span
  have order := a.sparse_order place.cells
  have part : a.fragments.start ≤ a.fragments.external ∧ a.fragments.external ≤ a.fragments.limit := by
    dsimp only [FragmentArena.Layout.external,FragmentArena.Layout.cursors,FragmentArena.Layout.triples,
      FragmentArena.Layout.pairs,FragmentArena.Layout.quads,FragmentArena.Layout.limit,FragmentArena.Layout.counts]
    omega
  have addresses : (R).sorted+(R).padded ≤ a.before.merged ∧ ctl+37 ≤ a.before.merged ∧
      ctl+37 ≤ a.fragments.start ∧ frame+112 ≤ a.fragments.start := by
    have bankStart := order.1.trans order.2.1
    have bankMerged := bankStart.trans (part.1.trans (part.2.trans order.2.2.1))
    exact ⟨place.sortedBank.trans bankMerged,place.beforeBank.trans bankMerged,
      place.beforeBank.trans bankStart,place.beforeControl.trans ((Nat.le_add_right ..).trans (place.beforeBank.trans bankStart))⟩
  have high₀ : a.before.merged+a.cube.cells ≤ a.before.limit := order.2.2.2.1.trans
    ((Nat.le_add_right ..).trans order.2.2.2.2.1)
  have calls := patch.room.calls
  change a.before.limit+3*a.cube.cells<2^w at calls
  have four : a.before.four+4*a.cube.cells≤a.before.limit := by
    have cap := Nat.mul_le_mul_left 4 place.cells
    change 4*a.cube.cells ≤ 4*a.before.bound.cells at cap
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six]
    omega
  have width : raw (frame+30)=w := by
    rw [e.original _ (by rw [geo.control]; have := place.beforeControl; omega) (.inl (by omega))]
    exact word
  have loaded (j : ℕ) (hj : j ∈ [11,17,31,32,34,35,36]) : raw (ctl+j)=a.controls j := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rw [e.original _ (by rw [geo.control]; omega) (.inl (by omega))]
    exact controls ⟨j,by omega⟩
  have hiSupp : a.fragments.external ≤ (R).supplemental := part.2.trans (Nat.le_add_right ..)
  have sections := MergeSections.of_public_private R p gs extra description publicEnd geometry (fun c hc j hj => by
    obtain ⟨lo,hi,body⟩ := originals c hc j hj
    exact ⟨lo,hi.trans hiSupp,body⟩) sup
  have zones (i : ℕ) (hi : i < num) := a.produced_signed_sections team frame offsets ctl live ports raw p gs extra place patch.room span
    publicEnd geometry (fun c hc j hj => by
      obtain ⟨_,hi,body⟩ := originals c hc j hj
      dsimp only [p]
      omega) sup (fun j hj => (stored j hj).prefixEnd) hi
  obtain ⟨ranges,regions,arenas⟩ := a.produced_sparse_safety team frame offsets ctl live ports raw p gs extra
    patch.built field place patch.room patch.image span rank sections stored zones (fun c hc own => (bounds c hc own).1)
    (fun c hc own => (bounds c hc own).2.1) sizes
  have cap := produced_call_cap (w:=w) (n:=n) a R raw p gs extra field (fun c hc own => (paid c hc own).1)
  have mergedLimit : a.before.merged ≤ a.before.limit := (Nat.le_add_right _ _).trans high₀
  have frameMerged := addresses.2.2.2.trans (part.1.trans (part.2.trans order.2.2.1))
  have controlCalls := addresses.2.1.trans mergedLimit
  have controlTasks : ctl+37 ≤ (R).tasks := controlCalls.trans (Nat.le_add_right ..)
  let input := SparseCallInput.ofOwned (n:=n) pub mac s patch.built a R raw p gs extra field fp taskFields patch.room
    patch.image width (show ctl+36<2^w by omega) (four.trans (by omega)) rfl rfl rfl rfl place.cells loaded span
    ⟨place.primary,frameMerged⟩ ⟨addresses.1.trans mergedLimit,high₀⟩ place.beforeControl ⟨controlCalls,controlTasks⟩ place.controller
    (.inl addresses.2.1) (addresses.2.2.2.trans part.1) stored ranges (fun c hc own => (bounds c hc own).1)
    (fun c hc own => (bounds c hc own).2.1) (fun c hc own => (bounds c hc own).2.2.1)
    (fun c hc own => (bounds c hc own).2.2.2.1) (fun c hc own => (bounds c hc own).2.2.2.2)
    receipt regions arenas cap
  let actual : SparseArgumentCells n input :=
    SparseCallInput.ofOwnedCells pub mac s patch.built a R raw p gs extra field (fun c hc own => (paid c hc own).2)
  have roster : ProducedRoster a R raw p gs extra input := SparseCallInput.ofOwned_roster a R raw p gs extra field
  refine ⟨input,actual,rfl,rfl,roster,rfl,rfl,rfl,fun i => e.globalCells_at row i,?_⟩
  intro r
  rw [input.return_memory r]
  have packed := actual.rows.packed
  have frameKept := input.typed.control.survives.1
  refine ⟨⟨actual.rows.cells,actual.rows.payload,?_⟩,rfl,rfl,?_⟩
  · rw [frameKept]
    exact packed
  · rw [frameKept]
    exact actual.extent

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
