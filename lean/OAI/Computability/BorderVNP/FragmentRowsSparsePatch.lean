import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenLayouts
import OAI.Computability.BorderVNP.DiagonalNativeSupplementWords
import OAI.Computability.BorderVNP.CellSparseExteriorNativeBatchArena

/-! # The sparse reader after the native task and supplemental writers

The task producer replaces the owned count and emits the true seven-word
rows. The supplemental loop changes only the four descriptor triples and
the merged counter belonging to each of those rows. The sparse reader can
therefore read its controller, its dense pointers, and its physical inputs
from the chronological output of both programs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM CellPacket.Supplement.Batch TypedTaskBuilder DiagonalTallyAllocation

/-- The true typed producer image and the geometry of its supplemental patch. -/
structure SparsePatch {w : ℕ} (Site : Type) (rows : CellControlRows.Layout) (src : ℕ → ℕ) where
  /-- Word memory returned by the typed-task producer. -/
  built : Memory w
  /-- Descriptor geometry of each globally numbered cell. -/
  placed : ℕ → CellPacket.Placed Site
  /-- Address of the original public geometry records. -/
  geometry : ℕ → ℕ
  /-- Supplemental records of each cell. -/
  extra : ℕ → List CellSparse.Record
  room : rows.toLayout.Room src w
  image : readings built = rows.toLayout.published src
  span : ∀ c < rows.cells, src (rows.sorted+rows.padded+(rows.stops+c))-src (rows.sorted+rows.padded+c)-1 =
    3*((placed c).parts.length+3)

variable {w : ℕ} {Site : Type} {rows : CellControlRows.Layout} {src : ℕ → ℕ}

/-- Actual contents after all merged-count and descriptor stores. -/
noncomputable def SparsePatch.memory (x : SparsePatch (w:=w) Site rows src) : Memory w :=
  written x.built (fun i => (produced rows src x.placed x.geometry x.extra i).cell) (rows.before src rows.cells)

/-- Outside the actual sorted descriptor bank and the merged-count column,
any word retains the value emitted by the native seven-word writer. -/
theorem SparsePatch.preserved (x : SparsePatch (w:=w) Site rows src) (addr : ℕ)
    (sorted : addr < rows.sorted ∨ rows.sorted+rows.padded ≤ addr)
    (merged : addr < rows.merged ∨ rows.merged+rows.cells ≤ addr) :
    readings x.memory addr=readings x.built addr := by
  apply congrArg Fin.val (preserve x.built _ (i:=0) (Nat.zero_le _) addr ?_)
  intro j _ hj
  have bound := (global_spec rows.toLayout src hj).1
  obtain ⟨mrg,_,stop,start⟩ := produced_addresses rows src x.placed x.geometry x.extra x.room hj x.span
  let o := produced rows src x.placed x.geometry x.extra j
  change addr ≠ o.layout.merged ∧ (addr < o.layout.tail ∨ o.layout.tail+12 ≤ addr)
  change o.layout.merged=rows.merged+globalCell rows.toLayout src j at mrg
  rw [mrg]
  change globalCell rows.toLayout src j < rows.cells at bound
  exact ⟨by omega,by rcases sorted with h|h; exact .inl (h.trans_le start); exact .inr (stop.le.trans h)⟩

/-- The previous value survives both writers outside their explicit store intervals. -/
theorem SparsePatch.original (x : SparsePatch (w:=w) Site rows src) (addr : ℕ)
    (sorted : addr < rows.sorted ∨ rows.sorted+rows.padded ≤ addr)
    (merged : addr < rows.merged ∨ rows.merged+rows.cells ≤ addr)
    (clear : ¬ rows.outputAt addr) : readings x.memory addr=src addr := by
  rw [x.preserved addr sorted merged,x.image,task_published_outside _ _ addr clear]

/-- The addressed dense-bank start and full raw extent come from the two
words of the true owned seven-word row. -/
theorem SparsePatch.dense_task (x : SparsePatch (w:=w) Site rows src)
    (sorted : rows.sorted+rows.padded ≤ rows.tasks) (merged : rows.merged+rows.cells ≤ rows.tasks)
    {i : ℕ} (owned : i < rows.before src rows.cells) :
    let c := globalCell rows.toLayout src i
    readings x.memory (rows.tasks+7*i+2)=src (rows.banks+2*c+1) ∧
      readings x.memory (rows.tasks+7*i+3)=src (rows.offsets+2*rows.cables+c)+src (rows.tails+c) := by
  intro c
  obtain ⟨hc,ho,rank⟩ := global_spec rows.toLayout src owned
  have field (k : Fin 7) : readings x.memory (rows.tasks+7*i+k.val) =
      (rows.row src c)[k.val]'(by exact k.isLt) := by
    have above := x.room.outputs.2
    change rows.frame+112≤rows.tasks at above
    rw [x.preserved _ (.inr (by omega)) (.inr (by omega)),x.image,TypedTaskBuilder.Layout.published,
      Function.update_of_ne (by omega : rows.tasks+7*i+k.val ≠ rows.frame+90),←rank]
    exact rows.toLayout.image_word src x.room hc le_rfl ho k
  exact ⟨field 2,field 3⟩

variable (a : Layout) {team frame offsets ctl live ports : ℕ}
local notation "R" => a.controlRows team frame offsets ctl live ports

/-- Absolute address order of the geometry and the count reservations. -/
structure Layout.SparsePlacement (a : Layout) (frame ctl : ℕ) : Prop where
  beforeControl : frame+112 ≤ ctl
  primary : frame+112 ≤ a.p.sorted
  controller : ctl+37 ≤ a.p.sorted ∨ a.p.sorted+a.p.padded ≤ ctl
  beforeBank : ctl+37 ≤ a.cube.cellBank
  sortedBank : a.p.sorted+a.p.padded ≤ a.cube.cellBank
  cells : a.cube.cells ≤ a.p.report.cells

/-- Order of the occupied native bank, fragment arrays, merged counters,
six-word headers and typed tables in the single signed reservation. -/
theorem Layout.sparse_order (cells : a.cube.cells ≤ a.p.report.cells) :
    a.cube.cellBank ≤ a.cube.stop ∧ a.cube.stop ≤ a.fragments.start ∧ a.fragments.limit ≤ a.before.merged ∧
    a.before.merged+a.cube.cells ≤ a.before.six ∧ a.before.six+6*a.cube.cells ≤ a.before.limit ∧
    a.before.limit ≤ (a.tasks 0 0 0 0).tasks := by
  have below : a.cube.stop ≤ a.fragments.start := by
    change a.cube.stop ≤ CubeConstants.arenaEnd a.cube.stop a.id
    unfold CubeConstants.arenaEnd CubeConstants.idBase; omega
  have bounds : a.before.bound.cells=a.p.report.cells := rfl
  refine ⟨Nat.le_add_right ..,below,?_,?_,?_,Nat.le_add_right ..⟩
  · change a.before.start ≤ a.before.merged
    unfold BeforeTasks.merged BeforeTasks.counters BeforeTasks.supplement BeforeTasks.tailWidths; omega
  · unfold BeforeTasks.six BeforeTasks.four; omega
  · unfold BeforeTasks.limit BeforeTasks.bundleTable BeforeTasks.ranges; omega

/-- The three frame words and six indirect controls are physically present
after the two writers, including the newly published count in slot 90. -/
theorem SparsePatch.loaded_in_arena (x : SparsePatch (w:=w) Site (R) src)
    (place : a.SparsePlacement frame ctl) (fields : (R).toLayout.Fields src)
    (controls : ∀ k : Fin 37, k.val ≠ 29 → src (ctl+k.val)=a.controls k.val) :
    (SparseExterior.batchLayout a frame ctl ((R).before src (R).cells)).Loaded (readings x.memory) := by
  have order := a.sparse_order place.cells
  have extent : a.fragments.start ≤ a.fragments.limit := by rw [a.fragments.footprint]; omega
  have below : a.cube.cellBank ≤ (R).merged := order.1.trans (order.2.1.trans (extent.trans order.2.2.1))
  have primary (k : ℕ) (hk : k<112) : readings x.memory (frame+k)=readings x.built (frame+k) :=
    x.preserved _ (.inl (lt_of_lt_of_le (by omega : frame+k<frame+112) place.primary))
      (.inl (by have := place.beforeControl; have := place.beforeBank; omega))
  have scalars (k : ℕ) (hk : k<37) (ne : k≠29) : readings x.memory (ctl+k)=a.controls k := by
    have address : ctl+k < a.cube.cellBank := lt_of_lt_of_le (show ctl+k < ctl+37 by omega) place.beforeBank
    have sorted : ctl+k < (R).sorted ∨ (R).sorted+(R).padded ≤ ctl+k := by
      change ctl+k<a.p.sorted ∨ a.p.sorted+a.p.padded≤ctl+k
      rcases place.controller with h|h <;> omega
    apply (x.original _ sorted (.inl (address.trans_le below)) ?_).trans (controls ⟨k,hk⟩ ne)
    have call : (R).merged ≤ (R).calls := (a.task_bounds team frame offsets ctl).1
    have tasks : (R).merged ≤ (R).tasks := (a.task_bounds team frame offsets ctl).2.1
    have head := place.beforeControl
    change ¬(((R).tasks ≤ ctl+k ∧ _) ∨ (∃ c < (R).cells,ctl+k=(R).calls+3*c) ∨ ctl+k=frame+90)
    rintro (⟨_,_⟩|⟨c,_,_⟩|_) <;> omega
  have base (k : ℕ) (small : k<112) (other : k≠90) : readings x.memory (frame+k)=src (frame+k) := by
    rw [primary k small,x.image]; exact (R).toLayout.published_field src x.room other small
  refine ⟨?_,(base 89 (by decide) (by decide)).trans fields.outer.2.2.2.2.2.2.1,
    (base 92 (by decide) (by decide)).trans fields.outer.2.2.2.2.2.2.2,scalars 17 (by decide) (by decide),
    scalars 31 (by decide) (by decide),scalars 32 (by decide) (by decide),scalars 34 (by decide) (by decide),
    scalars 35 (by decide) (by decide),scalars 36 (by decide) (by decide)⟩
  change readings x.memory (frame+90)=(R).before src (R).cells
  rw [primary 90 (by decide),x.image]
  exact Function.update_self ..

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
