import OAI.Computability.BorderVNP.FragmentRows
import OAI.Computability.BorderVNP.RoutingISASignedReaderArena
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostDest
import OAI.Computability.BorderVNP.RoutingISACubeArenaPreserveGroups

/-! # The sparse fragment emitter in the signed cell and cube allocation

Every geometry operand and physical receiving-cell pointer precedes the
quad arena. The populated raw-row count controls the number of stores.
Both types of emitted intervals refer to addresses inside the true cell
bank, and control word 29 precedes the first output store.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open BorderVNP.Cube Packing RoutingOutputs Diagonal.ExternalSew.Fragments
open VPVNP.BurstRAM

/-- The public routing arrays, host directory and bank allocation all precede
the fragment output. The entire emitted capacity fits before the bucket
headers, including the reserved terminal row. -/
theorem arena_order (a : SignedTaskArena.Layout) :
    a.cube.header.header ≤ a.fragments.quads ∧ a.cube.hostDirectory+2*a.cube.cells ≤ a.fragments.quads ∧
    a.cube.stop ≤ a.fragments.quads ∧
    a.fragments.quads+4*(2*a.cube.cables+a.cube.maxRows) ≤ a.fragments.limit := by
  let c := a.cube
  have stop : c.stop ≤ a.fragments.quads := by
    change c.stop ≤ CubeConstants.arenaEnd c.stop a.id
    dsimp only [CubeConstants.arenaEnd,CubeConstants.idBase]; omega
  have pair : c.records ≤ c.pairBase := by dsimp only [CubeArena.Layout.pairBase,TableLayout.reserveEnd]; omega
  have low := c.group_order.1
  have mid := c.separated.2.2.2.1
  have bank := c.separated.2.2.2.2.2
  have pairBank : c.pairBase ≤ c.cellBank := by dsimp only [CubeArena.Layout.cellBank]; omega
  refine ⟨low.trans (mid.trans (pairBank.trans (bank.trans stop))),pair.trans (pairBank.trans (bank.trans stop)),stop,?_⟩
  rw [a.fragments.footprint]
  change a.fragments.start+4*(2*c.cables+c.maxRows) ≤ a.fragments.start+
    7*(2*c.cables+c.maxRows+1)+4*c.cells+c.cells*a.p.scratchStride+1
  omega

/-- The actual contiguous geometry output puts all 37 controls before the
secondary cube header, from the native count of routing and suffix words. -/
theorem controls_before_header {fresh u k o b w m C J A tail : ℕ}
    (outputs : m*3+(RoutingOutputs.count m C J A+((C+(J+C))+(37+tail))) ≤ o) :
    let dest := GeometryAdvice.Allocation.dest fresh u k o b
    RoutingOutputs.controlsBase dest m C J A+37 ≤ GeometryAdvice.Allocation.stop fresh u k o b w := by
  intro dest
  dsimp only [controlsBase,bases,RoutingOutputs.count] at *
  unfold GeometryAdvice.Allocation.stop GeometryAdvice.Allocation.packed GeometryAdvice.Allocation.dense
  change dest+m*3+m*2+C+C+J*2+2*A+C+J+C+37 ≤ dest+o+_+_
  omega

/-- Any source within a populated cell's fixed-stride bank is below the
cube's end and therefore below the fragment output reservation. -/
theorem cell_address {a : CubeArena.Layout} {c slot : ℕ} (hc : c<a.cells) (hs : slot<a.cellStride) :
    a.cellBank+c*a.cellStride+slot < a.stop := by
  have h := Nat.mul_le_mul_right a.cellStride (Nat.succ_le_of_lt hc)
  rw [Nat.succ_mul] at h
  unfold CubeArena.Layout.stop; omega

/-- Physical bound of the real per-cell pointer, obtained from the native
cell writer for every label, independently of its owner's team. -/
theorem actual_cell_source (a : CubeArena.Layout) (mem : ℕ → ℕ)
    (bank : ∀ c<a.cells, mem (a.hostDirectory+2*c+1) = a.cellBank+c*a.cellStride)
    {c slot : ℕ} (hc : c<a.cells) (hs : slot<a.cellStride) :
    mem (a.hostDirectory+2*c+1)+slot < a.stop := by
  rw [bank c hc]; exact cell_address hc hs

variable {w head origin J A : ℕ} (a : SignedTaskArena.Layout) (mem : ℕ → ℕ)
local notation "c" => a.cube
local notation "H" => HostScatter.Layout.fromFrame head mem
local notation "f" => Layout.fromFrame head mem

/-- True decoded scalar layout and real row geometry suffice for the native
fragment emission. All source-array separations are consequences of the
geometry-before-cube and cube-before-fragment reservations. -/
theorem fits_in_arena
    (header : RoutingOutputs.Header head origin (c).cables (c).cells J mem)
    (control : mem (head+92) = controlsBase origin (c).cables (c).cells J A)
    (quad : mem (mem (head+92)+28) = a.controls 28) (hosts : mem (head+72) = (c).hostDirectory)
    (base : head+112 ≤ origin) (deliveries : mem (head+8)+7*mem (head+9) ≤ origin)
    (lower : controlsBase origin (c).cables (c).cells J A+37 ≤ (c).header.header)
    (limit : a.fragments.limit < 2^w) (rows : mem (head+9) ≤ (c).maxRows)
    (ends : ∀ i < (H).count, ∀ side, (H).width mem i ≠ 0 →
      (H).cell mem i side < (c).cells ∧ mem ((H).relative+2*i+side.toNat)+(H).width mem i ≤ (c).cellStride)
    (data : LabelIndex.Endpoints (LabelIndex.layout head mem) mem)
    (sizes : ∀ i<(c).cells, mem ((f).supplied+i) ≤ (c).cellStride)
    (bank : ∀ i<(c).cells, mem ((c).hostDirectory+2*i+1) = (c).cellBank+i*(c).cellStride) :
    (f).Fits w mem := by
  have headID : (f).host.frame = head := rfl
  have cable : (f).host.cables = origin := header.cables
  have cnt : (f).host.count = (c).cables := header.edges
  have cells : (f).cells = (c).cells := header.cells
  have ptr : (f).host.cells = (c).hostDirectory := hosts
  have dr : (f).deliveries+7*(f).count ≤ origin := deliveries
  have nrows : (f).count ≤ (c).maxRows := rows
  have ct : (f).control = controlsBase origin (c).cables (c).cells J A := control
  have qq : (f).quads = a.fragments.quads := quad.trans rfl
  have sup : (f).supplied = origin+(c).cables*3+2*(c).cables := by
    change (H).relative+2*(H).count = _
    rw [show (H).relative = (bases origin (c).cables (c).cells J).ends from header.ends,
      show (H).count = (c).cables from header.edges]
    rfl
  have before : (f).control+37 ≤ a.fragments.quads := ct ▸ lower.trans (arena_order a).1
  have geom : origin+(c).cables*3+2*(c).cables+(c).cells ≤ (f).control := by
    rw [ct]; dsimp only [controlsBase,bases]; omega
  have endQ := (arena_order a).2.2.2
  have quadFit : (f).quads+4*(2*(f).host.count+(f).count) ≤ 2^w := by rw [qq,cnt]; omega
  have high := (arena_order a).2.2.1
  have hostRoom := (arena_order a).2.1
  have dataCells (i : ℕ) (hi : i<(f).count) : ((f).row mem i).cell < (c).cells := by
    rw [← cells]
    simpa only [Layout.row,Layout.fromFrame,LabelIndex.layout,LabelIndex.deliveryAt,Nat.mul_comm 7 i] using data.deliveries i hi
  constructor
  · rw [headID]; omega
  · omega
  · rw [cable,cnt]; omega
  · omega
  · rw [sup,cells]; omega
  · rw [ptr,cells]; omega
  · exact quadFit
  · intro i hi side nonzero _
    rw [cells]; exact (ends i hi side nonzero).1
  · intro i hi; rw [cells]; exact dataCells i hi
  · intro i hi side nonzero _
    change (H).width mem i ≠ 0 at nonzero
    obtain ⟨ci,off⟩ := ends i hi side nonzero
    have offSmall : mem ((H).relative+2*i+side.toNat) < (c).cellStride := by omega
    change mem ((H).cells+2*((H).cell mem i side)+1)+mem ((H).relative+2*i+side.toNat) < 2^w
    rw [show (H).cells = (c).hostDirectory from hosts]
    exact (actual_cell_source (c) mem bank ci offSmall).trans_le (by omega)
  · intro i hi q hq
    let row := (f).row mem i
    have ci : row.cell < (c).cells := dataCells i hi
    change live (fun j => mem ((f).supplied+j)) (fun j => mem ((f).host.cells+2*j+1)) row = some q at hq
    unfold live at hq
    split at hq
    next h =>
      cases Option.some.inj hq
      change mem ((f).host.cells+2*row.cell+1)+row.slot < 2^w
      rw [ptr]
      have bankFit := actual_cell_source (c) mem bank ci (h.1.trans_le (sizes row.cell ci))
      exact bankFit.trans_le (by omega)
    next => contradiction
  · intro z input
    left
    rcases input with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · rw [cable,cnt] at h; omega
    · omega
    · rw [sup,cells] at h; omega
    · rw [ptr,cells] at h; omega
  · left; omega

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
