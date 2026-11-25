import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenBoot
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenSort
import OAI.Computability.BorderVNP.CubeRoutePreparedEntry

/-! # Original bundle slots at the actual pre-writer native directory return

The grouped allocator's scheduled input and physical cell directory recover
the same six bundle words as the real RAM returned after both native directory
programs. Private placement pairs live below the secondary header and survive
the positive-width demand publication.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM Packing BottomReports RoutingOutputs DiagonalTallyAllocation

variable {ar : CubeArena.Layout} {W frame origin next gap R : ℕ} {D : Directory.Layout}
variable (axis : Fin (ar.n+1)) (pp lp : ℕ → ℕ × ℕ)
variable {profile placed : Memory W} {entry input : ℕ → ℕ}

local notation "ctrl" => controlsBase origin ar.cables ar.cells D.entries (D.teams*D.sites)
local notation "l" => privateLayout frame origin ar.cables ar.cells D.entries D.description gap
local notation "banks" => ar.cellWriter frame ctrl axis
local notation "pubMem" => readings (Directory.ISA.publish placed frame next (D.directory pp lp))

/-- The actual checked schedule supplies the two private words consulted by
each source header and the installed bank pointer of its true owner. The
result identifies every six-word header with the final physical memory. -/
theorem NativeEntry.open_placement {bits : ℕ} (native : NativeEntry ar frame ctrl axis R input pubMem entry)
    (place : (l).Image (readings profile) D.entries (readings placed))
    (fit : (l).Fits bits (readings profile)) (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (controlEnd : ctrl+37 ≤ ar.header.header) :
    (l).raw+2*D.entries ≤ (banks).dest ∧
    ∃ scheduled, (∀ i : Fin D.entries, scheduled ((l).raw+2*i.val)=readings placed ((l).raw+2*i.val) ∧
      scheduled ((l).raw+2*i.val+1)=readings placed ((l).raw+2*i.val+1)) ∧
      ∀ i : Fin D.entries, ∀ copies base fine incoming cap,
        rawHeader ((banks).written scheduled ar.cells) (l).raw ar.hostDirectory i.val copies base fine incoming cap =
          rawHeader entry (l).raw ar.hostDirectory i.val copies base fine incoming cap := by
  obtain ⟨scheduled,_,img⟩ := native.image
  have head := ar.writer_order
  have group := ar.group_order
  have before : (l).raw+2*D.entries ≤ ctrl := by dsimp only [privateLayout,controlsBase,bases]; omega
  have start : origin ≤ (l).raw := by dsimp only [privateLayout,bases]; omega
  have hdr : ar.header.header ≤ (banks).dest := by
    change ar.header.header ≤ ar.hostDirectory
    omega
  have cap := Nat.mul_le_mul_left 7 (D.directory_length_le pp lp)
  have atPlaced (a : ℕ) (lo : origin ≤ a) (hi : a<ar.header.header) : entry a=readings placed a :=
    (native.low a hi).trans (congrArg Fin.val (CableTriples.published_outside placed frame next (D.directory pp lp) a
      (by omega) (.inr (by omega))))
  have clear (i : Fin D.entries) (j : ℕ) (hj : j<2) :
      scheduled ((l).raw+2*i.val+j) = readings placed ((l).raw+2*i.val+j) := by
    have h := i.isLt
    have bounds : (l).raw+2*i.val+j < ar.header.header := by omega
    exact (img.beforeHeader _ bounds).symm.trans (atPlaced _ (by omega) bounds)
  refine ⟨before.trans ((by omega : ctrl ≤ ar.header.header).trans hdr),scheduled,
    fun i => ⟨clear i 0 (by decide),clear i 1 (by decide)⟩,?_⟩
  intro i copies base fine incoming capWords
  let c := (l).owner (readings profile) i.val
  have owner := place.owner_eq fit i.isLt
  have count : c<ar.cells := fit.owners i.val i.isLt
  let actual := (banks).written scheduled ar.cells
  have same (j : ℕ) (hj : j<2) : actual ((l).raw+2*i.val+j)=entry ((l).raw+2*i.val+j) := by
    have h := i.isLt
    have e : (l).raw+2*i.val+j<ar.header.header := by omega
    exact ((banks).written_outside scheduled ar.cells _ (.inl (e.trans_le hdr))).trans (img.beforeHeader _ e).symm
  have raw : entry ((l).raw+2*i.val) = c :=
    (atPlaced _ (by omega) (by have := i.isLt; omega)).trans owner
  have ptr : actual (ar.hostDirectory+2*c+1)=entry (ar.hostDirectory+2*c+1) := by
    have cell := ((banks).written_at scheduled count).2
    apply cell.trans
    rw [Nat.mul_comm 2 c]
    exact (img.hostRows c count).2.symm
  change rawHeader actual _ _ _ _ _ _ _ _ = _
  have first : actual ((l).raw+2*i.val)=entry ((l).raw+2*i.val) := same 0 (by decide)
  simp only [rawHeader,first,same 1 (by decide),raw,ptr]

/-- Signed geometry words encode the absolute receiving base and bundle site.
The fit of control 11 alone bounds the complete cube reservation, including
the bank end, in the geometry output width. -/
theorem signed_cellWriter_fit (t : SignedTaskArena.Layout) (axis : Fin (t.cube.n+1)) {bits frame control : ℕ}
    (positive : 0 < t.cube.header.d) (low : frame+112 ≤ t.cube.header.header)
    (ctl : control+37 ≤ t.cube.header.header) (fit : t.controls 11 < 2^bits) :
    (t.cube.cellWriter frame control axis).Fits bits := by
  have deck : t.cube.stop ≤ CubeConstants.arenaEnd t.cube.stop t.id := by
    unfold CubeConstants.arenaEnd CubeConstants.idBase; omega
  have after := t.constants_le_before
  have four : t.before.start ≤ t.before.four := by
    dsimp only [BeforeTasks.four,BeforeTasks.merged,BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths]
    omega
  change t.before.four < 2^bits at fit
  exact t.cube.cellWriter_fits frame control axis positive low (by omega) (deck.trans (after.trans four) |>.trans_lt fit)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
