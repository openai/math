import OAI.Computability.BorderVNP.FragmentTaskDirectoryFields

/-! # Typed task-builder windows at the actual returned stable bucket memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM SignedTaskArena TypedTaskBuilder DiagonalTallyAllocation
open private before_order from OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenRoom

variable {w u v k team frame offsets ctl : ℕ} {a : SignedTaskArena.Layout} {f : Layout} {m : Memory w}
    {fit : f.Fits w (readings m)} {cells : a.fragments.cells=f.cells} (e : SparseEmission a f m fit cells)
local notation "old" => readings m
local notation "nowMem" => readings e.output
local notation "task" => a.tasks team frame offsets ctl

/-- Physical marker and supply bounds before native fragment emission. The
signed allocation locates the descriptor inverse rows below the receiving bank
and the report-tail counts above the fragment arena. -/
structure TaskSourceGeometry (a : SignedTaskArena.Layout) (frame offsets ctl : ℕ) (mem : ℕ → ℕ)
    (team : Option ℕ := none) : Prop where
  banks : frame+112 ≤ a.cube.hostDirectory
  offsetsLow : frame+112 ≤ offsets
  offsetsEnd : offsets+2*a.cube.cables+a.cube.cells ≤ ctl
  inverseEnd : a.p.sorted+2*a.p.padded ≤ a.cube.cellBank
  inverseControl : ctl+37 ≤ a.p.sorted ∨ a.p.sorted+2*a.p.padded ≤ ctl
  markers : a.cube.cells ≤ a.p.stops ∧ a.p.stops+a.cube.cells ≤ a.p.padded
  ranks : ∀ c < a.cube.cells, mem (a.p.sorted+a.p.padded+c)<a.p.padded ∧
    mem (a.p.sorted+a.p.padded+(a.p.stops+c))<a.p.padded
  /-- The sparse emitter overwrites one low word at `ctl+29`. A
  team-specific bound is valid whenever its physical owner table survives
  that write. A uniform bound works for any placement of the controller. -/
  extents :
    let fits := fun c => mem (offsets+2*a.cube.cables+c)+mem (a.before.tailWidths+c) ≤ a.cube.cellStride
    let allFit := ∀ c<a.cube.cells, fits c
    match team with
    | none => allFit
    | some u => allFit ∨
        ((∀ c<a.cube.cells, a.cube.hostDirectory+2*c ≠ ctl+29) ∧
          ∀ c<a.cube.cells, mem (a.cube.hostDirectory+2*c)=u → fits c)

/-- A source with a bound on every cell also bounds each team's owned cells. -/
theorem TaskSourceGeometry.atTeam {mem : ℕ → ℕ} (g : TaskSourceGeometry a frame offsets ctl mem) (t : ℕ) :
    TaskSourceGeometry a frame offsets ctl mem (some t) :=
  ⟨g.banks,g.offsetsLow,g.offsetsEnd,g.inverseEnd,g.inverseControl,g.markers,g.ranks,Or.inl g.extents⟩

/-- A true marker/supply geometry and the signed arena's single address ceiling
give every field of the native task-builder room certificate on the actual
returned bucket memory. -/
theorem SparseEmission.task_room_owned (control : f.control=ctl) (place : a.SparsePlacement frame ctl)
    (g : TaskSourceGeometry a frame offsets ctl old (some team)) (high : a.endAddress w u v k < 2^w) :
    (task).Room nowMem w := by
  have before := place.beforeControl
  have banks := place.beforeBank
  have host := a.open_table_order.2.1
  have cellsCap : a.cube.cells ≤ a.before.bound.cells := place.cells
  have first := place.primary
  have offLo := g.offsetsLow
  have offEnd := g.offsetsEnd
  have invEnd := g.inverseEnd
  obtain ⟨lowStop,stopFrag,_,_,_,_⟩ := a.sparse_order place.cells
  have frags : a.fragments.start ≤ a.fragments.limit := by rw [a.fragments.footprint]; omega
  have tailBase : a.before.tailWidths=a.fragments.limit := rfl
  have tailStop : a.before.tailWidths+a.cube.cells ≤ a.before.limit := by
    obtain ⟨_,_,_,_,_,_,_,_⟩ := before_order a.before
    change a.before.start+a.cube.cells ≤ a.before.limit
    have first : a.before.start+a.before.bound.cells=a.before.supplement := rfl
    omega
  have low (a₀ : ℕ) (ne : a₀≠ctl+29) (hi : a₀<a.cube.cellBank) : (nowMem) a₀ = old a₀ :=
    e.original _ (control ▸ ne) (.inl (hi.trans_le (lowStop.trans stopFrag)))
  have rank (c : ℕ) (hc : c<a.cube.cells) : (nowMem) (a.p.sorted+a.p.padded+c)<a.p.padded ∧
      (nowMem) (a.p.sorted+a.p.padded+(a.p.stops+c))<a.p.padded := by
    have mk := g.markers
    have separate := g.inverseControl
    rw [low _ (by omega) (by omega),low _ (by omega) (by omega)]
    exact g.ranks c hc
  have ext (c : ℕ) (hc : c<a.cube.cells) (belongs : (task).owner nowMem c=team) :
      (nowMem) (offsets+2*a.cube.cables+c)+(nowMem) (a.before.tailWidths+c) ≤ a.before.limit := by
    rw [low _ (by omega) (by omega),e.original _ (by rw [control]; omega) (.inr (by omega))]
    have size : old (offsets+2*a.cube.cables+c)+old (a.before.tailWidths+c) ≤ a.cube.cellStride := by
      obtain allFit | ⟨separate,ownedFit⟩ := g.extents
      · exact allFit c hc
      · apply ownedFit c hc
        change (nowMem) (a.cube.hostDirectory+2*c)=team at belongs
        rw [low _ (separate c hc) (by omega)] at belongs
        exact belongs
    have single := Nat.mul_le_mul_right a.cube.cellStride (show 1 ≤ a.cube.cells by omega)
    rw [Nat.one_mul] at single
    change a.cube.cellBank+a.cube.cells*a.cube.cellStride ≤ a.fragments.start at stopFrag
    omega
  have inputs : (task).InputBounds nowMem a.before.limit := by
    refine ⟨?_,?_,?_,g.markers,rank,ext⟩
    · change frame+112 ≤ _ ∧ ctl+28 ≤ _; omega
    · change a.cube.hostDirectory+2*a.cube.cells ≤ _ ∧ offsets+2*a.cube.cables+a.cube.cells ≤ _ ∧
        a.before.tailWidths+a.cube.cells ≤ _ ∧ a.p.sorted+2*a.p.padded ≤ _
      omega
    · change frame+112 ≤ a.cube.hostDirectory ∧ frame+112 ≤ offsets ∧ frame+112 ≤ a.before.tailWidths ∧ frame+112 ≤ a.p.sorted
      have := g.banks; omega
  have endFit : a.after.start < 2^w := by
    have last : a.after.start ≤ a.after.localBase := by rw [AfterTasks.localBase,a.after.footprint]; omega
    dsimp only [SignedTaskArena.Layout.endAddress,SignedTaskArena.Layout.entry,DiagonalResidueRAM.gateBase,
      SignedTaskArena.Layout.valuation,SignedTaskArena.Layout.tallyBits] at high
    omega
  exact windows_room task nowMem a.before.limit a.p.scratchStride a.p.burstStride w inputs endFit

/-- The original fully bounded source can likewise be used at any team. -/
theorem SparseEmission.task_room (control : f.control=ctl) (place : a.SparsePlacement frame ctl)
    (g : TaskSourceGeometry a frame offsets ctl old) (high : a.endAddress w u v k < 2^w) :
    (task).Room nowMem w :=
  e.task_room_owned control place (g.atTeam team) high

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
