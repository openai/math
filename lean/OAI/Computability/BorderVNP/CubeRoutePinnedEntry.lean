import OAI.Computability.BorderVNP.CubeRoutePreparedEntry
import OAI.Computability.BorderVNP.CubeISALocalRowGroupPrefix

/-! # Complete execution through the physical demand-compiler entry from the pinned cube header -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open LocalRow CubeArena CubeHeaderInstall TeamContraction.JointHeader

/-- Charge for the two native directories between group assignment and the compiler for data demands. -/
def directoryTicks (a : CubeArena.Layout) (frame : ℕ) :=
  (CellBanks.setup.slots+a.cells*15+1)+(30+(a.pairWriter frame).count*(24+27*(a.n+1)))

/-- The actual header controls all nine public stages. Their success criterion includes
the binary declaration range, the first minimizing coordinate and the genuine team capacities.
Every successful return contains the physical owner words and retains the raw source directory. -/
theorem beforeWriters_pinned {w : ℕ} (pub : Arg → Word w) (f : BroadcastFrame)
    (a : CubeArena.Layout) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (decl : Broadcast a.n a.header.d a.header.cap)
    (R X : ℕ) :
    let frame := (pub 0).val
    let raw := padded (TeamContraction.JointHeader.spelling (G++DeclarationBits.spelling decl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w a.header.d a.n a.header.blocks a.b a.h a.s
    let ext := jointFields (a.extension old) fresh G.length gates outputs width off ell a.header.d a.n a.header.blocks a.b a.h a.s
    let index := readCode (a.n+1) decl.1
    let axis := Fin.ofNat (a.n+1) index
    let wl := weightLayout a frame index
    let tl := teamLayout a R
    let labelTicks := labelPrefixCost frame (readings m)
    let ticks := ((labelTicks+publicBootCost a f.dst)+(minimumCost a.n+
      (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+
        (TeamBudget.setup.slots+(R+1)*(TeamBudget.row.slots+1)+1))))+directoryTicks a frame
    BootPins pub f ext raw m → a.header = physical → frame+112 ≤ a.header.header →
      f.dst+raw.length ≤ a.header.header → 2 ≤ a.header.d → 0 < a.header.blocks →
      0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w → LabelPrefixFits frame w (readings m) →
      readings m (frame+11) = a.cells → f.teams = R+1 → a.teams = R+1 → (old 0).val = X →
      1000000 < 2^w → 1000000*X*(R+1) < 2^w → controls+10 < a.header.header →
      readings m (frame+92)=controls ∧ readings m (controls+9)=a.cellBank ∧ readings m (controls+10)=a.cellStride →
      ∃ tr mid selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) s m tr mid selected ∧
        traceCost tr ≤ labelTicks ∧ (∀ x < a.publicBase, readings selected x = readings m x) ∧
        let input := powerHeaderImage a f.dst (readings selected)
        let groupNo := fun g : Fin a.header.d => (TeamNative.owner R (wl.weight input) g.val).val
        let rows := fun p j => readCode (a.header.cap+1) (decl.2 p j)
        (declarationInRange decl → (∑ i ∈ Finset.range a.header.d, wl.weight input i) < 2^w) →
        TestRun pub mac (.block (beforeWriters a.n (selectorWidth a.n a.K a.h))) s m ticks
          (declarationInRange decl ∧ declaredMinimum decl ∧ capacities wl tl X input)
          (fun z => NativeEntry a frame controls axis R input (readings m) z.mem ∧
            DirectorySources a frame controls axis (fun mem => a.ScannerWords frame f.team index groupNo (readings pub) mem rows) w z.mem) := by
  intro frame raw physical ext index axis wl tl labelTicks ticks pins shape primary extent two blocks bank room fit cells teams reserved budget million scaled ctl controlWords
  have alpha : 0 < a.header.d := by omega
  obtain ⟨tr,mid,selected,run,cost,atLabel,kept,first⟩ := groupPrefix_of_arena pub f a old fresh gates outputs width off ell mac s m G claims pad decl R X
    pins shape primary extent alpha blocks bank room fit cells teams reserved budget million scaled
  refine ⟨tr,mid,selected,run,cost,kept,?_⟩
  intro input groupNo rows mass
  have group := first mass
  by_cases valid : declarationInRange decl
  · have high : a.header.header ≤ a.publicBase := header_le_publicBase a
    have cellCount := (kept (frame+11) (by omega)).trans cells
    have checked := checkedFrame_of_pins pub f a old fresh gates outputs width off ell mac mid selected G claims pad decl R X
      atLabel shape primary extent cellCount teams reserved budget alpha blocks bank room million scaled valid (mass valid)
    have idx : axis.val = index := Nat.mod_eq_of_lt valid.1
    have cf : GroupWeights.CheckedFrame (weightLayout a frame axis.val) tl input w X := by
      rw [idx]; exact checked
    apply beforeWriters_test a controls axis input _ cf _ (DirectoryPointers.of_boot a old fresh G.length gates outputs width off ell controls pins controlWords room)
      two bank primary ctl room
    exact group.mono le_rfl Iff.rfl (fun _ z => ⟨by rw [idx]; exact z.1,z.2⟩)
  · refine ⟨fun h => (valid h.1).elim,?_⟩
    intro es t mt path
    let core := [LabelIndex.directoryProgram,NativeIntervals.prepare,CubePowers.install,
      install a.n (selectorWidth a.n a.K a.h),HeaderDecode.program,CubeLengths.minimum,GroupWeights.checkedSchedule]
    change Runs pub mac (.block (core++[CellBanks.install,PairDirectory.directory])) s m es t mt at path
    obtain ⟨_,_,_,_,_,early,_⟩ := Runs.seq_iff.mp ((Runs.block_append_iff (by simp [core]) (by simp)).mp path)
    exact (valid (group.sound early).1.1).elim

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
