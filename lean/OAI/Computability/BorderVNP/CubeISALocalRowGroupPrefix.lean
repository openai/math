import OAI.Computability.BorderVNP.CubeISALocalRowGroupCheckedFrame
import OAI.Computability.BorderVNP.CubeTeamOwnedPublicPrefix

/-! # Checked execution of the first seven public scheduling stages in the fixed arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open CubeHeaderInstall TeamContraction.JointHeader Finset

/-- From the physical primary words and copied declaration, execute label selection,
directed intervals, powers, the static and dynamic header, the first-minimum test and
checked group assignment. Surplus declaration codes reject before any group arithmetic. -/
theorem groupPrefix_of_arena {w : ℕ} (pub : Arg → Word w) (f : BroadcastFrame)
    (a : CubeArena.Layout) (old : Fin 81 → Word w) (fresh gates outputs width off ell : ℕ)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (m : Memory w)
    (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (decl : Broadcast a.n a.header.d a.header.cap)
    (r X : ℕ) :
    let frame := (pub 0).val
    let raw := padded (TeamContraction.JointHeader.spelling (G++DeclarationBits.spelling decl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w a.header.d a.n a.header.blocks a.b a.h a.s
    let ext := jointFields (a.extension old) fresh G.length gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s
    let labelTicks := labelPrefixCost frame (readings m)
    let wl := weightLayout a frame (readCode (a.n+1) decl.1)
    let tl := teamLayout a r
    BootPins pub f ext raw m → a.header = physical → frame+112 ≤ a.header.header →
      f.dst+raw.length ≤ a.header.header → 0 < a.header.d → 0 < a.header.blocks →
      0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w → LabelPrefixFits frame w (readings m) →
      readings m (frame+11) = a.cells → f.teams = r+1 → a.teams = r+1 → (old 0).val = X →
      1000000 < 2^w → 1000000*X*(r+1) < 2^w →
      ∃ tr mid selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg m tr mid selected ∧
        traceCost tr ≤ labelTicks ∧ BootPins pub f ext raw selected ∧
        (∀ x < a.publicBase, readings selected x = readings m x) ∧
        let input := powerHeaderImage a f.dst (readings selected)
        let groupNo := fun g : Fin a.header.d => (TeamNative.owner r (wl.weight input) g.val).val
        let rows := fun p j => readCode (a.header.cap+1) (decl.2 p j)
        (declarationInRange decl → (∑ i ∈ range a.header.d, wl.weight input i) < 2^w) →
          TestRun pub mac (groupPrefix a.n (selectorWidth a.n a.K a.h)) reg m
            ((labelTicks+publicBootCost a f.dst)+(minimumCost a.n+
              (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+
                (TeamBudget.setup.slots+(r+1)*(TeamBudget.row.slots+1)+1))))
            (declarationInRange decl ∧ declaredMinimum decl ∧ capacities wl tl X input)
            (fun z => GroupWeights.ScheduleResult wl tl input z.mem ∧
              a.ScannerWords (readings pub 0) f.team (readCode (a.n+1) decl.1) groupNo (readings pub) z.mem rows ∧
              ∀ x < a.header.header, z.mem x = readings m x) := by
  intro frame raw physical ext labelTicks wl tl pins eq primary extent alpha blocks stride high fitted count teams reserved budget million scaled
  obtain ⟨es,mid,selected,run,cost,atLabel,groups⟩ := groupPrefix_pinned pub f a old fresh gates outputs width off ell
    mac reg m G claims pad decl pins eq primary extent alpha blocks stride high fitted
  obtain ⟨low,cell⟩ := labelPrefix_preserved pub mac fitted run
  have limit := pins.arenaOperand a old fresh G.length gates outputs width off ell (k := 48)
    (value := a.publicBase) rfl (by have := a.separated; omega)
  change readings m (frame+48) = a.publicBase at limit
  refine ⟨es,mid,selected,run,cost,atLabel,fun x h => low x (limit ▸ h),?_⟩
  intro input groupNo rows mass
  by_cases valid : declarationInRange decl
  · have assigned := checkedFrame_of_pins pub f a old fresh gates outputs width off ell mac mid selected
      G claims pad decl r X atLabel eq primary extent (cell.trans count) teams reserved budget
      alpha blocks stride high million scaled valid (mass valid)
    exact groups wl tl X rfl assigned (mass valid) rfl rfl rfl rfl
  · obtain ⟨_,_,_,_,_,_,_,first⟩ := labelBoot_pinned pub f a old fresh gates outputs width off ell
      mac reg m G claims pad decl pins eq primary extent alpha blocks stride high fitted
    refine ⟨fun h => (valid h.1).elim,?_⟩
    intro fs u mu path
    let initial := [LabelIndex.directoryProgram,NativeIntervals.prepare,CubePowers.install,
      install a.n (selectorWidth a.n a.K a.h),HeaderDecode.program]
    let remaining := [CubeLengths.minimum,GroupWeights.checkedSchedule]
    change Runs pub mac (.block (initial++remaining)) reg m fs u mu at path
    obtain ⟨_,_,_,_,_,early,_⟩ := Runs.seq_iff.mp
      ((Runs.block_append_iff (by simp [initial]) (by simp [remaining])).mp path)
    exact (valid (first.sound early).1).elim

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
