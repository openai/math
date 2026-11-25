import OAI.Computability.BorderVNP.CubeRouteRawHistogram
import OAI.Computability.BorderVNP.CubeRoutePinnedSchedule

/-! # The real public schedule on every binary candidate declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open LocalRow CubeArena CubeHeaderInstall TeamContraction.JointHeader Transmission

variable {w : ℕ}
variable {a : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {pins : Pins.Layout} {pub : Arg → Word w} {slotted : Memory w} {base : ℕ}
variable {I : Type*} [Fintype I] {cell : I → Fin a.cells} {id : I ↪ ℕ} {widths : I → ℕ}
local notation "initialRAM" => Packing.Directory.ISA.publish slotted (Fin.val (pub 0)) base (D.directory pp lp)
local notation "num" => List.length (D.directory pp lp)

/-- The native eleven-pass schedule succeeds exactly when the raw range, least coordinate and
physical load guards hold. All histogram words fit prior to the guards from the concrete geometry
and literal source room, including at incorrect row declarations. -/
theorem SlottedWriter.raw_schedule (P : SlottedWriter a D pp lp pins pub slotted base cell id widths)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (G : List Bool) (claims : List (List Bool)) (pad : ℕ)
    (rawDecl : Broadcast a.n a.header.d a.header.cap) (R X : ℕ) :
    let frame := (pub 0).val
    let raw := padded (spelling (G++DeclarationBits.spelling rawDecl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w a.header.d a.n a.header.blocks a.b a.h a.s
    let ext := jointFields (a.extension old) fresh G.length gates outputs width off ell a.header.d a.n a.header.blocks a.b a.h a.s
    let index := readCode (a.n+1) rawDecl.1
    let axis := Fin.ofNat (a.n+1) index
    let decl : LengthDeclaration a.n a.header.d := (axis,fun p j => readCode (a.header.cap+1) (rawDecl.2 p j))
    let wl := weightLayout a frame index
    let tl := teamLayout a R
    let labelTicks := labelPrefixCost frame (readings initialRAM)
    let ticks := ((labelTicks+publicBootCost a f.dst)+(minimumCost a.n+
      (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+
        (TeamBudget.setup.slots+(R+1)*(TeamBudget.row.slots+1)+1))))+directoryTicks a frame
    BootPins pub f ext raw initialRAM → a.header=physical → frame+112 ≤ a.header.header → f.dst+raw.length ≤ a.header.header →
      2 ≤ a.header.d → 0 < a.header.blocks → 0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w →
      LabelPrefixFits frame w (readings initialRAM) → readings initialRAM (frame+11)=a.cells → f.teams=R+1 → a.teams=R+1 →
      (old 0).val=X → 1000000 < 2^w → 1000000*X*(R+1) < 2^w → controls+10 < a.header.header →
      readings initialRAM (frame+92)=controls ∧ readings initialRAM (controls+9)=a.cellBank ∧
        readings initialRAM (controls+10)=a.cellStride →
      0 < D.processors → 0 < D.block → D.fields ≤ 2 →
      1000000*(a.stop+3*D.teams*(D.processors*D.literal))+2*a.stop < 2^w →
      num+a.header.d.choose 2 ≤ a.maxRows →
      ∃ tr mid selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg initialRAM tr mid selected ∧
        traceCost tr ≤ labelTicks ∧ (∀ x < a.publicBase, readings selected x=readings initialRAM x) ∧
        let input := powerHeaderImage a f.dst (readings selected)
        let group := fun j : Fin a.header.d => TeamNative.owner R (wl.weight input) j.val
        let owner := a.receivingOwner frame axis R input
        let pass := declarationInRange rawDecl ∧ declaredMinimum rawDecl ∧ capacities wl tl X input
        TestRun pub mac (.block (beforeWriters a.n (selectorWidth a.n a.K a.h))) reg initialRAM ticks pass
          (fun z => WriterSources a frame controls f.team R decl group (readings pub) input (readings initialRAM) z.mem w) ∧
        PublicSchedule a D pp lp owner decl group pins pub mac reg initialRAM (ticks+writerTicks num a.header.d) pass := by
  intro frame raw physical ext index axis decl wl tl labelTicks ticks boot shape low copied two blocks bank fit
    dirFit cellNum teams reserved budget million scaled control pointers processors block fields rawRoom rows
  obtain ⟨tr,mid,selected,run,cost,keep,finish⟩ := P.pinned_schedule_with_sources f old fresh gates outputs
    width off ell controls mac reg G claims pad rawDecl R X boot shape low copied two blocks bank fit dirFit cellNum
    teams reserved budget million scaled control pointers rows
  have mass := P.raw_histogram_room f old fresh gates outputs width off ell mac reg G claims pad rawDecl boot shape
    low copied (by omega) blocks bank fit dirFit cellNum processors block fields rawRoom run
  exact ⟨tr,mid,selected,run,cost,keep,finish mass⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
