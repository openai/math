import OAI.Computability.BorderVNP.CubeRouteCompleteSchedule

/-! # Pinned execution and rejection of the eleven-stage public schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open LocalRow CubeArena CubeHeaderInstall TeamContraction.JointHeader Transmission

variable {w R : ℕ}

/-- The exact success criterion, clock and written row inventory for the native schedule at one team. -/
def PublicSchedule (ar : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (owner : ℕ → Fin (R+1)) (decl : LengthDeclaration ar.n ar.header.d) (group : Fin ar.header.d → Fin (R+1))
    (pins : Pins.Layout) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (reg : Bank w) (m : Memory w)
    (ticks : ℕ) (pass : Prop) : Prop :=
  (pass → ∃ es t mt, ∃ H : WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) pub mac reg m es t mt,
    ReturnedWriters ar D pp lp owner decl group pins H ∧ traceCost es ≤ ticks) ∧
  (∀ {es t mt}, Runs pub mac (scheduleGroups ar.n (selectorWidth ar.n ar.K ar.h)) reg m es t mt → pass ∧
    ∃ H : WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) pub mac reg m es t mt,
      ReturnedWriters ar D pp lp owner decl group pins H)

/-- Charge of both real descriptor writers after the public cell and pair directories. -/
def writerTicks (dataCount groups : ℕ) : ℕ :=
  DataWriter.setup.slots+dataCount*(DataWriter.step.slots+1)+5+SharedRows.budget groups

variable {a : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {pins : Pins.Layout} {pub : Arg → Word w} {slotted : Memory w} {base : ℕ}
variable {I : Type*} [Fintype I] {cell : I → Fin a.cells} {id : I ↪ ℕ} {widths : I → ℕ}
local notation "initialRAM" => Packing.Directory.ISA.publish slotted (Fin.val (pub 0)) base (D.directory pp lp)
local notation "num" => List.length (D.directory pp lp)

/-- Execute the complete signed group schedule on the real raw directory publication.
The native decisions are precisely the decoded range, least coordinate and actual team capacities. -/
theorem SlottedWriter.pinned_schedule_with_sources (P : SlottedWriter a D pp lp pins pub slotted base cell id widths)
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
      num+a.header.d.choose 2 ≤ a.maxRows →
      ∃ tr mid selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg initialRAM tr mid selected ∧
        traceCost tr ≤ labelTicks ∧ (∀ x < a.publicBase, readings selected x=readings initialRAM x) ∧
        let input := powerHeaderImage a f.dst (readings selected)
        let group := fun j : Fin a.header.d => TeamNative.owner R (wl.weight input) j.val
        let owner := a.receivingOwner frame axis R input
        let pass := declarationInRange rawDecl ∧ declaredMinimum rawDecl ∧ capacities wl tl X input
        (declarationInRange rawDecl → (∑ i ∈ Finset.range a.header.d, wl.weight input i) < 2^w) →
          TestRun pub mac (.block (beforeWriters a.n (selectorWidth a.n a.K a.h))) reg initialRAM ticks pass
            (fun z => WriterSources a frame controls f.team R decl group (readings pub) input (readings initialRAM) z.mem w) ∧
          PublicSchedule a D pp lp owner decl group pins pub mac reg initialRAM (ticks+writerTicks num a.header.d) pass := by
  intro frame raw physical ext index axis decl wl tl labelTicks ticks boot shape low copied two blocks bank fit dirFit
    cellNum teams reserved budget million scaled control pointers rows
  obtain ⟨tr,mid,selected,run,cost,kept,test⟩ := beforeWriters_pinned pub f a old fresh gates outputs width off ell controls
    mac reg initialRAM G claims pad rawDecl R X boot shape low copied two blocks bank fit dirFit cellNum teams reserved budget
    million scaled control pointers
  refine ⟨tr,mid,selected,run,cost,kept,?_⟩
  intro input group owner pass mass
  let Q := fun z : NatState => WriterSources a frame controls f.team R decl group (readings pub) input (readings initialRAM) z.mem w
  have before : TestRun pub mac (.block (beforeWriters a.n (selectorWidth a.n a.K a.h))) reg initialRAM ticks pass Q := by
    by_cases good : declarationInRange rawDecl
    · have ix : axis.val = index := Nat.mod_eq_of_lt good.1
      exact (test mass).mono le_rfl Iff.rfl (fun z h => ⟨h.1,by simpa only [Q,decl,ix] using h.2⟩)
    · exact ⟨fun passed => (good passed.1).elim,fun path => (good ((test mass).sound path).1.1).elim⟩
  have axes : a.header.a = a.n+1 := by rw [shape]; rfl
  exact ⟨before,P.complete_schedule before (fun _ _ => rfl) low axes
    (fun passed p j => Nat.lt_succ_iff.mp (passed.1.2 p j)) rows fit⟩

/-- Execute the complete signed group schedule on the real raw directory publication.
The native decisions are precisely the decoded range, least coordinate and actual team capacities. -/
theorem SlottedWriter.pinned_schedule (P : SlottedWriter a D pp lp pins pub slotted base cell id widths)
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
      num+a.header.d.choose 2 ≤ a.maxRows →
      ∃ tr mid selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg initialRAM tr mid selected ∧
        traceCost tr ≤ labelTicks ∧ (∀ x < a.publicBase, readings selected x=readings initialRAM x) ∧
        let input := powerHeaderImage a f.dst (readings selected)
        let group := fun j : Fin a.header.d => TeamNative.owner R (wl.weight input) j.val
        let owner := a.receivingOwner frame axis R input
        let pass := declarationInRange rawDecl ∧ declaredMinimum rawDecl ∧ capacities wl tl X input
        (declarationInRange rawDecl → (∑ i ∈ Finset.range a.header.d, wl.weight input i) < 2^w) →
          PublicSchedule a D pp lp owner decl group pins pub mac reg initialRAM (ticks+writerTicks num a.header.d) pass := by
  intro frame raw physical ext index axis decl wl tl labelTicks ticks boot shape low copied two blocks bank fit dirFit
    cellNum teams reserved budget million scaled control pointers rows
  obtain ⟨tr,mid,selected,run,cost,kept,full⟩ := P.pinned_schedule_with_sources f old fresh gates outputs width off ell controls
    mac reg G claims pad rawDecl R X boot shape low copied two blocks bank fit dirFit cellNum teams reserved budget million
    scaled control pointers rows
  exact ⟨tr,mid,selected,run,cost,kept,fun mass => (full mass).2⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
