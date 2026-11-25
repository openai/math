import OAI.Computability.BorderVNP.CubeRoutePinnedSchedule
import OAI.Computability.BorderVNP.CubeTeamOwnedCanonicalInput

/-! # The actual schedule return on the canonical declaration of a packet assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open LocalRow CubeArena CubeHeaderInstall TeamContraction.JointHeader Transmission
open private canonicalRead from OAI.Computability.BorderVNP.CubeTeamOwnedScheduledWords

variable {w R : ℕ} {a : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {pins : Pins.Layout} {pub : Arg → Word w} {slotted : Memory w} {base : ℕ}
variable {I : Type*} [Fintype I] {cell : I → Fin a.cells} {id : I ↪ ℕ} {widths : I → ℕ}
local notation "initialRAM" => Packing.Directory.ISA.publish slotted (Fin.val (pub 0)) base (D.directory pp lp)
local notation "num" => List.length (D.directory pp lp)

private theorem actualMinimum {n d blocks b h K s cap : ℕ} (sel : Packet n d blocks → Selector n K h)
    (raw : Broadcast n d cap) (size : cap = declarationCap n d blocks b h s)
    (spells : (size ▸ raw) = broadcast b s sel) : declarationInRange raw ∧ declaredMinimum raw := by
  subst cap
  change raw = broadcast b s sel at spells
  subst raw
  exact broadcast_passes_minimum b s sel

/-- For the true packet declaration the reached histogram passes every capacity guard.
The returned prefix records both physical directory images, and the full eleven native passes
yield the two writer receipts and their exact clock. -/
theorem SlottedWriter.canonical_schedule (P : SlottedWriter a D pp lp pins pub slotted base cell id widths)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (G : List Bool) (claims : List (List Bool)) (pad : ℕ)
    (select : Packet a.n a.header.d a.header.blocks → Selector a.n a.K a.h) (rawDecl : Broadcast a.n a.header.d a.header.cap)
    (R X : ℕ) :
    let frame := (pub 0).val
    let raw := padded (spelling (G++DeclarationBits.spelling rawDecl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w a.header.d a.n a.header.blocks a.b a.h a.s
    let ext := jointFields (a.extension old) fresh G.length gates outputs width off ell a.header.d a.n a.header.blocks a.b a.h a.s
    let i := chosen a.b a.s select
    let decl : LengthDeclaration a.n a.header.d := (i,subtotals itemRow (crossCount a.b a.s select) i)
    let wl := weightLayout a frame i.val
    let tl := teamLayout a R
    let labelTicks := labelPrefixCost frame (readings initialRAM)
    let ticks := ((labelTicks+publicBootCost a f.dst)+(minimumCost a.n+
      (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+
        (TeamBudget.setup.slots+(R+1)*(TeamBudget.row.slots+1)+1))))+directoryTicks a frame
    CanonicalInput pub mac f a ext raw R X i.val reg initialRAM → ∀ shape : a.header = physical,
      (show a.header.cap = declarationCap a.n a.header.d a.header.blocks a.b a.h a.s by rw [shape]; rfl) ▸ rawDecl = broadcast a.b a.s select →
      frame+112 ≤ a.header.header → f.dst+raw.length ≤ a.header.header → 2 ≤ a.header.d → 0 < a.header.blocks →
      0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w → f.teams=R+1 → a.teams=R+1 → (old 0).val=X →
      1000000 < 2^w → 1000000*X*(R+1) < 2^w → controls+10 < a.header.header →
      readings initialRAM (frame+92)=controls ∧ readings initialRAM (controls+9)=a.cellBank ∧
        readings initialRAM (controls+10)=a.cellStride → num+a.header.d.choose 2 ≤ a.maxRows →
      ∃ tr mid selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg initialRAM tr mid selected ∧
        traceCost tr ≤ labelTicks ∧ (∀ x < a.publicBase, readings selected x=readings initialRAM x) ∧
        let input := powerHeaderImage a f.dst (readings selected)
        let group := fun j : Fin a.header.d => TeamNative.owner R (wl.weight input) j.val
        let owner := a.receivingOwner frame i R input
        TestRun pub mac (.block (beforeWriters a.n (selectorWidth a.n a.K a.h))) reg initialRAM ticks True
          (fun z => WriterSources a frame controls f.team R decl group (readings pub) input (readings initialRAM) z.mem w) ∧
        PublicSchedule a D pp lp owner decl group pins pub mac reg initialRAM (ticks+writerTicks num a.header.d) True := by
  intro frame raw physical ext i decl wl tl labelTicks ticks canonical shape spells low copied two blocks bank fit teams reserved
    budget million scaled control pointers rows
  have size : a.header.cap = declarationCap a.n a.header.d a.header.blocks a.b a.h a.s := by rw [shape]; rfl
  obtain ⟨ix,vals⟩ := canonicalRead select rawDecl size spells
  have actual := actualMinimum select rawDecl size spells
  obtain ⟨tr,mid,selected,run,cost,kept,full⟩ := P.pinned_schedule_with_sources f old fresh gates outputs width off ell controls
    mac reg G claims pad rawDecl R X canonical.boot shape low copied two blocks bank fit canonical.fit canonical.cells
    teams reserved budget million scaled control pointers rows
  have eqFin : Fin.ofNat (a.n+1) i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  change readCode (a.n+1) rawDecl.1 = i.val at ix
  simp only [ix,eqFin,vals] at full
  have valid := canonical.guard run
  obtain ⟨before,complete⟩ := full (fun _ => valid.1)
  have admitted := And.intro actual.1 (And.intro actual.2 valid.2)
  refine ⟨tr,mid,selected,run,cost,kept,before.mono le_rfl ⟨fun _ => trivial,fun _ => admitted⟩ (fun _ h => h),
    fun _ => complete.1 admitted,?_⟩
  intro es t mt ret
  exact ⟨trivial,(complete.2 ret).2⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
