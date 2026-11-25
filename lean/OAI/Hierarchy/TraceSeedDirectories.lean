import OAI.ThreeFlat.Diagonal.PhysicalBlockRecordBounds
import OAI.ThreeFlat.Diagonal.NavigationArchiveDirectory
import OAI.ThreeFlat.Diagonal.ProgramEdgeCount

namespace OAI
/-! # The two public seed directory layouts at their physical addresses -/
namespace Hierarchy.TraceSeedWriter
open ThreeFlat Diagonal Diagonal.PhysicalStage NavigationPass NavigationDirectory
open scoped Classical
variable {F : Type} [Field F] (B : Block F)
noncomputable section
/-- The shared native seed, histogram, graph and control layout used by the
receiver. The two selector channels address the same body following its flag. -/
def archive (w axes off slots cap rawStatic : ℕ) : Archive :=
  let J:=2^(32*w)
  let S:=(2^w)^4
  let β:=16*J
  { control:=β+6*S, phase:=12*J, rawStatic:=rawStatic, rawCodebook:=rawStatic,
    staticCodebook:=β, codebookWords:=0, oldHistory:=12*J+1, newHistory:=12*J+1,
    pairCapacity:=cap, seed:=β, initialRecords:=β+4*S, initialDegree:=2^(B.exponent 0),
    axes:=axes, relayWidth:=2^(w/2)*(off*slots*3), remainingLanes:=2^axes,
    cursor:={header:=β+64,dense:=β+S,heap:=β+5*S,node:=0,graph:=β+2*S,width:=β+3*S},
    K:=B.alphabetCap }

/-- The bytes describing the public schedule depend only on the word size,
shape and terminal capacity. Moving their source address or changing the
input machine's relay multiplicity preserves all directory bytes. -/
theorem archive_directory (w axes off slots cap rawStatic : ℕ) (steps : List Stage) (edges : ℕ) :
    (archive B w axes off slots cap rawStatic).directory steps edges (64*w) =
      (archive B w axes 0 0 cap 0).directory steps edges (64*w) := rfl

private theorem length_cast {i j : ℕ} (e : i=j) (Q : Program F i) :
    (e ▸ Q : Program F j).length=Q.length := by subst j;rfl

private theorem prefix_length (n i : ℕ) (Q : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i Q).length=n+Q.length := by
  induction n generalizing i with
  | zero => simp [Block.shrinkPrefix]
  | succ n ih =>
    simp only [Block.shrinkPrefix,Program.length,ih,length_cast]
    omega

theorem repeat_length (n : ℕ) : (B.repeat n).length=(B.levels+1)*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Block.repeat,Block.«prefix»,prefix_length,length_cast,Program.length,ih,Nat.mul_succ]
    omega

end
end Hierarchy.TraceSeedWriter

namespace Hierarchy.TraceCompactSeed
open ThreeFlat Diagonal Diagonal.PhysicalStage NavigationPass
open scoped Classical
variable {F : Type} [Field F] (B : Block F)

/-- All mutable arrays live at the shifted public base. Both history input channels read the
selector body already present in the compact tick header. -/
noncomputable def archive (w β axes off slots cap rawStatic phase : ℕ) : Archive :=
  let S:=(2^w)^4
  { control:=β+6*S, phase:=phase, rawStatic:=rawStatic, rawCodebook:=rawStatic,
    staticCodebook:=β, codebookWords:=0, oldHistory:=phase+1, newHistory:=phase+1,
    pairCapacity:=cap, seed:=β, initialRecords:=β+4*S, initialDegree:=2^(B.exponent 0),
    axes:=axes, relayWidth:=2^(w/2)*(off*slots*3), remainingLanes:=2^axes,
    cursor:={header:=β+64,dense:=β+S,heap:=β+5*S,node:=0,graph:=β+2*S,width:=β+3*S},
    K:=B.alphabetCap }

noncomputable def directory (w β axes n cap phase : ℕ) : List ℕ :=
  let P:=B.repeat n
  let rem:=axes-P.charge
  (archive B w β axes 0 0 cap 0 phase).directory (P.directory rem axes) (P.finalEdges rem axes) (64*w)

theorem directory_length (w β axes n cap phase : ℕ) :
    (directory B w β axes n cap phase).length=64*((B.levels+1)*n+2) := by
  unfold directory
  rw [Archive.directory_length,Program.directory_length]
  rw [TraceSeedWriter.repeat_length]

theorem archive_directory (w β axes n off slots cap rawStatic phase : ℕ) :
    let P:=B.repeat n
    let rem:=axes-P.charge
    (archive B w β axes off slots cap rawStatic phase).directory (P.directory rem axes) (P.finalEdges rem axes) (64*w)=
      directory B w β axes n cap phase := rfl

end Hierarchy.TraceCompactSeed

end OAI
