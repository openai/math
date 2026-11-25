import OAI.ThreeFlat.Diagonal.NavigationDirectory
import OAI.ThreeFlat.RAM.TerminalWireHeader

namespace OAI
/-! # The original archive address space and its public chronological directory -/
namespace ThreeFlat.Diagonal.NavigationPass
open RAM
structure Archive where
  control : ℕ
  phase : ℕ
  rawStatic : ℕ
  rawCodebook : ℕ
  staticCodebook : ℕ
  codebookWords : ℕ
  oldHistory : ℕ
  newHistory : ℕ
  pairCapacity : ℕ
  seed : ℕ
  initialRecords : ℕ
  initialDegree : ℕ
  axes : ℕ
  relayWidth : ℕ
  remainingLanes : ℕ
  cursor : NavigationDirectory.Cursor
  K : ℕ

def Archive.initialSites (A : Archive) := A.axes*A.remainingLanes

def Archive.seedWords (A : Archive) : ℕ → ℕ
  | 0 => A.cursor.graph
  | 1 => 6*(A.axes*A.initialDegree)
  | 2 => A.cursor.width
  | 3 => A.axes*A.initialDegree*A.remainingLanes
  | 4 => A.axes
  | 5 => A.initialDegree
  | 6 => A.remainingLanes
  | 7 => A.initialRecords
  | 8 => 5*A.initialSites
  | 9 => A.initialRecords+5*A.initialSites
  | 10 => 2*A.initialSites
  | 11 => A.initialRecords+7*A.initialSites
  | 12 => 8*A.initialDegree*A.initialSites
  | _ => 0

def Archive.histWords (A : Archive) (steps : List NavigationDirectory.Stage) :=
  A.K*(steps.map NavigationDirectory.Stage.motifs).sum

def Archive.terminal (A : Archive) (steps : List NavigationDirectory.Stage) (finalEdges W : ℕ) :
    TerminalWireArchive.Layout :=
  let finalCursor := NavigationDirectory.finish A.K steps A.cursor
  let H := W*A.histWords steps
  ⟨A.control,A.phase,A.oldHistory+H,A.newHistory+H,A.pairCapacity-H,finalCursor.width,finalEdges,finalCursor.heap⟩

def Archive.directory (A : Archive) (steps : List NavigationDirectory.Stage) (finalEdges W : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin 64 => A.seedWords i.val) ++ (NavigationDirectory.tape A.K steps A.cursor ++
    List.ofFn (fun i : Fin 64 => TerminalWireArchive.header (A.terminal steps finalEdges W) i.val))

@[simp] theorem Archive.directory_length (A : Archive) (steps : List NavigationDirectory.Stage)
    (finalEdges W : ℕ) : (A.directory steps finalEdges W).length=64*(steps.length+2) := by
  simp [Archive.directory,Nat.mul_add]

end ThreeFlat.Diagonal.NavigationPass

end OAI
