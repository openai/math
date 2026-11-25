import OAI.ThreeFlat.Diagonal.NavigationDirectory
import OAI.ThreeFlat.RAM.NavigationNodeFields

namespace OAI
/-! # Chronological layer addresses issued by the native compressor -/

namespace ThreeFlat.Diagonal.NavigationPass
open RAM.NavigationNodeRows NavigationDirectory

def successors : Stage → ℕ
  | .shrink x => x.outputSites
  | .refresh v m l h p => (RefreshStageLayout.counts v m l h p).nodes

def childArity : Stage → ℕ
  | .shrink x => x.oldDegree*2^x.colorBits
  | .refresh .. => 1

def stageKind : Stage → ℕ | .shrink _ => 1 | .refresh .. => 2

def nodeLayer (K : ℕ) (c : Cursor) (s : Stage) : Layer :=
  let a := allocate K c s
  ⟨a.next.node,successors s,stageKind s,childArity s,a.words 42,a.words 34,a.words 38,c.header⟩

structure Layers where
  actual : Layer
  parent : Parent

/-- Every slot of the last layer is its own parent. During all previous
passes its parent has ordinal read from the *following* stage's output. -/
def nodeLayers (K : ℕ) : List Stage → Cursor → Layer → List Layers
  | [],_,layer => [⟨layer,⟨true,0,0⟩⟩]
  | s :: rest,c,layer =>
    let entry := allocate K c s
    ⟨layer,⟨false,entry.next.node,entry.words 44⟩⟩ ::
      nodeLayers K rest entry.next (nodeLayer K c s)

@[simp] theorem nodeLayers_length (K : ℕ) (s : List Stage) (c : Cursor) (layer : Layer) :
    (nodeLayers K s c layer).length=s.length+1 := by
  induction s generalizing c layer with
  | nil => rfl
  | cons hd tail ih => simp [nodeLayers,ih]

end ThreeFlat.Diagonal.NavigationPass

end OAI
