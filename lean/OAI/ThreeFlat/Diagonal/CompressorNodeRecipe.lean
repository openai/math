import OAI.ThreeFlat.Diagonal.CompressorNodeChildren
import OAI.ThreeFlat.Diagonal.CompressorNodeHalves
import OAI.ThreeFlat.Diagonal.CompressorStageBlocks

namespace OAI
/-! # Linked chronological producer of shrinking-site kernel and half records -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.NodeRecipe
open RAM.PhysicalPinsExpr
abbrev F := Formula 1

def kernelBase := 34
def incidentBase := 36
def halfBase := 38
def rowsBase := 40
def childrenBase := 42
def ownerBase := 44

def offset (start : ℕ) : F := .cut (.reg 0) (Template.f start)

def selectedAt (g : Bool → F) : F := .select .eq (Template.f selected) (.lit 1) (g true) (g false)

def kernel (S : Graph.Stage) (K kind : ℕ) : F :=
  let row := Formula.op .div (offset kernelBase) (.lit 5)
  let i := Formula.op .mod (offset kernelBase) (.lit 5)
  let count := selectedAt (fun l => Incidents.count Template.ptr S K l row)
  let hits := Formula.op .add (Template.f incidentBase) (.op .mul row (.lit (6*Incidents.capacity S)))
  .select .eq i (.lit 0) (.load Template.ptr) (.select .eq i (.lit 1) row
    (.select .eq i (.lit 2) (.lit kind) (.select .eq i (.lit 3) count hits)))

def motif (S : Graph.Stage) (K : ℕ) : F :=
  selectedAt (fun l => Incidents.record Template.ptr S K l (offset incidentBase))

def halfHeader (D : ℕ) : F :=
  let row := Formula.op .div (offset halfBase) (.lit 2)
  let i := Formula.op .mod (offset halfBase) (.lit 2)
  .select .eq i (.lit 0) (.lit (2*D)) (.op .add (Template.f rowsBase) (.op .mul row (.lit (8*D))))

def halfRows (D : ℕ) : F :=
  Halves.record (Halves.shrinkColumns Template.ptr) D (offset rowsBase)

def ownership (S : Graph.Stage) : Recipe :=
  let child := selectedAt (fun l => ChildRows.entry Template.ptr S l (offset childrenBase))
  let parent := selectedAt (fun l => ChildRows.parent Template.ptr S l (offset ownerBase))
  .seq (.one child childrenBase (childrenBase+1)) (.one parent ownerBase (ownerBase+1))

def localTables (S : Graph.Stage) (K kind : ℕ) : Recipe :=
  .seq (.one (kernel S K kind) kernelBase (kernelBase+1))
   (.seq (.one (motif S K) incidentBase (incidentBase+1))
   (.seq (.one (halfHeader S.outputDegree) halfBase (halfBase+1))
         (.one (halfRows S.outputDegree) rowsBase (rowsBase+1))))

def descriptors (S : Graph.Stage) (K kind : ℕ) : Recipe :=
  .seq (localTables S K kind) (ownership S)

/-- The selected graph and width arrays are materialized before the half
records dereference them. The six-word motif records use admitted histograms. -/
def after (S : Graph.Stage) (K kind : ℕ) : Recipe :=
  .seq (afterRecipe S) (descriptors S K kind)

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.NodeRecipe

end OAI
