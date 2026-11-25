import OAI.Hierarchy.GridNativeImageLayout
import OAI.Hierarchy.GridRegisteredRunData
import OAI.Hierarchy.GridStructuralHeader
import OAI.Hierarchy.TraceReceiverAge
import OAI.Hierarchy.TraceReceiverMaskBanks
import OAI.ThreeFlat.Diagonal.TraceBucketImage
import OAI.ThreeFlat.RAM.TraceRawLookup

namespace OAI
/-! # Fixed addresses and table operands of a receiver leaf -/

namespace Hierarchy.TraceReceiverLeafSetup
open ThreeFlat Diagonal Diagonal.PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open GridRegisteredSetting TraceBitHeader
noncomputable section
variable {F : Type} [Fintype F] [Field F] {w pc regs slots S base fuel axes : ℕ}
open scoped Fin.CommRing

def gateBase (_ : RunData F (64*w) pc regs slots S base fuel axes (w/2)) : ℕ := 26*GridDescription.sector w
def dict (_ : RunData F (64*w) pc regs slots S base fuel axes (w/2)) : ℕ := 27*GridDescription.sector w
def masks (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)) : ℕ := dict D+2^((axes+1)+w/2)
def tmp (D : RunData F (64*w) pc regs slots S base fuel axes (w/2)) : ℕ := masks D+TraceReceiverMaskBanks.count (axes+1) (w/2)

def start (w : ℕ) := TickWorkspace.base (TraceAdmission.receiverAge w) 38
def pages (w : ℕ) := 64*w
def intervalBase (w : ℕ) := TickWorkspace.base (TraceAdmission.receiverAge w) 5

variable (D : RunData F (64*w) pc regs slots S base fuel axes (w/2))

private abbrev gates := TraceStaticRow.gateTable (F:=F) D.field D.fit.width D.fit.labels
  base fuel D.state regs slots ((axes+1)+w/2)

def templateSize : ℕ := TraceReceiverTemplate.count (gates D)

def templateSrc (l : GridNativeImage.Layout) : ℕ := 2+SelfAdvice.textSize (64*w) pc slots+
  (64*w)*((GridStructuralHeader.directory (F:=F) (w:=w) D.block (axes+1) D.passes l.selectorCap).length+1)

def librarySrc (l : GridNativeImage.Layout) : ℕ := templateSrc D l+(64*w)*(templateSize D+
  (GridStructuralHeader.directory (F:=F) (w:=w) D.block (axes+1) D.passes l.selectorCap).length)

def shape : TraceBucketAtom.Layout :=
  bucketShape (F:=F) (w:=64*w) (p:=pc) (q:=axes) (low:=w/2) (S:=S) (f:=fuel)
    D.field D.fit.width D.fit.labels base D.state regs slots D.block.cursorCopies 0
    (dict D) (masks D) (gateBase D+FixedTraceImage.count (gates D))

def rom : TraceRawLookup.Layout :=
  let net := TraceBitHeader.network (F:=F) (S:=S) (f:=fuel) D.field D.fit.width D.fit.labels base
    D.state D.fit.header D.fit.time regs slots ((axes+1)+w/2)
  ⟨0,net.cells,gateBase D+FixedTraceImage.count (gates D)+(gates D).cells⟩

def rest (_ : RunData F (64*w) pc regs slots S base fuel axes (w/2)) : Fin 1 → Word (64*w) := fun _=>0


end
end Hierarchy.TraceReceiverLeafSetup

end OAI
