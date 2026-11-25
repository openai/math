import OAI.ThreeFlat.RAM.PhysicalInputRegions
import OAI.ThreeFlat.RAM.PhysicalTraceRows
import OAI.ThreeFlat.RAM.PhysicalPinsInput
import OAI.ThreeFlat.RAM.PackedTraceImage

namespace OAI
/-! # Data, external tape, and destination image of the physical evaluator -/

namespace ThreeFlat.RAM.PhysicalPrelude

open Computability.VPVNP.BurstRAM BitLayout Diagonal.TraceAddressRecord PhysicalInputRegions
open scoped Fin.CommRing

structure Image (F : Type*) [Fintype F] [Field F] (w : ℕ) where
  advice : ℕ
  endpointBits : ℕ
  auxBits : ℕ
  parameters : ℕ
  ports : ℕ
  rows : ℕ
  shared : ℕ
  exposed : ℕ
  H : BitNetwork F (PhysicalPinsInput.pinCount advice endpointBits auxBits)
  G : BitNetwork F ports
  input : Fin rows → Fin ports → BitSource shared exposed
  keys : Fin ports → Record
  field : FieldCode F w

variable {F : Type*} [Fintype F] [Field F] {w : ℕ} (I : Image F w)
namespace Image

noncomputable abbrev X := PhysicalTraceSource.expanded I.G I.input
abbrev pins := PhysicalPinsInput.pinCount I.advice I.endpointBits I.auxBits
abbrev firstCell := cellsBase I.pins I.H.internal
abbrev firstProduct := mulBase I.pins I.H.internal I.H.cells
abbrev products := Fintype.card F * Fintype.card F

noncomputable def sizes : Size :=
  ⟨I.endpointBits,I.advice,I.parameters,footprint I.H,I.X.cells,I.G.cells,I.ports,w⟩

/-- Only this initial prefix is constrained, including the polynomial local table.
All external memory past it can already contain a program or unrelated words. -/
structure Raw (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (params : Fin I.parameters → Bool) (m : Memory w) : Prop where
  input : ∀ j, j<I.sizes.rawParams → m j = bitWord w (PhysicalPinsInput.rawBit D x y j)
  parameters : ∀ j : Fin I.parameters,m (I.sizes.rawParams+j.val)=bitWord w (params j)
  metadata : ∀ j, m (I.sizes.rawTable+j.val) =
    ((FixedTraceImage.parameter I.G I.field I.keys j).toNat : Word w)

structure Fits : Prop where
  memory : I.sizes.limit<2^w
  ruleFits : ∀ (i : Fin I.rows) j, (I.keys j).Fits w i.val
  ports : ∀ (i : Fin I.rows) j,(I.keys j).eval i.val=sourceAddress (I.input i j)
  addresses : 2+I.ports+I.G.internal<2^w
  localCells : I.G.cells<2^w
  records : 11<2^w

structure Ready (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (params : Fin I.parameters → Bool) (m : Memory w) : Prop where
  low : ∀ a, a<I.firstCell →
    m a=memory I.H I.field (PhysicalPinsInput.logical D x y) (fun _=>false) a
  products : ∀ a, I.firstProduct≤a → a<footprint I.H →
    m a=memory I.H I.field (PhysicalPinsInput.logical D x y) (fun _=>false) a
  parameters : ∀ j : Fin I.parameters,m (I.sizes.parameterBase+j.val)=bitWord w (params j)
  template : ∀ (i : Fin I.X.cells) (j : Fin 11),m (I.sizes.templateBase+11*i.val+j.val)=record I.X I.field i j

end Image
end ThreeFlat.RAM.PhysicalPrelude

end OAI
