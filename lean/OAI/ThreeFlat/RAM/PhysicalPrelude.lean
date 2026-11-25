import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.PhysicalImageData
import OAI.ThreeFlat.RAM.PhysicalTraceSource
import OAI.ThreeFlat.RAM.PhysicalFieldTable
import OAI.ThreeFlat.RAM.PhysicalPinsInput

namespace OAI
/-! # The actual six-phase H initialization procedure on a paired binary input tape -/

namespace ThreeFlat.RAM.PhysicalPrelude

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure PhysicalInputPhases DescriptorExpr BitLayout
open Diagonal.TraceAddressRecord PhysicalInputRegions
open scoped Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {w : ℕ} (I : Image F w)
namespace Image

def blank : Fin 0 → Word w := Fin.elim0

noncomputable def Xdata : Fin FixedTraceProgram.P → Word w :=
  Fin.addCases (fun _ : Fin 2 => 0) (Fin.addCases (fun _ : Fin 5 => 0)
    (FixedTraceProgram.publicWords I.G I.field I.exposed I.shared I.sizes.templateBase
      I.sizes.gateBase I.sizes.portBase))

theorem Xdata_public (i : Fin 11) : I.Xdata (FixedTraceProgram.extra i) =
    FixedTraceProgram.publicWords I.G I.field I.exposed I.shared I.sizes.templateBase
      I.sizes.gateBase I.sizes.portBase i := by
  simp only [Xdata,FixedTraceProgram.extra,Fin.addCases_right]

noncomputable def firstWords : Term w 0 1 :=
  PhysicalPinsInput.low I.advice I.endpointBits I.auxBits I.sizes.scratch

noncomputable def productWord : Term w 0 1 :=
  PhysicalFieldTable.atAddress I.field (.literal (I.firstProduct : Word w)) (.result 0)

noncomputable def stage : Procedure w := copying w 0 I.sizes.rawCount I.sizes.scratch
noncomputable def pack : Procedure w := packing w (I.sizes.scratch+I.sizes.rawTable) I.sizes.gateBase I.sizes.packedWords
noncomputable def params : Procedure w := copying w (I.sizes.scratch+I.sizes.rawParams) I.parameters I.sizes.parameterBase
noncomputable def trace : Procedure w := writing (FixedTraceProgram.program w) I.Xdata I.sizes.templateBase (11*I.X.cells)
noncomputable def low : Procedure w := writing I.firstWords blank 0 I.firstCell
noncomputable def table : Procedure w := writing I.productWord blank I.firstProduct (products (F:=F))

/-- The instruction table and its size are independent of the endpoint and D bits.
All table-dependent words come from the actual short bit tape at run time. -/
noncomputable def procedure : Procedure w :=
  (((((I.stage.seq I.pack).seq I.params).seq I.trace).seq I.low).seq I.table)

noncomputable def cost :=
  (6+5*I.sizes.rawCount) + (I.sizes.packedWords*(5*w+6)+6) + (6+5*I.parameters) +
    (4+11*I.X.cells*(2*(FixedTraceProgram.program w).binds+4)) +
    (4+I.firstCell*(2*I.firstWords.binds+4)) +
    (4+(products (F:=F))*(2*I.productWord.binds+4))

end Image
end ThreeFlat.RAM.PhysicalPrelude

end OAI
