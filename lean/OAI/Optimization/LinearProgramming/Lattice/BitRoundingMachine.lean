import OAI.Optimization.LinearProgramming.Lattice.BitRoundControl
import OAI.Optimization.LinearProgramming.Lattice.BitRoundingKernels

/-! The single physical sign-rounding machine, with its literal projection,
integer LLL, and signed radix procedures in the transition table. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

open OracleSpec

noncomputable def actualKernelCode : KernelCode actualKernels where
  projection := Selector.integralRowsListP.comp Projector.projectorP
  selector := Selector.selectP
  assemble := Horner.assembleWordP

/-- A single finite transition table independent of both rank and radius. -/
noncomputable def roundingMachine : BitProgram := WordDialogue.machine (dispatchP actualKernelCode)

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
