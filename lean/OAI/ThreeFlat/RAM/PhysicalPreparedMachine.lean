import OAI.ThreeFlat.RAM.PhysicalPrelude
import OAI.ThreeFlat.RAM.PhysicalProcedureLink
import OAI.ThreeFlat.RAM.PhysicalProgramValue

namespace OAI
/-! # The H evaluator starting from the actual paired external memory -/

namespace ThreeFlat.RAM.PhysicalPinsExpr.Program

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPrelude BitLayout Diagonal Diagonal.TraceAddressRecord Contraction
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [Field F] {w q t shared b : ℕ}
variable (s : Shape) [NeZero s.period] (G : BitNetwork F q)
variable (input : Fin t → Fin q → BitSource shared (s.area+2*s.halfBits))
variable (keys : Fin q → Record) (params : Fin s.parameterBits → Bool)

noncomputable abbrev sourceNetwork := PhysicalTraceSource.expanded G input

noncomputable def inputImage (fit : Fits (H s (sourceNetwork s G input) params) w) : Image F w where
  advice := s.advice
  endpointBits := s.halfBits+s.halfBits
  auxBits := s.bits
  parameters := s.parameterBits
  ports := q
  rows := t
  shared := shared
  exposed := s.area+2*s.halfBits
  H := H s (sourceNetwork s G input) params
  G := G
  input := input
  keys := keys
  field := codec (H s (sourceNetwork s G input) params) fit

/-- Only two external descriptor bases must be selected to match the source layout. -/
noncomputable abbrev locate (N : BitNetwork F (s.area+2*s.halfBits)) :=
  let stop := footprint (H s N params)
  {s with parameterBase:=stop,templateBase:=stop+s.parameterBits}

theorem located_H (N : BitNetwork F (s.area+2*s.halfBits)) :
    H (locate s params N) N params = H s N params := rfl

/-- Placing the source right after the contraction footprint gives both address
equalities required by the value theorem, without changing the evaluated network. -/
theorem located_bases (fit : Fits (H s (sourceNetwork s G input) params) w) :
    let s' := locate s params (sourceNetwork s G input)
    let I := inputImage s' G input keys params fit
    s'.parameterBase=I.sizes.parameterBase ∧ s'.templateBase=I.sizes.templateBase :=
  ⟨rfl,rfl⟩

noncomputable abbrev prepared (fit : Fits (H s (sourceNetwork s G input) params) w) :=
  (inputImage s G input keys params fit).procedure.link (native s (sourceNetwork s G input) params fit)

noncomputable abbrev preCost (fit : Fits (H s (sourceNetwork s G input) params) w) :=
  (4+(10+(program w).binds)+1)+(inputImage s G input keys params fit).cost

end ThreeFlat.RAM.PhysicalPinsExpr.Program

end OAI
