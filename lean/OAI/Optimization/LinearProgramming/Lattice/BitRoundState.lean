import OAI.Optimization.LinearProgramming.Lattice.BitProbe
import OAI.Optimization.LinearProgramming.Lattice.BitDriverWire

/-! Finite state and transitions of the repeated-direction rounding controller. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
open OracleSpec

abbrev Env := (Input × ℕ) × IntMatrix
abbrev Carry := Env × Probe.Carry
abbrev Action := Word ⊕ (Word × Carry)

def packedEnv {p : ℕ} (M fuel : ℕ) (old : List (Fin p → ℤ)) : Env :=
  (((p,M),fuel),old.map List.ofFn)

structure Kernels where
  projection : ℕ × IntMatrix → IntMatrix
  selector : ℕ × List ℚ → ℕ × Row
  assemble : (ℕ × ℕ) × IntMatrix → Row

def finish (f : Kernels) (e : Env) : Action :=
  .inl (signPacket (f.assemble ((e.1.1.1,radixWidth e.1.1.1 e.1.1.2),e.2)))

def forward (e : Env) (query : Row × Probe.Carry) : Action :=
  .inr (signPacket query.1,(e,query.2))

def requestOf : Probe.Action → Row × Probe.Carry
  | .inl _ => ([],default)
  | .inr q => q

theorem start_request (x : Probe.Params) : Probe.start x = .inr (requestOf (Probe.start x)) := by
  unfold Probe.start Probe.nextMax
  split <;> rfl

def probeParams (f : Kernels) (e : Env) : Probe.Params :=
  ((e.1.1.1,searchPrecision e.1.1.1 e.1.1.2),f.projection (e.1.1.1,e.2))

def stage (f : Kernels) (e : Env) : Action :=
  if e.1.2 = 0 then finish f e
  else forward e (requestOf (Probe.start (probeParams f e)))

def receiveProbe (f : Kernels) (e : Env) : Probe.Action → Action
  | .inr q => forward e q
  | .inl (nonzero,values) =>
    if nonzero then stage f ((e.1.1,e.1.2-1),(f.selector (e.1.1.2,values)).2 :: e.2)
    else finish f e

def dispatch (f : Kernels) : Input ⊕ (Word × Carry) → Action
  | .inl x => stage f ((x,x.1),[])
  | .inr (w,e,c) => receiveProbe f e (Probe.advance (nonnegativeAnswer w) c)

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
