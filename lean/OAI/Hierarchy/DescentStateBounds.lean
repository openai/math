import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentGroupStageData

namespace OAI
/-! # Inductive bounds on a physically grouped ordinary stage -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {price ε : ℝ} {J V : Type}
  [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G price ε J V k) (S : AtomSchedule) (i : ℕ)

/-- Reusable inductive statements about the actual stage. The only graph
information listed here is the true site count and the common divisor of its cables. -/
structure StateBounds : Prop where
  coordinates : Function.Injective (fun u=>(A.pos u,A.block u))
  host : Fintype.card V≤S.hostSize i
  capacity : A.cap≤2^(8+S.capGain*i)
  bundleCapacity : A.cap≤2^(8+(S.capGain-(G.b+3))*i)
  history : S.Within i (∑v,(A.records v).length)
  atom : 0<A.hist
  valuation : price=1/((A.hist:ℝ)*(S.epochPower:ℝ)^S.priceExponent)
  paidUnit : price*((A.wire*(A.z*G.b):ℕ):ℝ)≤1
  divides : ∀e,A.z*G.b∣W.graph.width e

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
