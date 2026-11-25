import OAI.Hierarchy.DescentResetCanvasIngressRate
import OAI.Hierarchy.DescentDatedCanvasRate
import OAI.Hierarchy.DescentDatedResetOutput

namespace OAI
/-! # One actual reset from the acquired prior token and neighbor tensors to the final output catalogue -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty.PackedFlow.Canvas DescentPackedFlowPublication DescentSIMDLookup ProtocolRAM Filter
noncomputable section

structure PhysicalReset where
  k : ℕ
  c : ℕ
  previousToken : Setup.Tokens k c
  previousRoster : Bank
  ingress : DescentResetCanvasIngress.Layout
  hosts : ℕ
  ports : ℕ
  high : ℕ
  low : ℕ
  bits : ℕ
  short : ℕ
  lanes : ℕ
  depthCut : ℕ
  fullBudget : ℕ
  classBound : ℕ
  grain : ℕ
  positive : 0<bits
  gain : ℕ
  payload : ℕ
  field : ℕ
  groups : ℕ
  re : ℕ
  e : ℕ
  successor : ResetOutput

namespace PhysicalReset
variable (a : PhysicalReset)
def stageStart (base : ℕ) := a.ingress.endAddress base
def chart (base : ℕ) :=Setup.plan a.previousToken a.previousRoster a.hosts a.ports a.high a.low a.bits
  a.short a.lanes base a.depthCut a.fullBudget a.classBound a.grain
def rebased (base : ℕ) := (a.chart base).repackedEnd a.payload a.gain a.positive
  a.field a.groups (2^a.re) (2^a.e)
def endAddress (base : ℕ) := a.successor.metadataEnd (a.rebased base)

def fullEnd (base : ℕ) := a.endAddress (a.stageStart base)

theorem occupied (base : ℕ) : base≤(a.chart base).endAddress ∧
    (a.chart base).endAddress≤a.rebased base ∧ a.rebased base≤a.endAddress base := by
  have initial:=Setup.extent a.previousToken a.previousRoster a.hosts a.ports a.high a.low a.bits
    a.short a.lanes base a.depthCut a.fullBudget a.classBound a.grain
  change (a.chart base).endAddress=_ at initial
  have rng:=(a.chart base).estimator_range a.payload a.gain a.positive
  change (a.chart base).endAddress≤_ ∧ _≤_ ∧ _≤(a.chart base).remixEnd a.payload a.gain a.positive at rng
  have remixBound :=(rng.1.trans rng.2.1).trans rng.2.2
  have last:=a.successor.metadataTranslated (a.rebased base)
  refine ⟨by omega,?_,by unfold endAddress;omega⟩
  unfold rebased Placement.repackedEnd Placement.rotationEnd Subwords.finish Subwords.destination
  dsimp only
  omega

variable {ι : ℕ→Type*} (s : ∀h,ι h→PhysicalReset) (base : ∀h,ι h→ℕ)
theorem actual_increment
    (control : Placement.ScalarRoom (fun h i=>(s h i).chart (base h i)) (fun h i=>(s h i).payload) (fun h i=>(s h i).gain))
    (radix : Bounded (fun h i=>2^(s h i).k)) (axes : Bounded (fun h i=>2^((s h i).high+(s h i).low)))
    (book : ∀ᶠ h:ℕ in atTop,∀i,let v:=s h i;Book.width v.bits (2^v.k) v.short*v.lanes≤v.payload)
    (groups : Bounded (fun h i=>(s h i).groups)) (lanes : Bounded (fun h i=>2^(s h i).e))
    (dictionary : ∀ᶠ h:ℕ in atTop,∀i,let v:=s h i;v.re+v.field*(2^v.re*2^v.e)≤v.payload/2)
    (published : Bounded (fun h i=>(s h i).successor.metadataEnd 0)) :
    Bounded (fun h i=>(s h i).endAddress (base h i)-base h i) := by
  have pre (h : ℕ) (i : ι h) :=Setup.footprint (s h i).previousToken (s h i).previousRoster
    (s h i).hosts (s h i).ports (s h i).high (s h i).low (s h i).bits (s h i).short (s h i).lanes
    (base h i) (s h i).depthCut (s h i).fullBudget (s h i).classBound (s h i).grain
  have ready:=Setup.whole_repacked_rate (p:=fun h i=>(s h i).chart (base h i))
    (fun h i=>(s h i).payload) (fun h i=>(s h i).gain) (fun h i=>(s h i).positive) control
    (fun h i=>(s h i).field) (fun h i=>(s h i).groups) (fun h i=>(s h i).re) (fun h i=>(s h i).e)
    groups lanes dictionary base (fun h i=>(s h i).short) (fun h i=>(s h i).lanes) (fun h i=>(s h i).k)
    pre radix axes book
  apply (ready.add published).of_le
  intro h i
  change (s h i).endAddress (base h i)-base h i≤(s h i).rebased (base h i)-base h i+_
  rw [endAddress,(s h i).successor.metadataTranslated]
  omega

end PhysicalReset
end
end Hierarchy.DescentDatedAddressBook

end OAI
