import OAI.Hierarchy.DescentScheduledResetAtPorts
import OAI.Hierarchy.DescentPriorNodePresenceRate
import OAI.Hierarchy.DescentResetHostPadPrice

namespace OAI
/-! Uniform address width of the previous-register alignment and all-node presence pages. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook Filter
noncomputable section
variable {ι : ℕ→Type*}

theorem prior_padding_offset (v : DatePorts) (k base : ℕ) :
    v.priorStart k base-base=v.priorStart k 0:=by
  unfold priorStart
  rw [(v.presence k).translated ((v.resetPad k).endAddress base),(v.resetPad k).translated base,
    (v.presence k).translated ((v.resetPad k).endAddress 0)]
  omega

theorem prior_padding_rate (v : ∀h,ι h→DatePorts) (k : ∀h,ι h→ℕ)
    (raw : DescentResetPriorHostPad.Shape.ScalarRoom (fun h i=>(v h i).resetPad (k h i)))
    (pages : DescentPriorNodePresence.Chart.ScalarRoom (fun h i=>(v h i).presence (k h i))) :
    Bounded (fun h i=>(v h i).priorStart (k h i) 0):=
  DescentPriorNodePresence.Chart.rate _ pages _ (DescentResetPriorHostPad.Shape.extent_rate _ raw)

structure PriorPaddingAperture (C h : ℕ) (p : DatePorts) (k : ℕ) : Prop where
  hosts : p.venue.hosts≤2^(C*h)
  groups : p.venue.groups≤2^(C*h)
  args : p.argumentsPerNode≤2^(C*h)
  blocks : 2^k≤2^(C*h)
  operand : p.operandLanes≤2^(C*h)
  role : p.roleLanes≤2^(C*h)
  tokens : p.tokenBits*p.nodes*p.roleLanes≤C*h
  packedMask : p.nodes*p.roleLanes≤C*h
  expanded : p.nodes*p.operandLanes≤C*h

/-- The same exponent applies to all calendars, archives and initial addresses. -/
theorem uniform_prior_padding (C : ℕ) :
    ∃K : ℕ,∀ᶠ h : ℕ in atTop,∀(p : DatePorts) (k base : ℕ), PriorPaddingAperture C h p k →
      p.priorStart k base-base≤2^(K*h):=by
  let idx (h : ℕ) := {q : DatePorts×ℕ // PriorPaddingAperture C h q.1 q.2}
  let p:=fun h (i : idx h)=>i.val.1
  let k:=fun h (i : idx h)=>i.val.2
  have scalar (f : ∀h,idx h→ℕ) (fits : ∀h i,f h i≤2^(C*h)) : Bounded f:=
    ⟨C,Eventually.of_forall fits⟩
  have linear (f : ∀h,idx h→ℕ) (fits : ∀h i,f h i≤C*h) : DescentPriorNodePresence.Chart.Linear f:=
    ⟨C,Eventually.of_forall fits⟩
  have raw : DescentResetPriorHostPad.Shape.ScalarRoom (fun h i=>(p h i).resetPad (k h i)):=
    ⟨scalar _ (fun h i=>i.property.hosts),scalar _ (fun h i=>i.property.groups),
      scalar _ (fun h i=>i.property.args),scalar _ (fun h i=>i.property.blocks),
      scalar _ (fun h i=>i.property.operand),scalar _ (fun h i=>i.property.role)⟩
  have pages : DescentPriorNodePresence.Chart.ScalarRoom (fun h i=>(p h i).presence (k h i)):=
    ⟨raw.hosts,raw.groups,raw.blocks,raw.rolePitch,raw.dataPitch,
      linear _ (fun h i=>i.property.tokens),linear _ (fun h i=>i.property.packedMask),
      linear _ (fun h i=>i.property.expanded)⟩
  obtain ⟨K,large⟩:=prior_padding_rate p k raw pages
  refine ⟨K,large.mono ?_⟩
  intro h room p₀ k₀ base aperture
  rw [prior_padding_offset]
  exact room ⟨(p₀,k₀),aperture⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
