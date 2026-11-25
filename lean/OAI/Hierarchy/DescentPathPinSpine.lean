import OAI.Hierarchy.DescentOrdinaryPinStep
import OAI.Hierarchy.DescentResetPinStep
import OAI.Hierarchy.DescentPathParticles

namespace OAI
/-! # The exterior binary chart of the chosen ordinary and reset history -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing Catalyst DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts
noncomputable section

variable {F P : Type} [Field F] [Fintype P] {d k tail : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
  {W₀ W₁ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ wire hist : ℕ}
  {first : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist}
  {last : Reached W₁ G q ε S k i₁ z₁ D₁ wire hist}

def resetStep {W : MarkedWorld F d P bits} {i z D n h C f g cut resetTail : ℕ}
    {source : Reached W G q ε S k i z D wire hist}
    {ctl : ResetRates G S k D n h C f g cut resetTail} (b : ClosedReset source ctl)
    (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (owns : ∀pin,source.placement.hub (host source pin)=true) : Step source b.next base radix := by
  have powers : (2:ℕ)^tail=2^resetTail:=base.symm.trans ctl.base
  have eq : tail=resetTail := by simpa only [Nat.log2_two_pow] using congrArg Nat.log2 powers
  subst resetTail
  exact b.pinStep owns

/-- Each actual tape item splits off the k former local coordinates and keeps their order. -/
def Path.frozen (path : Path first last) : ℕ := by
  induction path with
  | here=>exact 0
  | ordinary prev ticket ih=>exact k+ih
  | reset prev b ih=>exact k+ih

/-- The selected execution determines one common invertible map on all original pins.
The remaining digits identify each current host once its original host is known. -/
def Path.pinSpine (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (p : ℕ) (hp : 0<p)
    (a : Archive W₀) (path : Path first last) (r : path.recorded p) (initial : a.Particles first) :
    Spine (active first base radix) (active last base radix) (host first) (host last) path.frozen := by
  induction path with
  | here=>exact Spine.start _ _
  | ordinary prev ticket ih=>
    have owners:=(prev.particles p hp a r initial).attached
    exact (ih r).append (ticket.pinStep base radix owners)
  | reset prev b ih=>
    have owners:=(prev.particles p hp a r.1 initial).attached
    exact (ih r.1).append (resetStep b base radix owners)


theorem Path.previous_host_of_equal (p : ℕ) (hp : 0<p) (a : Archive W₀)
    (path : Path first last) (r : path.recorded p) (initial : a.Particles first)
    {u v : P} (eqn : host last u=host last v) : host first u=host first v := by
  induction path with
  | here=>exact eqn
  | ordinary prev ticket ih=>
    have owners:=(prev.particles p hp a r initial).attached
    exact ih r (ticket.previous_host_of_equal owners eqn)
  | reset prev b ih=>exact ih r.1 (b.previous_host_of_equal eqn)

end
end Hierarchy.DescentSixParty.Chronology

end OAI
