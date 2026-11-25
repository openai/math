import OAI.Hierarchy.DescentNamedStencilRoom
import OAI.Hierarchy.DescentPhysicalRootSpectra

namespace OAI
/-! The old count, neighbor roster, hub flags and estimator columns fit the reset stencil's operand chart. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentPlainTerminal.Suffix DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false

variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y w : ℕ)
local notation "start" => a.stageStart floor
local notation "P" => a.stencilPhase sh start count hub g Y

theorem stencil_operand_geometry {src : Bank} {R δ : ℕ}
    (prime : a.PrimeRoom start src count R δ w) (hubFit : hub.Fits w floor)
    (degree : (P).S.degree=a.ports) (roof : a.fullEnd floor<2^w) :
    StencilBook.Geometry (P).S (P).X (P).base (P).bank w := by
  have endFit := (a.stencil_end_before_full sh floor count hub g Y).trans_lt roof
  have safe := ((P).S.header_before_output (P).base).trans_lt endFit
  obtain ⟨a₁,a₂,a₃⟩ := a.ingress.order floor
  have first : floor≤ start := a₁.trans (a₂.trans a₃)
  have issued := a.occupied start
  have inter : start≤(P).base := by
    rw [a.stencil_start sh start count hub g Y]
    exact issued.1.trans issued.2.1
  have initial : (P).first≤(P).base := by
    unfold DescentSixParty.PackedFlow.ResetMiddle.base Subwords.finish Subwords.destination
    omega
  have previously := a.root_spectra_before sh start count hub g Y prime.fit (P).base initial
  have atBase : (P).base<2^w := by
    have lower := (P).S.translated 0 (P).base
    simp only [Nat.zero_add] at lower
    change (P).S.endAddress (P).base<2^w at endFit
    omega
  have bankFit (b : Bank) (bound : b.base+b.size≤ start) : b.Fits w (P).base :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((bound.trans inter).trans_lt atBase),
      bound.trans inter⟩
  have hubRoom : hub.Fits w (P).base := ⟨hubFit.1,hubFit.2.1,hubFit.2.2.trans (first.trans inter)⟩
  refine ⟨⟨⟨bankFit count prime.countLow,trivial⟩,previously.1,hubRoom,previously.2,
    bankFit a.previousRoster prime.oldRoster⟩,?_,?_,safe⟩
  · change (P).S.hosts*(P).S.degree≤a.previousRoster.size
    have hosts : (P).S.hosts = a.hosts := sh.hosts
    rw [hosts, degree]
    exact prime.slots
  · change (P).bank+((1+(P).S.maxPorts)+(P).S.m)*((P).S.hosts*chunks (2^(P).S.c) (P).S.M)≤
      (P).bank+(((1+(P).S.maxPorts)+(P).S.m)*(P).S.hosts)*chunks (2^(P).S.c) (P).S.M
    rw [Nat.mul_assoc]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
