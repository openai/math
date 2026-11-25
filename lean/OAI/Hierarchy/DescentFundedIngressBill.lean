import OAI.Hierarchy.DescentFundedIngressTariff
import OAI.Hierarchy.DescentPackedChunkWork
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # Cost of the actual six operations that recover and clip the previous venue -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPackedColony DescentRawCablePanel DescentOrdinaryVenueIngress
open DescentPacking.PackedMatch.Local ProtocolRAM

noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (extra : ℕ)
local notation "c₀" => v.fundedClip extra


def ingressCharge (h ratio : ℕ) :=
  let c:=v.fundedClip extra
  let H:=c.venue.hosts
  let G:=c.venue.groups
  c.factor*ratio*((1+2^(h/2))*h+4*H*h+
    H*G*(v.fundedWorkingUnit extra+4*v.fundedPanelUnit+4*v.area.unit))

/-- The physical owner panel, actor table and clipped venue may all use distinct
pitches. Only the literal lookup allocation is independent of the host census. -/
theorem funded_ingress_bill (oldInputs : Inputs) (base w ratio : ℕ)
    («matching» : 2^v.area.k+1≤ v.area.unit)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤ v.area.unit)
    (wide : 4*v.fundedMaxUnit extra*2^v.area.k≤ v.payload) (bus : w≤ ratio*v.payload) :
    ((v.fundedClip extra).phase oldInputs base w).wordInvoice≤ v.ingressCharge extra v.payload ratio :=by
  let c:=v.fundedClip extra
  let r:=c.radix
  let S:=v.fundedMaxUnit extra
  have rad : 0<r := Nat.two_pow_pos _
  have dpos : 0<v.fundedPanelUnit := by
    have bound:=(v.ticket.installed_donor_widths v.short v.profile).2.2
    change 0<v.ticket.installedDonorWidth v.short v.profile
    omega
  have upos : 0<v.area.unit := paid.trans_le input
  have donorLe : v.fundedPanelUnit≤ S := le_max_left ..
  have oldLe : v.area.unit≤ S := (le_max_left ..).trans (le_max_right ..)
  have newLe : c.unit≤ S := (le_max_right ..).trans (le_max_right ..)
  have room {u : ℕ} (below : u≤ S) : 4*u*r≤ v.payload :=
    (Nat.mul_le_mul_right r (Nat.mul_le_mul_left 4 below)).trans wide
  have atLeast {u : ℕ} (pos : 0<u) (below : u≤ S) : r≤ lanes v.payload u := by
    have w:=room below
    change r≤ v.payload/(2*u)
    apply (Nat.le_div_iff_mul_le (by omega : 0<2*u)).2
    calc r*(2*u) = 2*(u*r) := by ring
         _ ≤ 4*(u*r) := by omega
         _ = 4*u*r := by ring
         _ ≤ _ := w
  have panel : r≤ c.panelPitch := atLeast dpos donorLe
  have actor : r≤ c.actorPitch := atLeast upos oldLe
  have localWide := room newLe
  have working := c.working_pos panel actor localWide
  have post := c.post_pos panel actor localWide
  have occupied {u : ℕ} (pos : 0<u) (below : u≤ S) :
      v.payload≤ lanes v.payload u*(4*u) := by
    have placed := atLeast pos below
    have live : 0<lanes v.payload u := rad.trans_le placed
    have fits : 2*u≤ v.payload := (Nat.div_pos_iff.mp live).2
    exact (occupancy _ _ pos fits).2.trans_eq (by ring)
  have den₀ : v.payload≤ c.panelPitch*(4*v.fundedPanelUnit) := occupied dpos donorLe
  have den₁ : v.payload≤ c.actorPitch*(4*v.area.unit) := occupied upos oldLe
  have funded:=v.funded_bounds extra paid input wide
  let H:=c.venue.hosts
  let G:=c.venue.groups
  let h:=v.payload
  have coreRows:=DescentDatedSeedStartup.chunk_work H G c.working h (v.fundedWorkingUnit extra) funded.fill₁
  have panelRows:=DescentDatedSeedStartup.chunk_work H G c.panelPitch h (4*v.fundedPanelUnit) den₀
  have actorRows:=DescentDatedSeedStartup.chunk_work H G c.actorPitch h (4*v.area.unit) den₁
  have measured:=v.funded_ingress_price extra «matching» oldInputs base w panel actor localWide
  let extent:=(1+2^(h/2))*h+4*H*h+H*G*(v.fundedWorkingUnit extra+4*v.fundedPanelUnit+4*v.area.unit)
  have mass : c.mass*h≤ extent:=by
    change (1+2^(h/2)+H+H*chunks G c.working+H*chunks G c.panelPitch+H*chunks G c.actorPitch)*h≤_
    dsimp only [extent]
    simp only [Nat.add_mul,Nat.mul_add]
    rw [show 4 * H * h = 4 * (H * h) by ring]
    omega
  calc
    _ = Clip.fee (c.phase oldInputs base w)*w:=rfl
    _ ≤ (c.factor*c.mass)*(ratio*h):=Nat.mul_le_mul measured bus
    _ = c.factor*ratio*(c.mass*h):=by ring
    _ ≤ c.factor*ratio*extent:=Nat.mul_le_mul_left _ mass

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
