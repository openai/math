import OAI.Hierarchy.DescentResetQuantityFunded
import OAI.Hierarchy.DescentResetVenueTailVolume
import OAI.Hierarchy.DescentResetReceiverPitch

namespace OAI
/-! The outgoing reset venue pays for two quantity planes, the compact peer
directory and the change to the genuinely selected successor pitch. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentSIMDLookup DescentVenueQuantityPlanes DescentCompiler
open DescentFallbackPeriod
noncomputable section
set_option quotPrecheck false

def venueArea (h H G Gnext M nextM : ℕ) :=
  1+H+H*chunks G M+H*chunks Gnext nextM+(h+1)^3*2^(h/2)

def venueFactor (v : ResetVenue) (gain : ℕ) :=
  (2*resetPlaneFactor 1*(v.dense.blocks+1)+DescentCompactVenuePeers.compactFactor+v.next.resetFactor)*
    (12*(v.dense.shapes+gain+1))

private theorem chunks_lt {g G M : ℕ} (order : g ≤ G) : chunks g M ≤ chunks G M :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right order _) _)

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "v₀" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "v" => (v₀).venue
local notation "H" => S.hostSize age
local notation "pop" => S.groupCount age
local notation "res" => S.groupCount (age+1)
local notation "M" => 2^e
local notation "N" => 2^k
local notation "gain" => 2^S.hostGain*S.radix
local notation "T" => venueArea h H pop res M nextM

theorem original_venue_bill (reached : age < S.length) (radix : S.radix=2^k)
    (oldHosts : prior.venue.hosts=H) (next : nextM ≤ h/2)
    (bought : ∀x,x∈(v₀).rootUnits ∨ x∈(v₀).receiverUnits → x*M ≤ h/2) :
    (v).fee ≤ venueFactor (v) gain*T := by
  let jobs:=(v).dense.shapes
  let coeff:=12*(jobs+gain+1)
  let precision:=prior.venue.paidBits
  have absolute:(precision*N)*M ≤ h/2:=by
    have raw:=bought (((v₀).funded.precision+(v₀).funded.precision)*(2^(v₀).middle.rootDepth))
      (Or.inl (by simp [rootUnits]))
    change ((precision+precision)*N)*M ≤ h/2 at raw
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right ..))).trans raw
  have origin:precision*M ≤ h/2:=
    (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k))).trans absolute
  have blocks:N*M ≤ h/2:=by
    have raw:=bought (2^(v₀).middle.rootDepth*Nat.clog 2 (2^(v₀).middle.rootDepth+1))
      (Or.inl (by simp [rootUnits]))
    change (N*Nat.clog 2 (N+1))*M ≤ h/2 at raw
    have digits:0 < Nat.clog 2 (N+1):=Nat.clog_pos (by decide) (by have nPos:=Nat.two_pow_pos k;omega)
    exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ digits)).trans raw
  have half:M ≤ h/2:=(Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)).trans blocks
  have full:M ≤ h:=half.trans (Nat.div_le_self ..)
  have signed:DescentSignedCableCodec.width (v).next.degree (v).next.cap*M ≤ h/2:=
    bought _ (Or.inl (by simp [rootUnits]))
  have planes:=(v).quantity_funded h (Nat.two_pow_pos k) (Nat.two_pow_pos e) full full full origin absolute half blocks
  have group:res*N=pop:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits reached radix)).symm
  have rows:chunks res M ≤ chunks pop M:=chunks_lt ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq group)
  have step:S.hostSize (age+1)=H*gain:=by simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have raw:(v).rawHosts=H*jobs:=by
    change prior.venue.hosts*jobs=H*jobs
    rw [oldHosts]
  have one:1 ≤ T:=by unfold venueArea;omega
  have hosts:H ≤ T:=by unfold venueArea;omega
  have cur:H*chunks pop M ≤ T:=by unfold venueArea;omega
  have curNext:H*chunks res M ≤ T:=(Nat.mul_le_mul_left H rows).trans cur
  have tailRows:H*chunks res nextM ≤ T:=by unfold venueArea;omega
  have shared:(h+1)^3*2^(h/2) ≤ T:=by unfold venueArea;omega
  have rawCounts: H*jobs ≤ jobs*T:=by simpa only [Nat.mul_comm H jobs] using Nat.mul_le_mul_left jobs hosts
  have nextCounts:H*gain ≤ gain*T:=by simpa only [Nat.mul_comm H gain] using Nat.mul_le_mul_left gain hosts
  have head₀:(H*jobs)*chunks pop M ≤ jobs*T:=by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left jobs cur
  have head₁:(H*jobs)*chunks res M ≤ jobs*T:=by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left jobs curNext
  have term₀:(H*gain)*chunks res M ≤ gain*T:=by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left gain curNext
  have term₁:(H*gain)*chunks res nextM ≤ gain*T:=by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left gain tailRows
  have charged:(v).quantityRows h ≤ coeff*T:=by
    change 1+(prior.venue.hosts*jobs+S.hostSize (age+1)+(prior.venue.hosts*jobs)*chunks (res*N) M+
      S.hostSize (age+1)*chunks res M+(prior.venue.hosts*jobs)*chunks res M+(h+1)^3*2^(h/2))+
      (v).rawHosts*chunks (res*N) M ≤ _
    rw [oldHosts,step,group,raw]
    dsimp only [coeff]
    nlinarith only [one,rawCounts,nextCounts,head₀,head₁,term₀,shared,Nat.zero_le (jobs*T),Nat.zero_le (gain*T)]
  have compact:1+(v).rawHosts+(v).dense.hosts ≤ coeff*T:=by
    change 1+(v).rawHosts+S.hostSize (age+1) ≤ _
    rw [raw,step]
    dsimp only [coeff]
    nlinarith only [one,rawCounts,nextCounts,Nat.zero_le (gain*T),Nat.zero_le (jobs*T)]
  have tailBill:=(v).next.reset_tariff h M (coeff*T) rfl rfl rfl full signed origin half next
    (by change 1+S.hostSize (age+1)*chunks res M+S.hostSize (age+1)*chunks res nextM ≤ _
        rw [step];dsimp only [coeff];nlinarith only [one,term₀,term₁,Nat.zero_le (jobs*T),Nat.zero_le (gain*T)])
    (by change 1+S.hostSize (age+1)+S.hostSize (age+1)*chunks res nextM ≤ _
        rw [step];dsimp only [coeff];nlinarith only [one,nextCounts,term₁,Nat.zero_le (jobs*T),Nat.zero_le (gain*T)])
    (by
      have smaller: (h+1)^2*2^(h/2) ≤ T:=(Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide : 2 ≤ 3))).trans shared
      exact smaller.trans (Nat.le_mul_of_pos_left _ (by dsimp [coeff];positivity)))
  have rotated:=(DescentCompactVenuePeers.compact_fee (v).rawHosts (v).dense.hosts).trans
    (Nat.mul_le_mul_left _ compact)
  calc
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (planes.trans (Nat.mul_le_mul_left _ charged)) rotated) tailBill
    _ = _ := by dsimp only [venueFactor,coeff,jobs];ring

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
