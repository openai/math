import OAI.Hierarchy.ProbeFixedWideSignedRow
import OAI.Hierarchy.ProbeFixedWideSignedPartyTariff

namespace OAI
/-! # The complete native selector, spill gather and signed party bank at an original date -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ThreeFlat Routing
open Tagged Tagged.WideControlJoin Tagged.WideStack AdaptiveProbe ProbeStage Probe
open WireTelescope WireTelescope.PassMatrix WireTelescope.PassMatrix.PartyPins
open WideCPU Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => v.widePacketDegree
def signedTagCeiling := Nat.log 2 (v.signedPartyCountCap+1)+1

theorem signed_tag_digits (h : ℕ) (a : Attempt) :
    let n:=v.signedPartyCount h a
    n+1≤ 2^Nat.clog 2 (n+1) ∧ Nat.clog 2 (n+1)≤ v.signedTagCeiling ∧
      Nat.log 2 (n+1)+1≤ v.signedTagCeiling := by
  intro n
  have countBound : n+1≤ v.signedPartyCountCap+1:=Nat.succ_le_succ (v.signed_party_count_bound h a)
  have b : Nat.log 2 (n+1)+1≤ v.signedTagCeiling:=Nat.succ_le_succ (Nat.log_mono_right (b:=2) countBound)
  exact ⟨Nat.le_pow_clog (by decide : 1<2) _,((Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    (Nat.lt_pow_succ_log_self (by decide) (n+1)).le).trans b,b⟩

private def gatherRate (degree : ℕ) := 266*degree+4616*degree*degree

private theorem gather_cost (degree e : ℕ) :
    let cap:=2^e
    degree*cap+degree*(cap*(200*e+65))+degree*degree*(2308*cap*(cap.log2+2))≤
      gatherRate degree*(cap*(e+1)) := by
  intro cap
  simp only [cap,Nat.log2_two_pow,gatherRate]
  ring_nf
  omega

theorem signedRow_tariff (unitCost : ℕ) :
    ∃P K:ℕ,0<K ∧ ∀ {Ex Se Data:Type} [Fintype Ex] [Fintype Se] [Fintype Data]
      (h w : ℕ) (a : Attempt) (_hw : 0<w) (G : Gate) {T : ℕ} (g : Dated T) (base : ℕ) (j : Fin T) (i : Fin g.sites)
      (words : Bool→Fin D→Fin (v.wideNeighborCap w unitCost)→SitePins Ex Se Data G⊕Bool)
      (inside : ∀f:SiteControls.Field D,controlAddress g base j i f<G.u)
      (mode : ballotAddress g base j i 0<G.u) {tagBits:ℕ} (_bounded : tagBits≤ v.signedTagCeiling)
      (fits : v.signedPartyCount h a+1≤ 2^tagBits) (tags : tagBits≤ G.W+1)
      (refs : v.wideNeighborDigits w unitCost≤ G.W+1),
      let net:=v.signedRow h w unitCost a G g base j i words inside mode fits tags refs
      net.cells+net.internal≤ P*(w+1)*(Nat.log 2 (K*w+1)+2)^3 := by
  obtain ⟨R,J,jpos,bank⟩:=v.signed_party_bank_tariff unitCost
  obtain ⟨H,hpos,room⟩:=v.signed_party_dimensions unitCost
  let K:=max J H
  let B:=gatherRate D*K
  let C:=B+177^v.signedTagCeiling*(v.signedPartyCountCap*(2*B)+R)
  refine ⟨C,K,jpos.trans_le (le_max_left ..),?_⟩
  intro Ex Se Data exf sef dataf h w a _hw G T g base j i words inside mode tagBits _bounded fits tags refs net
  let e:=v.wideNeighborDigits w unitCost
  let cap:=v.wideNeighborCap w unitCost
  let gate:=fun atom=>v.signedParty h w a cap (v.partyRoleBits h) (v.partyLaneBits h w a unitCost)
    v.partyKeyBits (ballotWord (Ex:=Ex) (Sel:=Se) («D»:=Data) G g base j i) atom
  let gathered:=D*cap+D*(cap*(200*e+65))+D*D*(2308*cap*(cap.log2+2))
  let vol:=(w+1)*(PacketScale.digits (K*w))^3
  have bill:=v.signedRow_fee h w unitCost a G g base j i words inside mode fits tags refs
  change net.cells+net.internal≤ D*D*(2308*cap*(cap.log2+2))+
    177^tagBits*∑atom,(2*gathered+((gate atom).cells+(gate atom).internal)) at bill
  have capRoom : 2^e≤ K*w:=(v.party_lane_room h w a unitCost).1.le.trans
    ((room h w a _hw).1.trans (Nat.mul_le_mul_right w (le_max_right ..)))
  have amount : gathered≤ B*vol:=(gather_cost D e).trans
    ((Nat.mul_le_mul_left (gatherRate D) (lane_volume capRoom)).trans_eq (by dsimp only [vol,B];ring))
  have charge : D*D*(2308*cap*(cap.log2+2))≤ B*vol:=
    (Nat.le_add_left _ _).trans amount
  have mono : PacketScale.digits (J*w)≤ PacketScale.digits (K*w):=
    Nat.add_le_add_right (Nat.log_mono_right (b:=2) (Nat.succ_le_succ (Nat.mul_le_mul_right w (le_max_left ..)))) 2
  have gates : (∑ atom, ((gate atom).cells + (gate atom).internal))≤ R*vol := by
    have raw:=bank h w a _hw cap (ballotWord (Ex:=Ex) (Sel:=Se) («D»:=Data) G g base j i)
    exact raw.trans ((Nat.mul_le_mul_left (R*(w+1)) (Nat.pow_le_pow_left mono 3)).trans_eq (Nat.mul_assoc _ _ _))
  have total : (∑atom,(2*gathered+((gate atom).cells+(gate atom).internal)))≤
      (v.signedPartyCountCap*(2*B)+R)*vol := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have copies:=Nat.mul_le_mul (v.signed_party_count_bound h a) (Nat.mul_le_mul_left 2 amount)
    simpa only [Nat.cast_id,Nat.add_mul,Nat.mul_assoc] using Nat.add_le_add copies gates
  have scaled:=Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<177) _bounded) total
  simpa only [C,vol,PacketScale.digits,Nat.add_mul,Nat.mul_assoc] using bill.trans (Nat.add_le_add charge scaled)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
