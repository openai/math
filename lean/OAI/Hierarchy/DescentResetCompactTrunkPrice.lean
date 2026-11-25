import OAI.Hierarchy.DescentResetReceivedVolume
import OAI.Hierarchy.DescentPhysicalTrunkCost
import OAI.Hierarchy.DescentResetClippedDatePrice

namespace OAI
/-! The received directory is followed by three physical compact trunk tables.
Their heads and indexed reads use the selected receiver batch. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentCompiler TerminalScale DescentSixParty DescentSIMDLookup
noncomputable section
set_option quotPrecheck false

def CandidateFront.compactTrunkWords (v : CandidateFront) :=
  let n:=v.newHosts*chunks v.peer.groups v.peer.lanes
  let pages:=3*2^(DescentResetTrunkIssue.width v.metaBits v.peer.lanes)
  (46+108*v.newHosts+124*n+10*pages)+7*(15*(2*v.newHosts+4*n+4)+350+15*(pages+1))

namespace ResetOutput
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "v" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "H" => S.hostSize age
local notation "M" => 2^e
local notation "growth" => 2^S.hostGain*S.radix

theorem compact_trunk_volume (rate : ℕ) (live : age < S.length) (radix : S.radix=2^k)
    (bought : ∀x,x∈(v).receiverUnits → x*M ≤ h/2) (gain : growth ≤ scale S.height rate) :
    (v).front.compactTrunkWords ≤ (32768*scale S.height rate)*
      (H+H*chunks (S.groupCount age) M+2^(h/2)) := by
  let a:=(v).front
  let P:=scale S.height rate
  have word:10*a.metaBits*M ≤ h/2:=by
    have bound:=bought ((v).sheets.metaBits*10) (by simp [receiverUnits])
    change a.metaBits*10*M ≤ h/2 at bound
    simpa only [Nat.mul_comm 10 a.metaBits] using bound
  have key:DescentResetTrunkIssue.width a.metaBits a.peer.lanes ≤ h/2:=by
    change (a.metaBits*7+a.metaBits)*M ≤ h/2
    exact (Nat.mul_le_mul_right _ (by omega : a.metaBits*7+a.metaBits ≤ 10*a.metaBits)).trans word
  have page:=Nat.pow_le_pow_right (by decide : 0 < 2) key
  have split:S.groupCount (age+1)*2^k=S.groupCount age:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits live radix)).symm
  have fewer:S.groupCount (age+1) ≤ S.groupCount age:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans_eq split
  have rows : chunks (S.groupCount (age+1)) M ≤ chunks (S.groupCount age) M :=
    Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right fewer _) _)
  have step:a.newHosts=H*growth:=by
    change S.hostSize (age+1)=_
    simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have hosts:a.newHosts ≤ H*P:=step.trans_le (Nat.mul_le_mul_left _ gain)
  have scans:a.newHosts*chunks a.peer.groups a.peer.lanes ≤ (H*chunks (S.groupCount age) M)*P:=by
    change a.newHosts*chunks (S.groupCount (age+1)) M ≤ _
    exact (Nat.mul_le_mul hosts rows).trans_eq (by ring)
  have half:1 ≤ 2^(h/2):=Nat.two_pow_pos _
  have common:2^(h/2) ≤ P*2^(h/2):=Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  change a.compactTrunkWords ≤ (32768*P)*_
  dsimp only [CandidateFront.compactTrunkWords]
  nlinarith only [hosts,scans,page,half,common]

end ResetOutput
end
end Hierarchy.DescentDatedAddressBook

end OAI
