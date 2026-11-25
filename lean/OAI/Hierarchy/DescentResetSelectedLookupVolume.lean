import OAI.Hierarchy.DescentResetLookupTraffic
import OAI.Hierarchy.DescentResetSelectedRankPrice

namespace OAI
/-! Actual local dimensions of all terminal lookup and candidate-sheet passes at the selected pitch. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSIMDLookup DescentSixParty DescentOperandFamilyBook DescentResetCandidatePair
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "v" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "M" => 2^e
local notation "H" => S.hostSize age
local notation "G₀" => S.groupCount age
local notation "G₁" => S.groupCount (age+1)
local notation "gain" => 2^S.hostGain*S.radix
local notation "area" => receiptArea h H (chunks G₀ M)

theorem selected_lookup_volume (Q : ℕ) (radix : S.radix=2^k) (live : age<S.length)
    (words : ∀t,t∈(v).receiverUnits→t*M≤h/2) :
    (v).sheetLookups (v).receiver.candidates Q≤((v).lookupFactor Q*gain)*area:=by
  let T:=gain*area
  have gp:0<gain:=by rw [radix];positivity
  have up : area≤T:=Nat.le_mul_of_pos_left _ gp
  have split:G₁*2^k=G₀:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits live radix)).symm
  have fewer:chunks G₁ M≤chunks G₀ M:=Nat.div_le_div_right
    (Nat.sub_le_sub_right (Nat.add_le_add_right ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq split) _) _)
  have old:H≤area:=by unfold receiptArea;omega
  have oldRows:H*chunks G₀ M≤area:=by unfold receiptArea;omega
  have half:2^(h/2)≤area:=by
    apply (Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans
    unfold receiptArea
    omega
  have hosts:S.hostSize (age+1)=H*gain:=by simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have nextH:S.hostSize (age+1)≤T:=by simpa [hosts,T,Nat.mul_comm] using Nat.mul_le_mul_left gain old
  have nextRows:S.hostSize (age+1)*chunks G₁ M≤T:=by
    rw [hosts,show H*gain*chunks G₁ M=gain*(H*chunks G₁ M) by ring]
    exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left H fewer).trans oldRows)
  have stock:=half.trans up
  have tables:=(v).setup.table_volume h T stock
    (words _ (by simp [receiverUnits])) (words _ (by simp [receiverUnits]))
    (words _ (by simp [receiverUnits,unit])) (words _ (by simp [receiverUnits]))
    (words _ (by simp [receiverUnits,unit])) (words _ (by simp [receiverUnits,unit]))
  have all_:=(v).lookup_volume h T Q stock nextH nextRows nextRows
    (words _ (by simp [receiverUnits])) (words _ (by simp [receiverUnits])) (words _ (by simp [receiverUnits])) tables
  simpa only [T,Nat.mul_assoc] using all_

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
