import OAI.Hierarchy.DescentResetReceivedContactScale
import OAI.Hierarchy.DescentResetStemFunded
import OAI.Hierarchy.DescentResetEvidenceScale
import OAI.Hierarchy.DescentResetReceivedTariff

namespace OAI
/-! All five sections of a genuine actor-to-trunk receipt use the same clipped
root batch. Their cost is linear in the old roster and its packed rows, plus one
shared lookup-table allowance. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentSixParty DescentCompiler
open ThreeFlat.Routing
noncomputable section
set_option quotPrecheck false

def receiptArea (h H rows : ℕ) := H+H*rows+(h+1)^3*2^(h/2)

def receiptFactor (v : ResetOutput) (gain U : ℕ) :=
  v.front.evidenceTrafficFactor U*(v.front.peer.shapes+1) + 2*v.contactFactor U+
  CandidateFront.stemCoefficient v.front.peer.oldDegree v.front.oldTicketCount v.front.blocks v.front.signedQueries
    v.front.peer.shapes U U*(4+2*gain)+
  (4+gain*(2*(8*U+10)+4)+7*(11+4*(8*U+10)))

private theorem chunks_mono {a b M : ℕ} (hle : a ≤ b) : chunks a M ≤ chunks b M :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right hle _) _)

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "V" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "v" => (V).front
local notation "P" => S.hostSize age
local notation "O" => S.groupCount age
local notation "M" => 2^e
local notation "growth" => 2^S.hostGain*S.radix
local notation "T" => receiptArea h P (chunks O M)

theorem received_volume (start U : ℕ) (dyadic : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (reached : age < S.length) (hp : 0 < P)
    (lookup : ∀x,x∈(V).rootUnits ∨ x∈(V).receiverUnits→x*(V).receiver.lanes ≤ h/2) :
    (v).receivedBill start U ≤ (V).receiptFactor growth U*T := by
  have group:=S.group_power dyadic radix age
  have split:S.groupCount (age+1)*2^k=O:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits reached radix)).symm
  have fewer:chunks (S.groupCount (age+1)) M ≤ chunks O M :=
    chunks_mono ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq split)
  have costRows:=Nat.mul_le_mul_left P fewer
  have next:S.hostSize (age+1)=P*growth:=by simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have rows:P*chunks O M ≤ T:=by unfold receiptArea;omega
  have hosts:P ≤ T:=by unfold receiptArea;omega
  have tables:2^(h/2) ≤ (h+1)^3*2^(h/2):=Nat.le_mul_of_pos_left _ (by positivity)
  have paid:(h+1)^3*2^(h/2) ≤ T:=by unfold receiptArea;omega
  have half:=tables.trans paid
  have one:1 ≤ T:=(Nat.two_pow_pos _).trans_le half
  have previous: S.hostSize (age+1) ≤ growth*T:=by rw [next,Nat.mul_comm P];exact Nat.mul_le_mul_left _ hosts
  have nextRows:S.hostSize (age+1)*chunks (S.groupCount (age+1)) M ≤ growth*T:=by
    rw [next,show (P*growth)*chunks (S.groupCount (age+1)) M=growth*(P*chunks (S.groupCount (age+1)) M) by ring]
    exact Nat.mul_le_mul_left _ (costRows.trans rows)
  have large:T ≤ ((v).peer.shapes+1)*T:=Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have target:(v).peer.hosts*chunks (S.groupCount (age+1)) M ≤ ((v).peer.shapes+1)*T:=by
    change (P*(v).peer.shapes)*_ ≤ _
    rw [show P*(v).peer.shapes*chunks _ M=(v).peer.shapes*(P*chunks (S.groupCount (age+1)) M) by ring]
    exact Nat.mul_le_mul (Nat.le_succ _) (costRows.trans rows)
  have small:=(V).evidence_keys rfl rfl rfl h (fun x hx=>lookup _ (Or.inl hx))
  have oldRow:P*chunks (2^S.groupWidth k tail age) M ≤ ((v).peer.shapes+1)*T:=by rw [group];exact rows.trans large
  have early:=(v).evidence_scale start U h (((v).peer.shapes+1)*T) hp (hosts.trans large)
    oldRow oldRow target (half.trans large) small.1 small.2.1 small.2.2.1 small.2.2.2.1 small.2.2.2.2
  have contact:=(V).contact_work h start U (Nat.two_pow_pos e) rfl rfl rfl
    (fun x hx=>lookup _ (Or.inl hx))
  have cArea:(V).contactArea h≤2*T:=by
    change 1+(P+P*chunks (2^S.groupWidth k tail age) M)+2^(h/2) ≤ _
    rw [group]
    unfold receiptArea
    have available:0 < (h+1)^3*2^(h/2):=by positivity
    omega
  have c:=contact.trans (Nat.mul_le_mul_left _ cArea)
  have stem:=bought_stem_bill_at G S board k tail age p f g drift degree h e prev nextM C packet prior base U U lookup
  have sArea: CandidateFront.stemEnvelope h P (S.hostSize (age+1)) (S.groupCount (age+1)) (2^k) M M ≤
      (4+2*growth)*T:=by
    unfold CandidateFront.stemEnvelope
    rw [split]
    have priorRows:=costRows.trans rows
    nlinarith only [hosts,previous,rows,nextRows,priorRows,paid]
  have st:=stem.trans (Nat.mul_le_mul_left _ sArea)
  let sc:=8*U+10
  have scan:4+(v).newHosts*(2*sc+4)+7*(11+4*sc) ≤ (4+growth*(2*sc+4)+7*(11+4*sc))*T:=by
    have left:=Nat.mul_le_mul_right (2*sc+4) previous
    have right:=Nat.le_mul_of_pos_right (4+7*(11+4*sc)) one
    change 4+S.hostSize (age+1)*(2*sc+4)+7*(11+4*sc) ≤ _
    nlinarith only [left,right]
  unfold CandidateFront.receivedBill
  dsimp only
  unfold receiptFactor
  unfold contactWork at c
  dsimp only at c
  dsimp only [sc] at scan
  nlinarith only [early,c,st,scan]

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
