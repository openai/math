import OAI.Hierarchy.DescentPrimitiveVolumeTariff
import OAI.Hierarchy.DescentResetReceivedVolume

namespace OAI
/-! # Primitive-role traffic in the original reset actor calendar -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSIMDLookup DescentSixParty DescentPlacedInvoiceVolume
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "V" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "z" => (V).birth
local notation "q" => (V).primitive
local notation "M" => 2^e
local notation "H" => S.hostSize age
local notation "O" => S.groupCount age
local notation "growth" => 2^S.hostGain*S.radix
local notation "area" => receiptArea h H (chunks O M)

def primitiveFactor (a : ResetOutput) (increase U : ℕ) :=
  (birthFactor a.birth+finalFactor a.primitive.chart.nodes a.primitive.chart.blocks U)*(increase+1)

theorem primitive_volume (U : ℕ) (radix : S.radix=2^k) (reached : age<S.length)
    (lookup : ∀t,t∈(V).rootUnits ∨ t∈(V).receiverUnits→t*(V).receiver.lanes≤h/2) :
    (z).invoice+((q).clockBound U+7*(q).nameBound U)≤(V).primitiveFactor growth U*area:=by
  let T:=growth*area
  have gp:0<growth:=by rw [radix];positivity
  have split:S.groupCount (age+1)*2^k=O:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits reached radix)).symm
  have fewer:chunks (S.groupCount (age+1)) M≤chunks O M:=Nat.div_le_div_right
    (Nat.sub_le_sub_right (Nat.add_le_add_right ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq split) _) _)
  have next:S.hostSize (age+1)=H*growth:=by simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have up:area≤T:=Nat.le_mul_of_pos_left _ gp
  have oldH:H≤area:=by unfold receiptArea;omega
  have oldR:H*chunks O M≤area:=by unfold receiptArea;omega
  have newR:S.hostSize (age+1)*chunks (S.groupCount (age+1)) M≤T:=by
    rw [next,show (H*growth)*chunks (S.groupCount (age+1)) M=growth*(H*chunks (S.groupCount (age+1)) M) by ring]
    exact Nat.mul_le_mul_left growth ((Nat.mul_le_mul_left H fewer).trans oldR)
  have book:(h+1)^3*2^(h/2)≤area:=by unfold receiptArea;omega
  have positive:1≤2^(h/2):=Nat.two_pow_pos _
  have one:1≤area:=positive.trans ((Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans book)
  have born:0<(z).rootBits:=by change 0<n*2^n+n+3;omega
  have spec:((z).rootBits*(V).sheets.blocks)*M≤h/2:=lookup _ (Or.inr (by simp [receiverUnits]))
  have pb:0<(V).sheets.blocks:=Nat.two_pow_pos k
  have bit:(z).rootBits*M≤h/2:=(Nat.mul_le_mul_right M (Nat.le_mul_of_pos_right _ pb)).trans spec
  have raw: (q).rawBits*M≤h/2:=lookup _ (Or.inr (by simp [receiverUnits]))
  have lanes:M≤h/2:=(Nat.le_mul_of_pos_left _ born).trans bit
  have shift:M*2^k≤h:=by
    have unit:M*2^k≤((z).rootBits*(V).sheets.blocks)*M:=by
      change M*2^k≤((z).rootBits*2^k)*M
      calc
        M*2^k=(2^k)*M:=Nat.mul_comm ..
        _≤_:=Nat.mul_le_mul_right M (Nat.le_mul_of_pos_left _ born)
    exact (unit.trans spec).trans (Nat.div_le_self ..)
  have original:H*chunks ((S.groupCount (age+1))*2^k) M≤T:=by rw [split];exact oldR.trans up
  have r:ScanRoom (z).placement (z).batch h T:=
    ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,lanes.trans (Nat.div_le_self ..),shift,bit,spec,
      original,((Nat.mul_le_mul_left H fewer).trans oldR).trans up,oldH.trans up,newR,book.trans up⟩
  have price:=DescentPlacedInvoiceVolume.birth (z) h T r
  have top: (z).rootBits*(z).stop≤(V).rootOutputBits:=(Nat.le_max_right ..).trans (Nat.le_max_left ..)
  have first:=price ((Nat.mul_le_mul_right M top).trans (lookup _ (.inl (by simp [rootUnits]))))
    (lookup _ (.inr (by simp [receiverUnits])))
  have second:=checkpoint (q) h T U raw lanes (lookup _ (.inr (by simp [receiverUnits]))) newR (book.trans up)
  apply (Nat.add_le_add first second).trans
  unfold primitiveFactor
  rw [←Nat.add_mul,Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  dsimp [T];rw [Nat.add_mul,Nat.one_mul];omega

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
