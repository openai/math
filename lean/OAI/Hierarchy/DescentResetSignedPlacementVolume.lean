import OAI.Hierarchy.DescentResetPrimitiveReceivedVolume
import OAI.Hierarchy.DescentResetLookupFactor

namespace OAI
/-! The earlier signed candidate slots use the actual projected pitch in both passes. -/
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
local notation "stageGrowth" => 2^S.hostGain*S.radix
local notation "area" => receiptArea h H (chunks O M)

def signedPlacementFactor (v : ResetOutput) (growth : ℕ) :=
  let C:=v.setup
  (stemFactor C.strip C.placement.blocks 7+suffixFactor C.placement.shapes C.strip C.placement.blocks)*(growth+1)

theorem signed_placement_volume (radix : S.radix=2^k) (reached : age<S.length)
    (lookup : ∀t,t∈(V).rootUnits ∨ t∈(V).receiverUnits→t*M≤h/2) :
    (V).setup.placement.invoice (V).setup.signedFields 7≤(V).signedPlacementFactor stageGrowth*area:=by
  let T:=stageGrowth*area
  have gp:0<stageGrowth:=by rw [radix];positivity
  have split:S.groupCount (age+1)*2^k=O:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits reached radix)).symm
  have fewer:chunks (S.groupCount (age+1)) M≤chunks O M:=Nat.div_le_div_right
    (Nat.sub_le_sub_right (Nat.add_le_add_right ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq split) _) _)
  have next:S.hostSize (age+1)=H*stageGrowth:=by simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have up:area≤T:=Nat.le_mul_of_pos_left _ gp
  have oldH:H≤area:=by unfold receiptArea;omega
  have oldR:H*chunks O M≤area:=by unfold receiptArea;omega
  have newR:S.hostSize (age+1)*chunks (S.groupCount (age+1)) M≤T:=by
    rw [next,show (H*stageGrowth)*chunks (S.groupCount (age+1)) M=stageGrowth*(H*chunks (S.groupCount (age+1)) M) by ring]
    exact Nat.mul_le_mul_left stageGrowth ((Nat.mul_le_mul_left H fewer).trans oldR)
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
  let c:=(V).setup
  have width:(c.signedBits*2^k)*M≤h/2:=lookup ((V).setup.signedFields.bits*(V).sheets.blocks) (.inr (by simp [receiverUnits]))
  have part:c.signedBits*M≤h/2:=(Nat.mul_le_mul_right M (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k))).trans width
  have r:ScanRoom c.placement c.signedFields h T:=
    ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _,lanes.trans (Nat.div_le_self ..),shift,part,width,
      original,((Nat.mul_le_mul_left H fewer).trans oldR).trans up,oldH.trans up,newR,book.trans up⟩
  apply (DescentPlacedInvoiceVolume.placement c.placement c.signedFields h T 7 r).trans
  unfold signedPlacementFactor
  change _≤(_*(stageGrowth+1))*area
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (by dsimp [T]; rw [Nat.add_mul,Nat.one_mul];omega)

theorem signed_factor_bound (v : ResetOutput) (growth J e : ℕ)
    (slots : v.setup.strip≤TerminalScale.scale J e)
    (blocks : v.setup.placement.blocks≤TerminalScale.scale J e)
    (shapes : v.setup.placement.shapes≤TerminalScale.scale J e)
    (stages : growth≤TerminalScale.scale J e) :
    v.signedPlacementFactor growth≤1000000*TerminalScale.scale J (3*e):=by
  let n:=TerminalScale.scale J e
  have one:1≤n:=Nat.two_pow_pos _
  calc
    _≤(stemFactor n n 7+suffixFactor n n n)*(n+1):=by
      unfold signedPlacementFactor stemFactor suffixFactor volumeFactor
      dsimp only
      gcongr
    _≤1000000*n^3:=by
      unfold stemFactor suffixFactor volumeFactor
      have square:n≤n^2:=by nlinarith [Nat.mul_le_mul_left n one]
      have cube:n^2≤n^3:=by nlinarith [Nat.mul_le_mul_left (n^2) one]
      nlinarith
    _=_:=by simp [n,TerminalScale.scale,show 3*e*(J+1)=(e*(J+1))*3 by ring,pow_mul]
end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
