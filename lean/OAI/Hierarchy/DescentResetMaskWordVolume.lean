import OAI.Hierarchy.DescentPhysicalResetDateTariff
import OAI.Hierarchy.DescentResetReceivedVolume
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # The actual remapping table, three rank passes, and nine mask sources -/
namespace Hierarchy.DescentDatedAddressBook
open DescentResetCandidateDate DescentSIMDLookup DescentStaticWordColumn

private theorem mask_table (L : Shape) (N field h : ℕ) (fieldCount : N ≤ 9)
    (packed : (field*N+field)*L.lanes ≤ h/2) :
    L.size N field ≤ 20*(2*L.rows+1+2^(h/2)) := by
  have bank : 2^(L.width N field) ≤ 2*L.rows+1+2^(h/2) := by
    unfold Shape.width
    rcases le_total ((field*N+field)*L.lanes) L.rowBits with first | last
    · rw [max_eq_right first]
      exact (DescentDyadicSpan.span_le L.rows).trans (Nat.le_add_right ..)
    · rw [max_eq_left last]
      exact (Nat.pow_le_pow_right (by decide) packed).trans (Nat.le_add_left ..)
  exact Nat.mul_le_mul (by omega : N*2+2 ≤ 20) bank

private def scanTime (jobs rows size work : ℕ) :=
  4+10*size+(4+jobs*(4+rows*(2*work+4)+(4+44*rows)))

private def scanText (jobs size work : ℕ) := 15*(size+1)+(15+jobs*(102+4*work))

private theorem mask_numeric (jobs rows sparse fee page : ℕ) :
    let relay := 2*(2*rows+1)+(2*sparse+1)
    let size := 20*(2*rows+1+page)
    4+10*relay+(scanTime (3*jobs) rows size fee+scanTime jobs rows size fee)+
      7*(15*(relay+1)+(scanText (3*jobs) size fee+scanText jobs size fee)) ≤
    32768*(jobs+1)*(fee+1)*(1+rows+sparse+page) := by
  dsimp only [scanTime,scanText]
  ring_nf
  omega

namespace PhysicalReset
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)

private theorem maskCharges (m : DescentResetDenseOperand.MaskedDate) (h T rankFee maskFee : ℕ)
    (rank : rankFee ≤ T) (mask : maskFee ≤ T) (packed : 10*m.field*m.lanes ≤ h/2) :
    (4+10*m.relay.size)+(m.mixed.ranks.costBound 5 m.field rankFee+m.mixed.masks.costBound 9 m.field maskFee)+
     7*(15*(m.relay.size+1)+(m.mixed.ranks.nameBound 5 m.field rankFee+m.mixed.masks.nameBound 9 m.field maskFee)) ≤
      32768*(m.jobs+1)*(T+1)*(1+m.toShape.rows+m.sparseHosts+2^(h/2)) := by
  let rows := m.toShape.rows
  let area := 20*(2*rows+1+2^(h/2))
  have bound (N : ℕ) (n : N ≤ 9) : (m.field*N+m.field)*m.lanes ≤ h/2 :=
    (Nat.mul_le_mul_right m.lanes (by nlinarith only [Nat.mul_le_mul_left m.field n] :
      m.field*N+m.field ≤ 10*m.field)).trans packed
  have r : m.mixed.ranks.size 5 m.field ≤ area :=
    mask_table _ 5 _ h (by decide) (bound 5 (by decide))
  have s : m.mixed.masks.size 9 m.field ≤ area :=
    mask_table _ 9 _ h (by decide) (bound 9 (by decide))
  have relay : m.relay.size ≤ 2*(2*rows+1)+(2*m.sparseHosts+1) :=
    Nat.add_le_add (Nat.mul_le_mul_left 2 (DescentDyadicSpan.span_le rows)) (DescentDyadicSpan.span_le m.sparseHosts)
  change 4+10*m.relay.size+
      (scanTime (3*m.jobs) rows (m.mixed.ranks.size 5 m.field) rankFee+
       scanTime m.jobs rows (m.mixed.masks.size 9 m.field) maskFee)+
      7*(15*(m.relay.size+1)+(scanText (3*m.jobs) (m.mixed.ranks.size 5 m.field) rankFee+
       scanText m.jobs (m.mixed.masks.size 9 m.field) maskFee)) ≤ _
  apply le_trans _ (mask_numeric m.jobs rows m.sparseHosts T (2^(h/2)))
  dsimp only [scanTime,scanText,area] at *
  gcongr

theorem rank_mask_envelope (h T : ℕ) (rank : rankWork u ≤ T) (mask : maskWork u ≤ T)
    (packed : 10*u.masked.field*u.masked.lanes ≤ h/2) :
    let m := u.masked
    instructionWords (m.code w) m.ticks ≤
      32768*(m.jobs+1)*(T+1)*(1+m.toShape.rows+m.sparseHosts+2^(h/2)) := by
  intro m
  exact (rank_mask_words u).trans (maskCharges m h T _ _ rank mask packed)

end PhysicalReset
end Hierarchy.DescentDatedAddressBook

namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentSixParty DescentCompiler
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)

def maskFactor (jobs source shapes growth : ℕ) := 32768*(jobs+1)*(source+1)*(2+shapes+growth)

set_option quotPrecheck false
local notation "V" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base

/-- The new host rectangle shrinks its group axis at this same scheduled descent. -/
theorem mask_envelope_area (radix : S.radix=2^k) (live : age< S.length) :
    1+(V).sheets.hosts*chunks (V).sheets.groups (V).sheets.lanes+(V).front.peer.hosts+2^(h/2) ≤
      (2+(V).front.peer.shapes+2^S.hostGain*S.radix)*receiptArea h (S.hostSize age) (chunks (S.groupCount age) (2^e)) := by
  let cells := chunks (S.groupCount age) (2^e)
  let next := chunks (S.groupCount (age+1)) (2^e)
  let gain := 2^S.hostGain*S.radix
  let H := S.hostSize age
  let area := receiptArea h H cells
  have group : S.groupCount (age+1)*2^k=S.groupCount age := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits live radix)).symm
  have few : S.groupCount (age+1) ≤ S.groupCount age := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq group
  have packed : next ≤ cells := Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right few _) _)
  have paid : H*cells ≤ area := by dsimp only [area,receiptArea];omega
  have hosts : H ≤ area := by dsimp only [area,receiptArea];omega
  have half : 2^(h/2) ≤ area := (Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans (Nat.le_add_left ..)
  have one : 1 ≤ area := (Nat.two_pow_pos _).trans_le half
  have newSize : S.hostSize (age+1)=H*gain := by simp only [H,gain,AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have newRows : S.hostSize (age+1)*next ≤ gain*area := by
    rw [newSize]
    simpa only [Nat.mul_left_comm,Nat.mul_assoc] using
      Nat.mul_le_mul_left gain ((Nat.mul_le_mul_left H packed).trans paid)
  have raw : H*(V).front.peer.shapes ≤ (V).front.peer.shapes*area := by
    simpa only [Nat.mul_comm H] using Nat.mul_le_mul_left (V).front.peer.shapes hosts
  change 1+S.hostSize (age+1)*next+H*(V).front.peer.shapes+2^(h/2) ≤ (2+(V).front.peer.shapes+gain)*area
  nlinarith only [one,half,newRows,raw]

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
