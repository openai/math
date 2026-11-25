import OAI.Hierarchy.DescentRegisterTimelineCore
import OAI.Hierarchy.DescentOrdinarySharedLedger

namespace OAI
/-! Sum the actual register-selected instruction prices and keep the single
initial native program separate from the dated maneuvers. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline.CostCore
open ProtocolRAM DescentCompiler TerminalScale DescentDatedAddressBook
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {w : ℕ}
    {Cut : ℕ→Type*} (issue : ∀i,Cut i→Position→Move w→Prop) (initial : Position)
set_option quotPrecheck false
local notation "current" i => position issue initial i
local notation "machine" => date issue initial
/-- Charge the selected native instruction only to the existing named cut.
The public empty scan has its own measured four steps and nineteen names. -/
theorem selected_tariff (i limit : ℕ) (idle : 137*w ≤ limit)
    (actual : ∀(e : Cut i) (m : Move w),issue i e (current i) m→m.code.tariff ≤ limit) :
    (machine i).tariff ≤ limit :=by
  change (selected issue i (current i)).code.tariff ≤ limit
  unfold selected
  split
  · rename_i hit
    obtain ⟨e,h⟩:=hit.choose_spec.1
    exact actual e _ h
  · change (4+7*DescentStaticWordColumn.names (scan w 0 0 .row))*w ≤ limit
    rw [DescentStaticWordColumn.names_scan]
    exact idle

/-- The finite ledger includes one additional boundary index. Give it the
empty sum, since terminal replay starts after the last registered instruction. -/
theorem date_ledger (t J f g reset M τ h p high low saving : ℕ)
    (config : S=stageNumbers G t J f g reset M (tail τ J)) (positive : 0 < h)
    (host : ((S.length+1)*(high+1))*h ≤ p*2^(tail τ J))
    (items : (S.length+1)*(2^S.hostGain)^S.length*low*2^J ≤ p)
    (fees : ∀i < S.length,(machine i).tariff ≤ S.hostSize i*h*high+
      S.hostSize i*(S.groupCount i*S.radix)*low+M/(2^J)^saving) :
    (∑i∈Finset.range S.length,(machine i).tariff)*2^J ≤ 2*(M*(S.copies*p)) :=by
  let cost (i : ℕ):=if i < S.length then (machine i).tariff else 0
  have paid (i : Fin (S.length+1)) : cost i.val ≤ S.hostSize i.val*h*high+
      S.hostSize i.val*(S.groupCount i.val*S.radix)*low+M/(2^J)^saving:=by
    dsimp only [cost]
    split
    · exact fees i.val ‹_›
    · exact Nat.zero_le _
  have total:=stage_ledger_shared G t J f g reset M τ h p high low saving S config positive host items
    (fun i=>cost i.val) paid
  rw [Fin.sum_univ_eq_sum_range cost,Finset.sum_range_succ,show cost S.length=0 by simp [cost],Nat.add_zero] at total
  have same : (∑i∈Finset.range S.length,(machine i).tariff)=∑i∈Finset.range S.length,cost i :=
    Finset.sum_congr rfl fun i hi=>by simp [cost,Finset.mem_range.mp hi]
  rw [same]
  exact total

/-- A single cofinal instruction estimate covers each side of the actual
public menu. Several shared table residues can be paid with the original hosts. -/
theorem funded_issue (t J f g reset M τ h ratio p lead exponent share saving : ℕ)
    (config : S=stageNumbers G t J f g reset M (tail τ J)) (positive : 0 < h)
    (sites : 0 < M) (width : w ≤ ratio*h)
    (issuedFees : ∀i < S.length,∀(e : Cut i) (m : Move w),
      issue i e (current i) m→m.code.tariff ≤
        S.hostSize i*h*(lead*scale J exponent)+S.hostSize i*(S.groupCount i*S.radix)*(lead*scale J exponent)+
        share*(M/(2^J)^saving)) :
    let coef:=lead+share+137*ratio
    let localRate:=coef*scale J exponent
    ((S.length+1)*(localRate+1))*h ≤ p*2^(tail τ J) →
    (S.length+1)*(2^S.hostGain)^S.length*localRate*2^J ≤ p →
    (∑i∈Finset.range S.length,(machine i).tariff)*2^J ≤ 2*(M*(S.copies*p)) :=by
  intro coef R host items
  apply date_ledger issue initial t J f g reset M τ h p R R saving config positive host items
  intro i hi
  have radix : 0 < S.radix :=by rw [config];exact Nat.two_pow_pos _
  have base : S.hostSize 0=M:=by rw [config];change M*_ ^ (0:ℕ)=M;simp
  have size : M ≤ S.hostSize i :=base ▸ host_mono S (Nat.zero_le i) radix
  have header : M ≤ S.hostSize i*h:=size.trans (Nat.le_mul_of_pos_right _ positive)
  have hp := sites.trans_le size
  have age : 1 ≤ scale J exponent := Nat.two_pow_pos _
  have room : lead*scale J exponent+share ≤ R:=by
    dsimp [R,coef]
    rw [Nat.add_mul,Nat.add_mul]
    have:=Nat.le_mul_of_pos_right share age
    omega
  apply selected_tariff issue initial i
  · have bus:137*w ≤ (S.hostSize i*h)*(137*ratio) :=by
      calc
        _ ≤ 137*(ratio*h) := Nat.mul_le_mul_left _ width
        _ ≤ (S.hostSize i)*(137*(ratio*h)) := Nat.le_mul_of_pos_left _ hp
        _ = _ :=by ring
    have control:137*ratio ≤ R:=by
      apply (show 137*ratio ≤ coef by dsimp [coef];omega).trans
      exact Nat.le_mul_of_pos_right _ age
    exact (bus.trans (Nat.mul_le_mul_left _ control)).trans
      ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  · intro e m published
    have entry:=issuedFees i hi e m published
    have table:share*(M/(2^J)^saving) ≤ (S.hostSize i*h)*share:=by
      rw [Nat.mul_comm share]
      exact Nat.mul_le_mul_right _ ((Nat.div_le_self ..).trans header)
    have both:=Nat.mul_le_mul_left (S.hostSize i*h) room
    rw [Nat.mul_add] at both
    have second:=Nat.mul_le_mul_left (S.hostSize i*(S.groupCount i*S.radix))
      (show lead*scale J exponent ≤ R by omega)
    have sum := Nat.add_le_add (Nat.add_le_add_left table (S.hostSize i*h*(lead*scale J exponent))) second
    rw [Nat.add_right_comm] at entry
    exact entry.trans ((sum.trans (Nat.add_le_add_right both _)).trans (Nat.le_add_right ..))

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline.CostCore

end OAI
