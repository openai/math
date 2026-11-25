import OAI.Hierarchy.TaggedWideSwitchTariff
import OAI.Hierarchy.TaggedWideCalendarMask
import OAI.Hierarchy.TaggedWideTimeGuard
import OAI.Hierarchy.TaggedWideCalendarPlane
import OAI.Hierarchy.TaggedWideDataCost

namespace OAI
/-! # Prices of the reported shorter-output mask, chronological mask and decoded output plane -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.Tagged.WideStack.Leaf
open TaggedShorterBudget WireTelescope CalendarTape WideControlJoin
open scoped Classical BigOperators

variable {F : Type} [Field F] {T E H V Ex Se : Type} [Fintype T] [Fintype E] [Fintype H] [Fintype V]
  [Fintype Ex] [Fintype Se] {ports lanes groups view w b : ℕ}
  (key : T ↪ ℕ×ℕ) (cap : E→ℕ) (histCap : H→ℕ) (es : List ProtocolRAM.Calendar.Event)
local notation "cls" => fun t:T=>(key t).2
local notation "digit" => fun t:T=>⌈dyadic (key t).2*w⌉₊
local notation "hist" => Fin ((es.length+1)*Fintype.card ((u:H)×Fin (histCap u)))
local notation "pos" => OutputData T (Fin groups) ports lanes digit
local notation "P" => (Fin groups×Fin ports)×Fin view
local notation "D" => DataWorkspace T (Fin groups) E H ports lanes (es.length+1) view digit cap histCap
variable (word : ∀_t:T,Fin groups→Bool→Fin (ports*lanes)→Fin b→V)
  (payload : ∀t:T,ProtocolStackContraction.Slot (Fin groups) (ports*lanes)×Fin ⌈dyadic (key t).2*w⌉₊→V)
  (fits : ∀r,histCap r≤2^b) (timeWord : Fin (es.length+1)→H→Fin b→V) (datum : Fin ((es.length+1)*Fintype.card ((u:H)×Fin (histCap u)))→V)
  (G : Gate)

theorem masks_and_plane_cost :
    let pad:=positiveMask (F:=F) (w:=w) cls word payload
    let time:=timeGuard (F:=F) histCap es fits timeWord datum
    let plane:=planeNet (F:=F) (Ex:=Ex) (Se:=Se) (H:=hist) (groups:=groups) (ports:=ports)
      (lanes:=lanes) (view:=view) (w:=w) key cap G
    (pad.cells+pad.internal)+(time.cells+time.internal)+(plane.cells+plane.internal)≤
      Fintype.card D*(200*b+65+48*(2*Fintype.card T)+98) := by
  intro pad time plane
  have posBill : pad.cells+pad.internal≤Fintype.card pos*(200*b+65):=by
    have charged:=positiveMask_cost (F:=F) (w:=w) cls word payload
    simpa only [OutputData,Fintype.card_sigma,Finset.sum_mul] using charged
  have timeBill:=timeGuard_cost (F:=F) histCap es fits timeWord datum
  have planeBill:=planeNet_cost (F:=F) (Ex:=Ex) (Se:=Se) (H:=hist) (groups:=groups) (ports:=ports)
    (lanes:=lanes) (view:=view) (w:=w) key cap G
  have rows : Fintype.card pos+((es.length+1)*Fintype.card ((u:H)×Fin (histCap u)))≤Fintype.card D:=by
    simp only [DataWorkspace,Fintype.card_sum,Fintype.card_fin];omega
  have decoded : Fintype.card P≤Fintype.card D:=by
    simp only [DataWorkspace,Fintype.card_sum];omega
  calc
    _ ≤ (Fintype.card pos+((es.length+1)*Fintype.card ((u:H)×Fin (histCap u))))*(200*b+65)+
        Fintype.card P*(48*(2*Fintype.card T)+98) := by
          exact (Nat.add_le_add (Nat.add_le_add posBill timeBill) planeBill).trans_eq
            (congrArg (fun subtotal : ℕ => subtotal + _) (Nat.add_mul _ _ _).symm)
    _ ≤ Fintype.card D*(200*b+65)+Fintype.card D*(48*(2*Fintype.card T)+98) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ rows) (Nat.mul_le_mul_right _ decoded)
    _ = _ := by ring

end Hierarchy.Tagged.WideStack.Leaf

namespace Hierarchy.Tagged.WideParent
open Real Filter
theorem logarithmic_mask_fee {κ A : ℝ} (B K types : ℕ) :
    ∃C:ℝ,0≤C ∧ ∀ᶠx : WideParent κ A in large κ A,∀fee cells:ℕ,
      cells≤B*(2^x.h*x.w) → fee≤cells*(200*columnBits (K*x.w)+65+48*(2*types)+98) →
      (fee:ℝ)≤C*((2:ℝ)^x.h*x.w*log (x.h:ℝ)) := by
  let L:=max 1 (logb 2 ((K+1:ℕ):ℝ)+2+A/log 2)
  let factor:=200*L+65+48*(2*(types:ℝ))+98
  have posL : 0≤L:=(by norm_num : (0:ℝ)≤1).trans (le_max_left ..)
  have posF : 0≤factor:=by dsimp [factor];positivity
  refine ⟨(B:ℝ)*factor,by positivity,?_⟩
  have high : Tendsto (h (κ:=κ) (A:=A)) (large κ A) atTop:=tendsto_comap
  filter_upwards [high.eventually ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1)] with x big
  change 1≤log (x.h:ℝ) at big
  intro fee cells size bill
  have hw:=x.formats.2.1
  have hh : 0<x.h:=by change 0<x.val.1;have two:=x.property.1.1;omega
  have upper : K*x.w+1≤(K+1)*x.w:=by nlinarith only [hw]
  have est:=site_log A (K+1) (by omega) x.h x.w (K*x.w+1) big hh hw x.property.1.2.2 (by omega) upper
  have loose:=mul_le_mul_of_nonneg_right (le_max_right 1 (logb 2 ((K+1:ℕ):ℝ)+2+A/log 2))
    (zero_le_one.trans big)
  have bit : (columnBits (K*x.w):ℝ)≤L*log (x.h:ℝ):=by
    rw [columnBits,Nat.cast_add,Nat.cast_one]
    exact (by linarith only [est] : ((Nat.log 2 (K*x.w+1):ℕ):ℝ)+1 ≤
      (logb 2 ((K+1:ℕ):ℝ)+2+A/log 2)*log (x.h:ℝ)).trans loose
  have localBill : ((200*columnBits (K*x.w)+65+48*(2*types)+98:ℕ):ℝ)≤factor*log (x.h:ℝ):=by
    push_cast
    dsimp [factor]
    nlinarith only [bit,big,mul_nonneg (Nat.cast_nonneg types) (sub_nonneg.mpr big)]
  calc
    (fee:ℝ) ≤ ((B*(2^x.h*x.w)*(200*columnBits (K*x.w)+65+48*(2*types)+98):ℕ):ℝ) :=
      by exact_mod_cast bill.trans (Nat.mul_le_mul_right _ size)
    _ ≤ (B*(2^x.h*x.w):ℕ)*(factor*log (x.h:ℝ)) := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left localBill (by positivity)
    _ = _ := by push_cast;ring

end Hierarchy.Tagged.WideParent

end
end OAI
