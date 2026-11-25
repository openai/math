import OAI.Computability.NearSquareRoot.InterchangeConfiguredBatch
import OAI.Computability.NearSquareRoot.InterchangeVerifiedAtlas
import OAI.Computability.NearSquareRoot.InterchangeROMRepairLowerSizes
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStage

/-!
# Integer contraction tests for interchange templates

The selected minor and the incidence list determine the maximum number of
recursive calls for one batch. Integer exponentiation checks its normalized
cost at the rational exponent chosen by the schedule generator.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.TemplateCost

open OAI.LinearAlgebra.FiniteFourier InterchangeROMRepair.Sizes Generator

/-- Independent ground-field records occupied by all labels. -/
def width (m L : ℕ) := rows m * basisCount m * L

/-- Recursive call bound on one whole batch, before the radix split. -/
def calls (m a L h inc : ℕ) :=
  (4 * pencilOrder m) * (108 * (rows m * basisCount m) * (a+2) * (1+inc) * (L+m*h)) +
    4*m*(checkRows m * basisCount m)*L

/-- Integer test for the padded batch and the two reserve passes. -/
def accept (j m a b W C : ℕ) : Bool :=
  contractionTest (C*BatchRows.groups b W + 2*a*b) b m (j+4) (2*(j+2))

theorem width_eq (m L : ℕ) : width m L = independentRows m * L := by
  simp only [width,rows_eq,basisCount_eq,independentRows,componentWidth,SwapRepair.BasisIndex,Fintype.card_fin]

theorem calls_eq (p k m : ℕ) [Fact p.Prime] :
    calls m (hammingReserve p k) (Fintype.card (HammingLabels p k)) (hammingLabelMatrix p (2^k)).rank
      (labelIncidence p k (Fact.out : p.Prime).pos) = batchCalls p k m 108 := by
  simp only [calls,batchCalls,card_gramIndex,hammingReserve,HammingLabels,pencilOrder_eq,rows_eq,
    checkRows_eq,basisCount_eq,independentRows,correctedRows,componentWidth,SwapRepair.BasisIndex,Fintype.card_fin]
  ring

theorem accept_iff (j m a b W C : ℕ) (hb : 0 < b) :
    accept j m a b W C = true ↔
      ((C * BatchRows.groups b W : ℕ) : ℝ)/b + 2*a < (m : ℝ)^(targetExponent j) := by
  have he : ((j+4 : ℕ) : ℝ) / (2*(j+2) : ℕ) = targetExponent j := by
    unfold targetExponent
    push_cast
    field_simp
    ring
  rw [accept, contractionTest_correct _ _ _ _ _ hb (by positivity), he]
  push_cast
  rw [add_div, mul_div_cancel_right₀ _ (by exact_mod_cast hb.ne')]

open StageRoute StageLedger IntegerMultiplication.Port

/-- A passing finite catalog certifies the price used in the raw arithmetic
test for every choice of stage matrices on the given incidence table. -/
theorem bound_catalog {m a b inc : ℕ} {L H B K E : Type} [DecidableEq L]
    [Fintype L] [Fintype H] [Fintype B] [Field K] [AddCommGroup E] [Module K E]
    {r : B → Rectangle L} (w : AddressROM.Catalog r a m b) (hb : 1 < b)
    (hw : AddressROM.valid w = true) (I J : H → L) (M : Matrix H H K)
    (hinc : ∀ side v, Fintype.card (Incident r side v) ≤ inc)
    (A₀ : Fin (4*pencilOrder m) → E →+ E) (A : Fin (4*pencilOrder m) → Fin m → E →+ E) :
    let quote (op : Move r (Fin m) I J) := ((AddressROM.instructions w op).map Lag.prices).sum
    (∑ s, (rows m * basisCount m) * StageScript.cost quote (stage r I J M (A₀ s) (A s))) +
      4*m*(checkRows m * basisCount m)*Fintype.card L ≤ calls m a (Fintype.card L) (Fintype.card H) inc := by
  intro quote
  have paid (v : Move r (Fin m) I J) : quote v ≤ AddressROM.cap a v :=
    AddressROM.instructions_cost w hb hw v
  let lim := 2*(54*(a+2))*(rows m*basisCount m)*(1+inc)*(Fintype.card L+m*Fintype.card H)
  have hs (s : Fin (4*pencilOrder m)) : (rows m*basisCount m) *
      StageScript.cost quote (stage r I J M (A₀ s) (A s)) ≤ lim := by
    simpa only [lim,Fintype.card_fin] using scalar_stage_cost_le (cap:=54*(a+2)) (Fin (rows m*basisCount m)) M
      (A₀ s) (A s) quote (Nat.eq_zero_of_le_zero (paid .idle))
      (fun j e => Nat.eq_zero_of_le_zero (paid (.align j e)))
      (fun j e => Nat.eq_zero_of_le_zero (paid (.unalign j e)))
      (fun e => paid (.prepare e)) (fun e => paid (.restore e))
      (fun j t => paid (.gather j t)) (fun j t => paid (.distribute j t)) hinc
  unfold calls
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _s : Fin (4*pencilOrder m), lim := Finset.sum_le_sum fun s _ => hs s
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,lim]; ring

variable {X : Type*} [Primcodable X]

theorem primrec_width {m L : X → ℕ} (hm : Primrec m) (hL : Primrec L) :
    Primrec fun x => width (m x) (L x) :=
  Primrec.nat_mul.comp (Primrec.nat_mul.comp (primrec_rows.comp hm) (primrec_basisCount.comp hm)) hL

theorem primrec_calls {m a L h inc : X → ℕ} (hm : Primrec m) (ha : Primrec a) (hL : Primrec L)
    (hh : Primrec h) (hi : Primrec inc) : Primrec fun x => calls (m x) (a x) (L x) (h x) (inc x) := by
  have hr := Primrec.nat_mul.comp (primrec_rows.comp hm) (primrec_basisCount.comp hm)
  have hc := Primrec.nat_mul.comp (primrec_checkRows.comp hm) (primrec_basisCount.comp hm)
  have prep := Primrec.nat_mul.comp (Primrec.nat_mul.comp (.const 108) hr) (Primrec.nat_add.comp ha (.const 2))
  have shared := Primrec.nat_mul.comp (Primrec.nat_mul.comp prep (Primrec.nat_add.comp (.const 1) hi))
    (Primrec.nat_add.comp hL (Primrec.nat_mul.comp hm hh))
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp (.const 4) (primrec_pencilOrder.comp hm)) shared)
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp (.const 4) hm) hc) hL)

theorem primrec_groups {b W : X → ℕ} (hb : Primrec b) (hw : Primrec W) :
    Primrec fun x => BatchRows.groups (b x) (W x) := by
  simpa only [BatchRows.groups,Nat.ceilDiv_eq_add_pred_div] using
    Primrec.nat_div.comp (Primrec.nat_sub.comp (Primrec.nat_add.comp hb hw) (.const 1)) hw

theorem primrec_accept {j m a b W C : X → ℕ} (hj : Primrec j) (hm : Primrec m) (ha : Primrec a)
    (hb : Primrec b) (hw : Primrec W) (hc : Primrec C) :
    Primrec fun x => accept (j x) (m x) (a x) (b x) (W x) (C x) := by
  have hden := Primrec.nat_mul.comp (.const 2) (Primrec.nat_add.comp hj (.const 2))
  have hnum := Primrec.nat_add.comp hj (.const 4)
  have htotal := Primrec.nat_add.comp (Primrec.nat_mul.comp hc (primrec_groups hb hw))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (.const 2) ha) hb)
  exact Primrec.nat_lt.decide.comp (primrecNatPow.comp htotal hden)
    (Primrec.nat_mul.comp (primrecNatPow.comp hb hden) (primrecNatPow.comp hm hnum))

/-- The search test has witnesses at every exponent and above every fixed
radix threshold. A single physical address frame serves all field widths. -/
theorem exists_frame (j threshold : ℕ) :
    ∃ p : ℕ, ∃ hp : Fact p.Prime, 2 < p ∧ ∃ m : ℕ, 2 ≤ m ∧ ∃ k : ℕ,
      letI := hp
      let a := hammingReserve p k
      let L := Fintype.card (HammingLabels p k)
      let h := (hammingLabelMatrix p (2^k)).rank
      let inc := labelIncidence p k hp.out.pos
      let W := width m L
      ∃ (K : StageKernel p k m) (atlas : RectangleAtlas (nodeRectangles p k) a) (b : ℕ),
        b.Prime ∧ max threshold W < b ∧ Nonempty (RectangleAtlas.Frame atlas m b) ∧
        K.calls atlas ≤ calls m a L h inc ∧ accept j m a b W (calls m a L h inc) = true := by
  have hγ : 1/2 < midExponent j := by
    unfold midExponent
    exact lt_add_of_pos_right _ (by positivity)
  have hα : midExponent j < targetExponent j := by
    unfold midExponent targetExponent
    apply add_lt_add_right
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith [Nat.cast_nonneg (α:=ℝ) j]
  obtain ⟨p,hp,odd,sel⟩ := exists_contracted_frame hγ hα
  let := hp
  obtain ⟨m,hm,large⟩ := (sel.and (Filter.eventually_ge_atTop (2:ℕ))).exists
  obtain ⟨k,atlas,radix⟩ := hm
  obtain ⟨b,hb,big,code,_,frame,_,contract⟩ := radix threshold ∅
  obtain ⟨K⟩ := StageKernel.exists_kernel p k m odd large
  refine ⟨p,hp,odd,m,large,k,K,atlas,b,hb,?_,frame,?_,?_⟩
  · simpa only [width_eq] using big
  · rw [calls_eq]
    exact K.calls_le_batchCalls atlas
  · rw [accept_iff _ _ _ _ _ _ hb.pos,calls_eq,width_eq]
    exact contract

end Interchange.TemplateCost

end NearSquareRoot
end Computability
end OAI
