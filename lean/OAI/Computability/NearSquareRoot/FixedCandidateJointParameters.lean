import OAI.Computability.NearSquareRoot.FixedCandidateBoxCutoff
import OAI.Computability.NearSquareRoot.FixedLayerWalshTemplate
import OAI.Computability.NearSquareRoot.InterchangeTemplateSelect
import OAI.Computability.NearSquareRoot.FixedCandidateCRTBudgetNative
import OAI.Computability.IntegerMultiplication.Net.Contract

/-! # Joint computed Fourier, interchange and reserve parameters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CandidateParameters

open IntegerMultiplication Filter DigitPacking KernelPass.ComputableSyntax Controlled

/-- The exponent index, two position-router reserve degrees, and sparse mask
reserve degree. No component encodes a certificate of a good resource bound. -/
abbrev Guess := ℕ × ℕ × ℕ × ℕ
def exponent (p : Guess) := p.1
def positionLow (p : Guess) := p.2.1
def positionHigh (p : Guess) := p.2.2.1
def exterior (p : Guess) := p.2.2.2

theorem exponent_pr : Primrec exponent := .fst
theorem positionLow_pr : Primrec positionLow := Primrec.fst.comp Primrec.snd
theorem positionHigh_pr : Primrec positionHigh := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem exterior_pr : Primrec exterior := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

noncomputable def signedTemplate (p : Guess) : Raw := computable_midpoint_templates.choose (exponent p)

theorem signedTemplate_computable : Computable signedTemplate :=
  computable_midpoint_templates.choose_spec.1.comp exponent_pr.to_comp

theorem signedTemplate_good (p : Guess) :
    (interpreted (signedTemplate p)).Good (exponent p+3) (2*(exponent p+2)) :=
  computable_midpoint_templates.choose_spec.2 (exponent p)

theorem signedTemplate_accurate (p : Guess) :
    AccurateTemplate (exponent p+3) (2*(exponent p+2)) (rawPrecisionCutoff (signedTemplate p)) (signedTemplate p) :=
  accurateTemplate_of_good _ (signedTemplate_good p)

def nativeIndex (p : Guess) := 2*exponent p+2

theorem nativeIndex_pr : Primrec nativeIndex :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) exponent_pr) (.const 2)

noncomputable def rectangle (p : Guess) : Interchange.Template.Data :=
  Interchange.Template.Data.select (nativeIndex p) Net.Shuttle.base

theorem rectangle_computable : Computable rectangle :=
  Interchange.Template.Data.computable_select.comp nativeIndex_pr.to_comp (.const Net.Shuttle.base)

theorem rectangle_valid (p : Guess) :
    Interchange.Template.Data.Valid (nativeIndex p) Net.Shuttle.base (rectangle p) :=
  Interchange.Template.Data.selected_valid ..

theorem native_exponent (p : Guess) : Generator.targetExponent (nativeIndex p) = Generator.midExponent (exponent p) := by
  unfold Generator.targetExponent Generator.midExponent nativeIndex
  push_cast
  ring_nf

theorem rectangle_contraction (p : Guess) :
    let x := rectangle p
    ((x.calls*BatchRows.groups x.b x.width : ℕ) : ℝ)/x.b + (2*x.a : ℕ) <
      (x.m : ℝ)^Generator.midExponent (exponent p) := by
  rw [← native_exponent]
  exact Interchange.Template.Data.select_contraction ..

def positionCutoff (p : Guess) := boxCutoff (positionLow p) (positionHigh p)

theorem positionCutoff_pr : Primrec positionCutoff := boxCutoff_primrec.comp positionLow_pr positionHigh_pr

theorem positionCutoff_fits {p : Guess} {k : ℕ} (h : positionCutoff p ≤ k) :
    payloadBits (positionLow p) k + payloadBits (positionHigh p) k ≤ k/2-2 :=
  position_reserves_of_cutoff h

private noncomputable def baseWidth := max CoprimeBox.eventually_valid.choose
  (eventually_atTop.mp (CRTBudget.eventually_layout_room 0 0)).choose

/-- The last degree is a fixed polynomial bound on the compact serialized
CRT ticket. It does not vary with the outer template or any guessed reserve. -/
noncomputable def addressCut (ticketDegree : ℕ) (p : Guess) :=
  baseWidth + rawPrecisionCutoff (signedTemplate p) + FixedLayer.walshTemplateCut (positionCutoff p) (signedTemplate p) +
    boxCutoff (exterior p) 2 +
    boxCutoff (4*exterior p*(ticketDegree+1)) 0

theorem addressCut_computable (degree : ℕ) : Computable (addressCut degree) := by
  apply Primrec.nat_add.to_comp.comp
  · apply Primrec.nat_add.to_comp.comp
    · exact Primrec.nat_add.to_comp.comp
        (Primrec.nat_add.to_comp.comp (.const baseWidth) (rawPrecisionCutoff_primrec.to_comp.comp signedTemplate_computable))
        (FixedLayer.walshTemplateCut_computable signedTemplate_computable positionCutoff_pr.to_comp)
    · exact boxCutoff_primrec.to_comp.comp exterior_pr.to_comp (.const 2)
  · apply boxCutoff_primrec.to_comp.comp _ (.const 0)
    exact Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp (.const 4) exterior_pr.to_comp) (.const _)

noncomputable def inputCut (ticketDegree : ℕ) (p : Guess) := widthGuard 2 (addressCut ticketDegree p)

theorem inputCut_computable (degree : ℕ) : Computable (inputCut degree) :=
  (widthGuard_primrec 2).to_comp.comp (addressCut_computable degree)

theorem inputCut_ge_two (degree : ℕ) (p : Guess) : 2 ≤ inputCut degree p := (widthGuard_ge ..).1

theorem accepted_width {degree n : ℕ} {p : Guess} (h : inputCut degree p ≤ n) :
    Directory n ∧ 1024+rawPrecisionCutoff (signedTemplate p) ≤ addressBits n ∧
      SynchronizedPermutationBudget.BoxPasses (addressBits n) (exterior p) 2 := by
  have big := widthGuard_addressBits h
  dsimp [addressCut] at big
  have hbase : CoprimeBox.eventually_valid.choose ≤ baseWidth := le_max_left ..
  have valid := CoprimeBox.eventually_valid.choose_spec (addressBits n) (by omega)
  exact ⟨valid,by omega,boxPasses_of_cutoff (by omega) valid⟩

theorem accepted_walsh {degree n : ℕ} {p : Guess} (h : inputCut degree p ≤ n) :
    4 ≤ (box n).length ∧ FixedLayer.walshTemplateCut (positionCutoff p) (signedTemplate p) ≤ addressBits n := by
  obtain ⟨shape,hk,_⟩ := accepted_width h
  have big := widthGuard_addressBits h
  dsimp [addressCut] at big
  exact ⟨SynchronizedBlocks.four_le_length shape (SynchronizedBlocks.three_width_lt (by omega)),by omega⟩

theorem accepted_native {degree n : ℕ} {p : Guess} (h : inputCut degree p ≤ n)
    {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) {b depth slot Q : ℕ}
    (sel : Fin b → Fin (CRTTable.targetOrder (box n).length depth).length)
    (card : b ≤ blocksPerBatch (addressBits n) 4 (CRTBudget.stride (addressBits n)))
    (scale : Q ≤ (addressBits n+1)^degree) :
    CRTBudget.NativeAdmission sel (addressBits n) slot (addressBits n/16) (exterior p) Q ρ := by
  let k := addressBits n
  have big := widthGuard_addressBits h
  dsimp [addressCut] at big
  have shape := (accepted_width h).1
  have bas : (eventually_atTop.mp (CRTBudget.eventually_layout_room 0 0)).choose ≤ baseWidth := le_max_right ..
  have guard := ((eventually_atTop.mp (CRTBudget.eventually_layout_room 0 0)).choose_spec k
    (by dsimp [k]; omega)).1
  have hk : 16 ≤ k := by dsimp [k]; omega
  have hd : boxCutoff (4*exterior p*(degree+1)) 0 ≤ k := by dsimp [k]; omega
  have room := boxRoom_of_cutoff hd
  have wide : BoxScale.width k ≤ CRTBudget.stride k := le_max_right ..
  have res : 32*(k/16+payloadBits 2 k) ≤ 3*k := by
    unfold SynchronizedPermutationBudget.width at room
    unfold payloadBits
    omega
  have half : 2*BoxScale.width k ≤ k := by omega
  apply CRTBudget.native_admission (k := k) (by omega) h₀ h₁ shape sel half guard card res (by omega)
  apply (CRTBudget.payload_of_polynomial_scale (k := k) (D := exterior p) (by omega) scale).trans
  have g := room.2
  unfold payloadBits at g ⊢
  have e : 4*exterior p*(degree+1)*Nat.clog 2 (k+1) = 4*(exterior p*(degree+1)*Nat.clog 2 (k+1)) := by ring
  rw [e] at g
  omega

/-- A constant coefficient in the physical ticket-size estimate can be
absorbed in the single hardwired exponent used by the executable guard. -/
theorem polynomial_ticket {C e k Q : ℕ} (hk : 1 ≤ k) (hQ : Q ≤ C*(k+1)^e) :
    Q ≤ (k+1)^(C+e) := by
  rw [pow_add]
  exact hQ.trans (Nat.mul_le_mul_right _ ((Nat.lt_two_pow_self (n := C)).le.trans
    (Nat.pow_le_pow_left (by omega) C)))

theorem directory (e : ℕ) (p : Guess) (i : LargeInput (inputCut e p)) :
    Directory i.val.width := (accepted_width i.property).1

theorem axes (e : ℕ) (p : Guess) (i : LargeInput (inputCut e p)) :
    4 ≤ (box i.val.width).length := (accepted_walsh i.property).1

theorem width (e : ℕ) (p : Guess) (i : LargeInput (inputCut e p)) :
    1024 ≤ addressBits i.val.width := by
  have := (accepted_width i.property).2.1
  omega

end FixedCandidate.CandidateParameters

end NearSquareRoot
end Computability
end OAI
