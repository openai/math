import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectWordUniform
import OAI.Computability.NearSquareRoot.InterchangeROMStageStep

/-! # Computable stage costs at ordinary and enlarged record widths -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROMStage InterchangeROMStageVolume InterchangeROMRepair

def chartFactor (M C K e : ℕ) (x : Data) :=
  stageFactor x.stageParameters + localFactor x.stageParameters +
    (fieldCount x.roleFrame (Raw.rowCount x.m)+1)*(4*rowFactor M C K e x)+1

theorem computable_chartFactor (M C K e : ℕ) : Computable (chartFactor M C K e) := by
  have count := primrec_fieldCount.comp primrec_roleFrame (Raw.primrec_rowCount.comp (primrec_header 2))
  have factors := Primrec.nat_add.comp (primrec_stageFactor.comp primrec_stageParameters)
    (primrec_localFactor.comp primrec_stageParameters)
  exact Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp factors.to_comp
    (Primrec.nat_mul.to_comp.comp ((Primrec.succ.comp count).to_comp)
      (Primrec.nat_mul.to_comp.comp (.const 4) (computable_rowFactor M C K e)))) (.const 1)

/-- The three actual charges in the selected stage are covered at once. -/
theorem chart_bounds (M C K e : ℕ) (x : Data) {m U B : ℕ}
    (hm : m ≤ B) (hU : U ≤ 4*B) (hB : 1 ≤ B) :
    let F := rowFactor M C K e x * U
    let bound := chartFactor M C K e x * B
    stageFactor x.stageParameters*m + fieldCount x.roleFrame (Raw.rowCount x.m)*F ≤ bound ∧
    localFactor x.stageParameters*m + F ≤ bound ∧ localFactor x.stageParameters*m + F+1 ≤ bound := by
  let s := stageFactor x.stageParameters
  let t := localFactor x.stageParameters
  let n := fieldCount x.roleFrame (Raw.rowCount x.m)
  let r := rowFactor M C K e x
  have hs := Nat.mul_le_mul_left s hm
  have ht := Nat.mul_le_mul_left t hm
  have hr : r*U ≤ 4*r*B := by
    calc r*U ≤ r*(4*B) := Nat.mul_le_mul_left _ hU
         _ = _ := by ring
  have hn := Nat.mul_le_mul_left n hr
  have eqn : chartFactor M C K e x*B = s*B + t*B + n*(4*r*B) + 4*r*B + B := by
    change (s+t+(n+1)*(4*r)+1)*B = _
    ring
  dsimp only
  change s*m+n*(r*U) ≤ _ ∧ t*m+r*U ≤ _ ∧ t*m+r*U+1 ≤ _
  rw [eqn]
  omega

private theorem chart_mass_of (e : ℕ) (hdr : InterchangeROMAddress.Header) (N pay width : ℕ)
    (hN : 0 < N) (hpay : pay ≤ width) (hpower : pay+1+(size hdr+1)^e ≤ 2*(width+1)) :
    let m := mass (send hdr) N pay
    let U := rowMass e hdr N pay
    let B := mass (send hdr) N width
    m ≤ B ∧ U ≤ 4*B ∧ 1 ≤ B := by
  have amount := Nat.mul_le_mul_left N (Nat.add_le_add_right hpay 1)
  have hu : rowMass e hdr N pay ≤ 4*(N*(width+1)) := by
    calc (N+1)*(pay+1+(size hdr+1)^e) ≤ (2*N)*(2*(width+1)) :=
          Nat.mul_le_mul (by omega) hpower
         _ = _ := by ring
  unfold InterchangeROMStageVolume.mass
  dsimp only
  omega

/-- With the geometry polynomial included in the width, no thickness
hypothesis is required. -/
theorem chart_mass_enlarged (e : ℕ) (hdr : InterchangeROMAddress.Header) (N pay width : ℕ)
    (hN : 0 < N) (hpay : pay ≤ width) :
    let m := mass (send hdr) N pay
    let U := rowMass e hdr N pay
    let B := mass (send hdr) N (width+(size hdr+1)^e)
    m ≤ B ∧ U ≤ 4*B ∧ 1 ≤ B :=
  chart_mass_of e hdr N pay _ hN (by omega) (by omega)

/-- A sufficiently wide record pays the same costs at its original width. -/
theorem chart_mass_thick (e : ℕ) (hdr : InterchangeROMAddress.Header) (N pay width : ℕ)
    (hN : 0 < N) (hpay : pay ≤ width) (hpow : (size hdr+1)^e ≤ width+1) :
    let m := mass (send hdr) N pay
    let U := rowMass e hdr N pay
    let B := mass (send hdr) N width
    m ≤ B ∧ U ≤ 4*B ∧ 1 ≤ B :=
  chart_mass_of e hdr N pay width hN hpay (by omega)

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
