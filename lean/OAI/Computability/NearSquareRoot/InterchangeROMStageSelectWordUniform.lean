import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectWordState
import OAI.Computability.NearSquareRoot.InterchangeROMStageVolume

/-! # One computable movement coefficient for every scalar row of a chosen stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom
  InterchangeAddress InterchangeROMStage InterchangeROMTable Space

/-- The clock for a row depends on its record geometry and an absolute
polynomial degree. It is the same for every chart operand and every value. -/
def rowMass (e : ℕ) (hdr : InterchangeROMAddress.Header) (N width : ℕ) :=
  (N+1)*(width+1+(size hdr+1)^e)

def rowFactor (M C K e : ℕ) (x : Data) :=
  moveWeightMax M C K e x * (2*(2*(x.modulusIndex+1)+2)+1)

theorem computable_rowFactor (M C K e : ℕ) : Computable (rowFactor M C K e) := by
  have hp : Computable fun x : Data => x.modulusIndex+1 :=
    (Primrec.succ.comp (Primrec.nat_sub.comp (primrec_header 0) (.const 1))).to_comp
  exact Primrec.nat_mul.to_comp.comp (computable_moveWeightMax M C K e)
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (.const 2) (Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (.const 2) hp) (.const 2))) (.const 1))

private theorem geom {p : ℕ} [NeZero p] {A D : Type} (rows : Series A) (pay : Series D)
    (x : A → D → ZMod p) (e : ℕ) (hdr : InterchangeROMAddress.Header) :
    let u := stripe rows fun a => stripe pay fun d => numeral (x a d).val
    OpcodeProgram.geometry e hdr rows.count u u ≤
      (2*(2*p+2)+1)*rowMass e hdr rows.count pay.count := by
  let N := rows.count
  let L := pay.count
  let W := rowMass e hdr N L
  let u := stripe rows fun a => stripe pay fun d => numeral (x a d).val
  have cells : N*(L+1)+1 ≤ W := by
    calc N*(L+1)+1 ≤ (N+1)*(L+1) := by nlinarith
         _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have front : (N+1)*(size hdr+1)^e ≤ W := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  have hu := InterchangeROMStageVolume.stream_size rows (fun _ => pay) L (fun _ => le_rfl) x
  change u.count+1 ≤ (N*(L+1)+1)*(2*p+2) at hu
  have hv := hu.trans (Nat.mul_le_mul_right (2*p+2) cells)
  change u.count+u.count+1+(N+1)*(size hdr+1)^e ≤ (2*(2*p+2)+1)*W
  calc _ ≤ W*(2*p+2)+W*(2*p+2)+W := by omega
       _ = _ := by ring

/-- Every local move uses the same computable multiple of a single mass.
The recursive child list, its exact price, its data invariant, and its
per-child recursive time and peak accounting are preserved. -/
theorem selected_state_uniform : ∃ M C K e : ℕ, 1 ≤ e ∧ ∀ {j threshold f l : ℕ}
    {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
    (h : Valid j threshold x) (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S)
    {D : Type} (pay : Series D) (v : x.Wide P G S f D)
    (k : Fin 6) (z : (roleRealization h).Boundary (Frame.Realization.routePos k+1)) (d : x.WideIndex),
    let r := roleRealization h
    let n := Frame.Realization.routePos k
    let op := r.moveAt k z
    let μ := r.operand op
    let hdr := InterchangeROMAddress.header f P G S
    let rows := x.stageRows P G S f
    let src := stripe rows (stateRecord h pay v n (r.srcAt k z) d)
    let dst := stripe rows (stateRecord h pay v (n+1) z d)
    let F := rowFactor M C K e x * rowMass e hdr rows.count pay.count
    ∃ qs, qs.length = wordPrice h op ∧
      (∀ q∈qs, OpcodeProgram.Valid (b:=x.b) f rows.count l P G S (x.recordGood pay) q) ∧
      InterchangeROMSequence.Step (Request.job x.b) (x.moveCmd μ) (send hdr) src dst qs F F F := by
  obtain ⟨M,C,K,e,he,run⟩ := selected_state_word_run
  refine ⟨M,C,K,e,he,?_⟩
  intro j threshold f l x nz hp h P G S p g s D pay v k z d
  let r := roleRealization h
  let n := Frame.Realization.routePos k
  let μ := r.operand (r.moveAt k z)
  let hdr := InterchangeROMAddress.header f P G S
  let rows := x.stageRows P G S f
  let src := stripe rows (stateRecord h pay v n (r.srcAt k z) d)
  obtain ⟨qs,hlen,valid,step⟩ := run (l:=l) h P G S p g s pay v k z d
  refine ⟨qs,hlen,valid,?_⟩
  have H : moveWeight M C K e x μ * OpcodeProgram.geometry e hdr rows.count src src ≤
      rowFactor M C K e x * rowMass e hdr rows.count pay.count := by
    calc _ ≤ moveWeightMax M C K e x * ((2*(2*(x.modulusIndex+1)+2)+1)*
            rowMass e hdr rows.count pay.count) :=
            Nat.mul_le_mul (moveWeight_le M C K e x μ) (geom rows pay
              (fun a k => stageStates h v n (r.srcAt _ z) (a,k) d) e hdr)
         _ = _ := (Nat.mul_assoc ..).symm
  exact step.mono H H H

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
