import OAI.Hierarchy.DescentSeedCompleteAfterAt
import OAI.Hierarchy.DescentSeedNativeInvoice

namespace OAI
/-! # The two separately scheduled startup programs in the final host price -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentInitialHost DescentSeedInitialTable
open DescentPackedSeed DescentDyadicSpan DescentColonies Catalyst Filter
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] (D : PoweredGadget F) (op : RotorSpec)

theorem complete_after_invoice (t f g reset drift degreeMax quota : ℕ) :
    ∃τ₀ : ℕ,∃B₀ : ℕ → ℕ,∀τ B factor,τ₀ ≤ τ → B₀ τ ≤ B →
      ∀ᶠ h : ℕ in atTop,CompleteAfterAt D op t f g reset drift degreeMax quota τ B factor h :=by
  obtain ⟨τ₀,B₀,invoice⟩:=complete_invoice D op t f g reset drift degreeMax quota
  refine ⟨τ₀,B₀,?_⟩
  intro τ B factor long enough
  filter_upwards [invoice τ B factor long enough] with h paid
  let J:=Nat.log 2 h/(2*B)
  dsimp only [CompleteAfterAt]
  intro M degree w base field wire hist header ambient degreeFit word cp pin X wide digits budget E lower
  let S:=stageNumbers D t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let q₀:=2^Nat.clog 2 (NativeBranch.localLimit D S)
  let split:=NativeBranch.binLimit (k:=k) S
  let U:=D.b^(t*J)*D.b
  let q:=q₀*U
  let p:=split*(h/(16*(q*split)))
  let l:=selectedLayout D S h k (tail τ J) g p drift degree f quota base field wire hist
  let Z:=S.grainAt D.b p 0
  let flags:=DescentWideSeedFlags.check X S.copies l.seedWidth h w
  let boot:=Input.completeAfter D op X digits wide l header h Z w
  let n:=rows X S.copies l.seedWidth h
  let T:=Input.completeTicks D op X wide l h Z w (k:=k) (S:=S)
  let amount:=(4+(n+1)*66+7*DescentStaticWordColumn.names flags)+(T+7*DescentStaticWordColumn.names boot)
  have full := paid M degree w base field wire hist header ambient degreeFit word X wide digits
  have charged : amount*(w+1)*2^J ≤ 4*(M*(S.copies*p)) :=by
    change (4+(n+1)*66+T+7*DescentStaticWordColumn.names
      (Input.selectedProgram D op X digits wide l header h Z (w:=w)))*(w+1)*2^J ≤ _ at full
    rw [Input.selectedProgram,DescentStaticWordColumn.names_seq] at full
    apply le_trans (b:= (4+(n+1)*66+T+7*(DescentStaticWordColumn.names flags+
      DescentStaticWordColumn.names boot))*(w+1)*2^J)
    · apply le_of_eq
      dsimp only [amount]
      ring
    · exact full
  have bins : p≤l.seedWidth:=
    (Nat.le_mul_of_pos_right p (pow_pos D.base_pos _)).trans (Nat.le_mul_of_pos_right _ D.base_pos)
  calc
    amount*(budget+1)*2^J ≤ amount*(w+1)*2^J := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.succ_le_succ lower))
    _ ≤ 4*(M*(S.copies*p)) := charged
    _ = (4*(S.copies*p))*M := by ring
    _ ≤ 4*(S.copies*l.seedWidth)*(M+2^J*E) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ bins)) (Nat.le_add_right ..)

end
end Hierarchy.DescentDatedSeedStartup

end OAI
