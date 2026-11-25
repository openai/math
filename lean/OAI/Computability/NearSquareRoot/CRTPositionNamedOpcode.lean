import OAI.Computability.NearSquareRoot.CRTPositionNamedSum
import OAI.Computability.NearSquareRoot.CRTPositionNamedSingleton
import OAI.Computability.NearSquareRoot.CRTPositionNamedSwap
import OAI.Computability.NearSquareRoot.CRTPositionNamedPacked

/-! # A single effective source for the native position instruction -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Loom CommonRegisters GeneratorSyntax

private theorem coarseTemplate : OpcodeTemplate swapChunks := by
  let X := Call swapChunks
  let r := Call.regime swapChunks
  have code : r.Has (fun x : X => (false,x.operand)) := Call.opcodeHas
  have run := swapNativeProgram (r:=r) (q:=fun x : X => x.operand) (k:=Call.k)
    (u:=fun x : X => Series.natural x.width) (l:=Call.width) (f:=Call.data)
    (code.ez Easy.snd) Call.widthHas (fun _ => by simp)
  have eq (x : X) (a : Block 2 x.k) :
      swapNative x.k x.operand a = nativeOp x.k (guardWidth x.k) (swapChunks x.operand) a := by
    apply prefixBit_injective x.k
    rw [nativeOp_bits]
    exact swapNative_bits x.k x.operand.1 x.operand.2 x.legal a
  obtain ⟨t,run⟩ := run
  refine ⟨t,?_⟩
  intro c ρ hρ ok
  have step := run c ρ hρ ok
  simp only [eq] at step
  exact step

/-- The same command tree handles every valid interchange backend. Each of its
three tests reads a sum-constructor bit from the physical instruction header. -/
theorem opcodeTemplate : OpcodeTemplate id := by
  apply opcodeTemplate_sum id Call.opcodeHas coarseTemplate
  refine opcodeTemplate_sum _ ?_ packedProgram ?_
  · have code : (Call.regime (id ∘ Sum.inr)).Has (fun x => (true,x.operand)) := Call.opcodeHas
    exact code.ez Easy.snd
  refine opcodeTemplate_sum _ ?_ highCnotTemplate tailSwapTemplate
  have code : (Call.regime ((id ∘ Sum.inr) ∘ Sum.inr)).Has (fun x => (true,true,x.operand)) := Call.opcodeHas
  exact code.ez (Easy.snd.compose Easy.snd)

noncomputable def opcodeCmd (rectangle : Cmd) : Cmd := opcodeTemplate.choose.eval rectangle

theorem opcodeCmd_runs {ρ : ℝ} {rect : Cmd} (hρ : 0 ≤ ρ) (run : Effective.rectContract rect ρ) :
    OpAt (opcodeCmd rect) ρ id := opcodeTemplate.choose_spec rect ρ hρ run

theorem opcodeCmd_effective {P : Type} [Primcodable P] {rect : P → Cmd} (h : GeneratorSyntax.Effective ltr rect) :
    GeneratorSyntax.Effective ltr (fun p => opcodeCmd (rect p)) := opcodeTemplate.choose.effective h

theorem opcodeCmd_within (R : ℕ) : ∃ B, 0 < B ∧ ∀ c, Within R c → Within B (opcodeCmd c) :=
  opcodeTemplate.choose.within R

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
