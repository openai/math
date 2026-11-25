import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigitArenaBody
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigitRun

/-! # Digit machine execution for a width-dependent stack-space bound -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open CommonAlphabet

open private source_run decode_blank decode_bit from OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPublicRun
open private literal_time literal_space from OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigitRun

/-- A width-dependent stack budget passes through the literal input, execution and
output phases with an additive linear term for the operand and result tapes. -/
theorem digit_computes_arena [Fintype Ltr] {R : ℕ} (hR : 0 < R) {p : Cmd} (bound : CommonRegisters.Within R p)
    {T S : ℕ → ℕ} {C : ℕ} {z : MultiplicationInput → List Bool}
    (body : ArenaBody p T S C z) (length : ∀ i, (z i).length = 2*i.width) :
    ∃ E : ℕ, 0 < E ∧ StagingCall.Computes
      (digitMachine hR (multiplyWrap p) (within_multiplyWrap hR bound))
      (digitEntry R (multiplyWrap p)) (digitProduct z) (fun n => E*(T n+n+1)) (fun n => E*(S n+n+1)) := by
  let cmd := multiplyWrap p
  let c := blockCode ltrNumbering cmd
  let H := Fintype.card (Pipeline.Index (Option (FixedTapes R)))
  let F := 32*(c.width+H+1)
  let D := C+64
  let K := 2*(C+46)+8
  let L := (R+2)*(4*D+6)+5
  let E := F*max K L
  refine ⟨E,Nat.mul_pos (by dsimp [F]; omega)
    (lt_of_lt_of_le (show 0 < K by dsimp [K]; omega) (le_max_left _ _)),?_⟩
  intro v
  let i : MultiplicationInput := ⟨⟨v.val,v.property.1⟩,v.property.2⟩
  let n := v.val.1.length
  have hx : i.operands.1.length = n := rfl
  have hy : i.operands.2.length = n := v.property.1.symm
  have hz : (z i).length = 2*n := length i
  obtain ⟨u,ub,wrapped⟩ := multiplyWrap_arena_run body i (length i)
  obtain ⟨done,tr,halt,word,area⟩ :=
    source_run hR cmd (within_multiplyWrap hR bound) i.operands.1 i.operands.2 (z i) wrapped
      (Schoolbook.raw_zero _)
  obtain ⟨t,y,time,hist,stop,output,space⟩ :=
    Pipeline.literal_from_source c (fun b => symbol cmd (.bit b)) (symbol cmd .sep) none
      (oneHot_blank _ _) _ (decode_blank cmd) (decode_bit cmd) (fixedInput hR) none
      (paddedRule hR cmd (within_multiplyWrap hR bound)) (entry cmd)
      i.operands.1 i.operands.2 (z i) done tr halt word area
  have time' := time.trans (literal_time c H _ _ _ _)
  have timeIn : 2*u+1+(z i).length+i.operands.1.length+i.operands.2.length+(z i).length+1 ≤
      K*(T n+n+1) := by
    rw [hz,hx,hy]
    change u ≤ (C+46)*(T n+n+1) at ub
    dsimp only [K]
    rw [Nat.add_mul, Nat.mul_assoc]
    omega
  have totalTime := time'.trans (Nat.mul_le_mul_left F timeIn)
  have totalTime' : t ≤ E*(T n+n+1) := totalTime.trans (by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left F (le_max_left K L)))
  refine ⟨t,totalTime',y,hist,stop,?_,?_⟩
  · rwa [digitProduct_val]
  · obtain ⟨cells,count,cover⟩ := space
    refine ⟨cells,count.trans ?_,cover⟩
    apply (literal_space c.width H _ i.operands.1 i.operands.2 (z i)).trans
    have emptyBound : (R+2)*(4*(D*(S n+n+1))+6)+n+n+2*n+1 ≤ L*(S n+n+1) := by
      dsimp only [L]
      ring_nf
      omega
    simp only [hx,hy,hz,max_self]
    exact (Nat.mul_le_mul_left F emptyBound).trans (by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left F (le_max_right K L)))

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
