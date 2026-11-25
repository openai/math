import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigit
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxMultiplication
import OAI.Computability.NearSquareRoot.ScheduleStagingCall
import Batteries.Tactic.OpenPrivate

/-! # Resource bounds for a literal multiplication digit call -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open CommonAlphabet

/-- Extend the certified product to the operand type expected by the chunk
scheduler. Only positive equal-width inputs can enter a digit call. -/
def digitProduct (z : MultiplicationInput → List Bool) (v : ChunkLoop.Operands) : Word :=
  if h : v.1.length = v.2.length ∧ 0 < v.1.length then z ⟨⟨v,h.1⟩,h.2⟩ else []

theorem digitProduct_val (z : MultiplicationInput → List Bool) (v : ChunkTask.EqualWords) :
    digitProduct z v.val = z ⟨⟨v.val,v.property.1⟩,v.property.2⟩ :=
  dite_eq_left v.property

theorem digitProduct_spec {z : MultiplicationInput → List Bool}
    (correct : ∀ i, (z i).length = 2*i.width ∧ bitValue (z i) = bitValue i.operands.1 * bitValue i.operands.2)
    (v : ChunkTask.EqualWords) :
    (digitProduct z v.val).length = 2*v.val.1.length ∧
      bitValue (digitProduct z v.val) = bitValue v.val.1 * bitValue v.val.2 := by
  rw [digitProduct_val]
  exact correct _

open private source_run decode_blank decode_bit from OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPublicRun

private theorem literal_time {A : Type} (c : CommonAlphabet.Code A) (H t : ℕ) (x y z : List Bool) :
    Pipeline.expandSteps c.width x y+1+(2*clock c t+3)+1+Pipeline.compactSteps c.width z ≤
      (32*(c.width+H+1))*(t+x.length+y.length+z.length+1) := by
  dsimp only [Pipeline.expandSteps,Pipeline.compactSteps,clock]
  ring_nf
  omega

private theorem literal_space (w H S : ℕ) (x y z : List Bool) :
    2*(Pipeline.expandSteps w x y+1)+H+(2*((2*(1+5*w)+1)*S)+H)+(2*(Pipeline.compactSteps w z+1)+H) ≤
      (32*(w+H+1))*(S+x.length+y.length+z.length+1) := by
  dsimp only [Pipeline.expandSteps,Pipeline.compactSteps]
  ring_nf
  omega

/-- A rigid candidate digit machine has one constant for all positive equal-width
input pairs. Time is affine in the body time and word length, and visited cells
are affine in the word length. -/
theorem digit_computes [Fintype Ltr] {R : ℕ} (hR : 0 < R) {p : Cmd} (bound : CommonRegisters.Within R p)
    {T : ℕ → ℕ} {S C : ℕ} {z : MultiplicationInput → List Bool}
    (body : MultiplicationBody p T S C z) (length : ∀ i, (z i).length = 2*i.width) :
    ∃ E : ℕ, 0 < E ∧ StagingCall.Computes
      (digitMachine hR (multiplyWrap p) (within_multiplyWrap hR bound))
      (digitEntry R (multiplyWrap p)) (digitProduct z) (fun n => E*(T n+n+1)) (fun n => E*(n+1)) := by
  let cmd := multiplyWrap p
  let c := blockCode ltrNumbering cmd
  let H := Fintype.card (Pipeline.Index (Option (FixedTapes R)))
  let F := 32*(c.width+H+1)
  let D := C*(S+1)+128
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
  have hn : i.width = n := rfl
  have hz : (z i).length = 2*n := length i
  obtain ⟨u,ub,wrapped⟩ := multiplyWrap_run body i (length i)
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
    have emptyBound : (R+2)*(4*(D*n)+6)+n+n+2*n+1 ≤ L*(n+1) := by
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
