import OAI.Computability.NearSquareRoot.SynchronizedLowerWord
import OAI.Computability.NearSquareRoot.SynchronizedAxisProgram
import OAI.Computability.NearSquareRoot.SynchronizedAxisSemantics
import OAI.Computability.NearSquareRoot.SynchronizedControlledWalsh
import OAI.Computability.NearSquareRoot.SynchronizedHalfTables

/-! # Exact action of the expanded, physically encoded slot list -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord

open IntegerMultiplication.Code Matrix
open scoped Matrix
noncomputable section

variable {a k : ℕ} [NeZero a]

/-- A phase lookup outside an internal radix bit range defaults to the identity. -/
def bitLookup (arg : ℕ) (f : Fin k → Matrix (Ambient k) (Ambient k) ℂ) : Matrix (Ambient k) (Ambient k) ℂ :=
  if h : arg < k then f ⟨arg,h⟩ else 1

/-- Actual full-array matrices, including the fixed identity phases in idle halves. -/
def lowerDecode (har : a ≤ 2^k) (tag arg : ℕ) : Matrix (Ambient k) (Ambient k) ℂ :=
  if tag < 10 then decode har tag arg else
  let z := calibratedMultiplier a (2^k)
  match tag-10 with
  | 0 => physicalHalfWalsh
  | 1 => diagonal (physicalDilationPhase z 0 1)
  | 2 => diagonal (physicalDilationPhase z 2 3)
  | 3 => diagonal (physicalDilationPhase z 4 5)
  | 4 => bitLookup arg bothHalvesWalsh
  | 5 => bitLookup arg fun i => diagonal (controlledPhase i 0 1)
  | 6 => bitLookup arg fun i => diagonal (controlledPhase i 2 3)
  | 7 => bitLookup arg fun i => diagonal (controlledPhase i 4 5)
  | _ => 1

def evalSlot (har : a ≤ 2^k) (op : Inst) : Matrix (Ambient k) (Ambient k) ℂ :=
  let u := lowerDecode har op.1.length op.2.1.length
  if op.2.2 then uᴴ else u

def slotProd (har : a ≤ 2^k) (w : List Inst) := (w.map (evalSlot har)).prod

private theorem evalSlot_inst (har : a ≤ 2^k) (tag : ℕ) (arg : Tally) :
    evalSlot har (inst tag arg) = lowerDecode har tag arg.length := by simp [inst, evalSlot]

private theorem evalSlot_flip (har : a ≤ 2^k) (x : Inst) :
    evalSlot har (flip x) = (evalSlot har x)ᴴ := by
  rcases x with ⟨t,s,b⟩
  cases b <;> simp [flip, evalSlot]

private theorem slot_append (har : a ≤ 2^k) (w v : List Inst) :
    slotProd har (w ++ v) = slotProd har w * slotProd har v := by simp [slotProd]

private theorem slot_adj (har : a ≤ 2^k) (w : List Inst) :
    slotProd har (adj w) = (slotProd har w)ᴴ := by
  induction w with
  | nil => simp [slotProd, adj]
  | cons x w ih =>
    rw [show adj (x::w) = adj w ++ [flip x] by simp [adj], slot_append, ih]
    simp [slotProd, evalSlot_flip]

private theorem three_controlled (har : a ≤ 2^k) (arg : Tally) :
    slotProd har (threeRounds 14 15 arg) = decode har 2 arg.length := by
  simp only [slotProd, threeRounds, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, evalSlot_inst]
  by_cases hi : arg.length < k
  · simpa [lowerDecode, bitLookup, hi, decode, Matrix.mul_assoc] using
      (firstHalf_butterfly_threeWalsh (k := k) ⟨arg.length,hi⟩).symm
  · simp [lowerDecode, bitLookup, hi, decode]

private theorem three_dilation (har : a ≤ 2^k) (arg : Tally) :
    slotProd har (threeRounds 10 11 arg) = decode har 3 arg.length := by
  simp only [slotProd, threeRounds, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, evalSlot_inst]
  simpa [lowerDecode, decode, Matrix.mul_assoc] using
    (physical_dilation (calibratedMultiplier a (2^k)) (fun i => (calibratedMultiplier_lt_half (NeZero.pos a) i).le)).symm

theorem lowerInst_sound (har : a ≤ 2^k) (x : Inst) (h : x.1.length < 10) :
    slotProd har (lowerInst x) = evalInst har x := by
  rcases x with ⟨t,s,b⟩
  change t.length < 10 at h
  by_cases h₂ : t.length = 2
  · cases b <;> simp [lowerInst, evalInst, h₂, slot_adj, three_controlled]
  by_cases h₃ : t.length = 3
  · cases b <;> simp [lowerInst, evalInst, h₃, slot_adj, three_dilation]
  · cases b <;> simp [lowerInst, evalInst, h₂, h₃, evalSlot, lowerDecode, slotProd, h]

theorem lower_sound (har : a ≤ 2^k) (w : List Inst) (h : ∀ x ∈ w, x.1.length < 10) :
    slotProd har (lower w) = evalWord har w := by
  induction w with
  | nil => simp [slotProd, lower, evalWord]
  | cons x w ih =>
    rw [show lower (x :: w) = lowerInst x ++ lower w by simp [lower], slot_append,
      lowerInst_sound _ _ (h x (by simp)), ih (fun y hy => h y (by simp [hy]))]
    simp [evalWord]

/-- The code produced by expanding the charged setup word now consists of phase,
permutation, and unconditional Walsh stages, and acts correctly on the full fiber. -/
theorem loweredRestored_correct (hr : 2*a-1 ≤ 2^k) (har : a ≤ 2^k) :
    slotProd har (loweredRestored (tally k)) = extend (activeFiber har) (normalizedFourier a) := by
  rw [loweredRestored, lower_sound har _ (fun x hx => Nat.lt_succ_of_le (restored_fieldsBounded _ _ hx).1)]
  exact eval_restored hr har

end
end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
