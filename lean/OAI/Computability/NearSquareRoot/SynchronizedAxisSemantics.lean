import OAI.Computability.NearSquareRoot.SynchronizedAxisWord
import OAI.Computability.NearSquareRoot.SynchronizedShortAxis

/-! # Semantics of the encoded short-axis instructions

Decoding each record emitted by `AxisWord.restored` gives the calibrated chirp
dilation, reflections, and phase diagonals on the actual doubled address space.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Axon
open Matrix SynchronizedRestoration
open scoped Matrix
noncomputable section

variable {a k : ℕ} [NeZero a]
abbrev Ambient (k : ℕ) := Fin (2^k) ⊕ Fin (2^k)

/-- Exact matrix for the forward orientation of each encoded operation. -/
def decode (har : a ≤ 2^k) (tag arg : ℕ) : Matrix (Ambient k) (Ambient k) ℂ :=
  let E := activeFiber har
  match tag with
  | 0 => firstHalf (radixReverseMatrix k)
  | 1 => if h : arg < k then firstHalf (radixGateMatrix k (.twiddle ⟨arg,h⟩)) else 1
  | 2 => if h : arg < k then firstHalf (radixGateMatrix k (.butterfly ⟨arg,h⟩)) else 1
  | 3 => dilation (calibratedMultiplier a (2^k))
  | 4 => extend E (bluesteinDiagonal a)
  | 5 => (2 : ℝ) • (E * Eᴴ) - 1
  | 6 => 1 - (2 : ℝ) • (E * Eᴴ)
  | 7 => extend E (diagonal fun i : Fin a => chirp a i.val)
  | 8 => extend E (diagonal (chirpSpectrum a))
  | 9 => extend E (diagonal fun i : Fin a => chirp a (-(i.val : ℤ)))
  | _ => 1

def evalInst (har : a ≤ 2^k) (op : Inst) : Matrix (Ambient k) (Ambient k) ℂ :=
  let u := decode har op.1.length op.2.1.length
  if op.2.2 then uᴴ else u

def evalWord (har : a ≤ 2^k) (w : List Inst) := (w.map (evalInst har)).prod

theorem eval_inst (har : a ≤ 2^k) (tag : ℕ) (arg : Tally) :
    evalInst har (inst tag arg) = decode har tag arg.length := by simp [inst, evalInst]

theorem eval_flip (har : a ≤ 2^k) (x : Inst) : evalInst har (flip x) = (evalInst har x)ᴴ := by
  rcases x with ⟨t,s,b⟩
  cases b <;> simp [flip, evalInst]

theorem eval_append (har : a ≤ 2^k) (w v : List Inst) :
    evalWord har (w ++ v) = evalWord har w * evalWord har v := by simp [evalWord]

theorem eval_single (har : a ≤ 2^k) (x : Inst) : evalWord har [x] = evalInst har x := by simp [evalWord]

theorem eval_adj (har : a ≤ 2^k) (w : List Inst) : evalWord har (adj w) = (evalWord har w)ᴴ := by
  induction w with
  | nil => simp [evalWord, adj]
  | cons x w ih =>
    rw [show adj (x::w) = adj w ++ [flip x] by simp [adj], eval_append, ih, eval_single, eval_flip]
    simp [evalWord]

theorem eval_repeat (har : a ≤ 2^k) (w : List Inst) (n : ℕ) :
    evalWord har (List.replicate n w).flatten = (evalWord har w)^n := by
  induction n with
  | zero => simp [evalWord]
  | succ n ih => simp only [List.replicate_succ, List.flatten_cons, eval_append, ih, pow_succ']

private theorem eval_radix_suffix (har : a ≤ 2^k) (is : List (Fin k)) :
    ((is.reverse.flatMap (fun i => [inst 1 (tally i.val), inst 2 (tally i.val)])).map (evalInst har)) =
      ((Radix.word is).map (fun g => firstHalf (radixGateMatrix k g))) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp [Radix.word, List.flatMap_append, ih, eval_inst, decode, i.isLt]

theorem eval_radix (har : a ≤ 2^k) :
    evalWord har (radix (tally k)) = firstHalf (normalizedFourier (2^k)) := by
  have hline : Iter.lineup (tally k) = (layers k).map (fun i => tally i.val) := by
    simp [layers, List.map_ofFn]
  rw [evalWord, radix, hline, List.map_cons, List.prod_cons]
  simp only [eval_inst, decode, ← List.map_reverse, List.flatMap_map]
  rw [eval_radix_suffix]
  have hm := List.map_map (l := Radix.word (layers k)) (f := radixGateMatrix k) (g := firstHalf)
  simp only [Function.comp_def] at hm
  rw [← hm, firstHalf_prod, ← firstHalf_mul, radix_program_eq]

theorem eval_dilation (har : a ≤ 2^k) :
    evalWord har (dilate (tally k)) = shortDilation har := by
  simp only [dilate, eval_append, eval_single, eval_adj, eval_radix, eval_inst, decode]
  simp only [shortDilation, chirpDilation, dilatedConvolution, activeFiber, Matrix.mul_assoc]

theorem eval_reflections (har : a ≤ 2^k) :
    let E := activeFiber har
    let V := shortDilation har
    evalWord har (reflections (tally k)) =
      ((2 : ℝ) • (V * (E * Eᴴ) * Vᴴ) - 1) * (1 - (2 : ℝ) • (E * Eᴴ)) := by
  have hV := mul_eq_one_comm.mp (shortDilation_isometry (NeZero.pos a) har)
  dsimp only
  simp only [reflections, eval_append, eval_single, eval_adj, eval_dilation, eval_inst, decode,
    Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hV]

theorem eval_amplify (har : a ≤ 2^k) :
    evalWord har (amplify (tally k)) = amplifiedCircuit (activeFiber har) (shortDilation har) 64 := by
  rw [amplify, eval_append, eval_repeat, eval_reflections, eval_dilation]
  rfl

/-- Exact action of the emitted instruction list, including the contents of
every inactive and borrowed position. -/
theorem eval_restored (hr : 2*a-1 ≤ 2^k) (har : a ≤ 2^k) :
    evalWord har (restored (tally k)) = extend (activeFiber har) (normalizedFourier a) := by
  rw [← restoredShortTransform_eq hr har]
  simp only [restored, eval_append, eval_single, eval_adj, eval_amplify, eval_inst, decode,
    restoredShortTransform]

end
end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
