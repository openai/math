import OAI.Computability.VPVNP.SliceArithmeticCountPorts
import OAI.Computability.VPVNP.SliceArithmeticConstantEmit

/-!
# Converting signed witness counts into an extension-field coefficient

Each arbitrary-width little-endian count is reduced independently modulo the
advised prime. Their difference occupies the constant coordinate of the power
basis, with a zero word for every higher coordinate. The input counts, field
advice and the caller's output suffix survive the conversion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticSignedCount

open BurstRAM RAMTape TapeWord SliceArithmetic

/-- Route constant emission through the residue holding the signed difference, the caller's
degree and zero word, and the result port. -/
def emitPorts : ConstantEmit.Port → Port
  | .degree => .inr .degree
  | .zeroWord => .inr .zeroWord
  | .limb => .inl (.residue false)
  | .out => .inr .result
  | .scratch => .inl .scratch
  | .marker => .inl .marker

private theorem emit_injective : Function.Injective emitPorts := by
  intro i j h
  cases i <;> cases j <;> simp_all [emitPorts]

/-- Reduce both counts modulo the prime, subtract the residues, emit their difference in the
constant coordinate, and clear the residues. -/
def machine : FiniteRoutine Port :=
  (((((reduceCount false).followedBy (reduceCount true)).followedBy
    (SliceArithmeticSubtract.machine.onPorts arithmeticPorts)).followedBy
    (ConstantEmit.machine.onPorts emitPorts)).followedBy (CallClear.clear (.inl (.residue false)))).followedBy
    (CallClear.clear (.inl (.residue true)))

/-- Step bound for signed-count conversion with input bit lengths `n` and `m`, extension degree
`e`, and limb width `w`. -/
def callCap (n m e w : ℕ) :=
  reduceCost n w + reduceCost m w + 400 * (w + 1)^2 + ConstantEmit.cost e w + 2 * (w + 1)

/-- The coefficient emitted from the two binary counters. -/
def difference (p : ℕ) [NeZero p] (positive negative : List Bool) : Fin p :=
  Fin.ofNat p (value positive) - Fin.ofNat p (value negative)

private theorem emit_runs {p e w : ℕ} (he : 0 < e) (positive negative suffix : List Bool)
    (low : BurstRAM.Word w) (other : List Bool) :
    let residues := fun sign : Bool => if sign then other else wordBits low
    (ConstantEmit.machine.onPorts emitPorts).Runs (ConstantEmit.cost e w)
      (frame (external p e w positive negative suffix) [] residues)
      (frame (external p e w positive negative (wordBits low ++ List.replicate ((e-1)*w) false ++ suffix))
        [] residues) := by
  intro residues
  apply FiniteRoutine.runs_onPorts_framed _ emit_injective (ConstantEmit.machine_runs he low suffix)
  · intro i
    cases i <;> rfl
  · intro i
    cases i <;> rfl
  rintro (i|i) hi
  · cases i with
    | divide i => cases i <;> rfl
    | _ => rfl
  · cases i <;> first | rfl | exact (hi .out rfl).elim

theorem machine_runs {p e w : ℕ} [NeZero p] (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (positive negative suffix : List Bool) :
    let low := Word.limb w (difference p positive negative)
    ∃ t ≤ callCap positive.length negative.length e w, machine.Runs t
      (clean (external p e w positive negative suffix))
      (clean (external p e w positive negative (wordBits low ++ List.replicate ((e-1)*w) false ++ suffix))) := by
  intro low
  let a := Fin.ofNat p (value positive)
  let b := Fin.ofNat p (value negative)
  let bits := fun z : Fin p => wordBits (Word.limb w z)
  let io := external p e w positive negative suffix
  let blank := fun _ : Bool => ([] : List Bool)
  let first := Function.update blank false (bits a)
  have pos := reduceCount_runs hw false io blank rfl rfl
  have neg := reduceCount_runs hw true io first rfl rfl
  have hboth : Function.update first true (bits b) = fun s : Bool => if s then bits b else bits a := by
    funext s; cases s <;> rfl
  change (reduceCount true).Runs (reduceCost negative.length w) _ (frame io [] (Function.update first true (bits b))) at neg
  rw [hboth] at neg
  obtain ⟨n, hn, subtract⟩ := subtract_runs hw io a b rfl rfl
  have emit := emit_runs (p := p) he positive negative suffix low (bits (-b))
  let next := external p e w positive negative (wordBits low ++ List.replicate ((e-1)*w) false ++ suffix)
  let after := frame next [] (fun s : Bool => if s then bits (-b) else wordBits low)
  let afterLow := frame next [] (fun s : Bool => if s then bits (-b) else [])
  have hclear₁ := CallClear.clear_runs (.inl (.residue false)) after
  have hclear₂ := CallClear.clear_runs (.inl (.residue true)) afterLow
  have heq₁ : Function.update after (.inl (.residue false)) [] = afterLow := by
    funext j
    rcases j with i|i
    · cases i with
      | divide i => cases i <;> rfl
      | residue s => cases s <;> rfl
      | _ => rfl
    · rfl
  have heq₂ : Function.update afterLow (.inl (.residue true)) [] = clean next := by
    funext j
    rcases j with i|i
    · cases i with
      | divide i => cases i <;> rfl
      | residue s => cases s <;> rfl
      | _ => rfl
    · rfl
  rw [heq₁, show (after (.inl (.residue false))).length = w from length_wordBits _] at hclear₁
  rw [heq₂, show (afterLow (.inl (.residue true))).length = w from length_wordBits _] at hclear₂
  refine ⟨_, ?_, ((((pos.followedBy neg).followedBy subtract).followedBy emit).followedBy hclear₁).followedBy hclear₂⟩
  change reduceCost positive.length w + reduceCost negative.length w + n + ConstantEmit.cost e w +
    (w+1) + (w+1) ≤ _
  unfold callCap
  omega

/-- A single quadratic bound in all bit lengths and the number of coordinates. -/
theorem callCap_le (n m e w : ℕ) : callCap n m e w ≤ 600 * (n + m + e + w + 1)^2 := by
  unfold callCap reduceCost SliceArithmeticMagnitude.cost ConstantEmit.cost
  have h := Nat.mul_le_mul_right (5*w + 3) (Nat.sub_le e 1)
  ring_nf at h ⊢
  omega

end SliceArithmeticSignedCount

end VPVNP
end Computability
end OAI
