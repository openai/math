import OAI.Computability.NearSquareRoot.SynchronizedLowerSemantics
import OAI.Computability.NearSquareRoot.PrecisionOuterChirp

/-! # Coefficients actually addressed by the expanded short-axis word -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord

open IntegerMultiplication Matrix ChirpTable
open scoped Matrix
noncomputable section
variable {a k : ℕ} [NeZero a]

/-- Lookup for an internal address bit; a nonexistent bit is idle. -/
def bitPhase (arg : ℕ) (f : Fin k → Ambient k → ℂ) (x : Ambient k) : ℂ :=
  if h : arg < k then f ⟨arg,h⟩ x else 1

/-- Scalar entry for any phase instruction in matrix-product orientation.
The default coefficient is one at all the non-phase instructions. -/
def slotPhase (a k : ℕ) [NeZero a] (tag arg : ℕ) (x : Ambient k) : ℂ :=
  let z := calibratedMultiplier a (2^k)
  match tag with
  | 1 => bitPhase arg (fun i => Sum.elim (fun y => Fourier.phase (2^(k-i.val)) (twiddleNumerator i y)) (fun _ => 1)) x
  | 4 => fiberEntries (OuterChirp.bluestein.entry (a := a)) 1 x
  | 5 => fiberEntries (fun _ : Fin a => 1) (-1) x
  | 6 => fiberEntries (fun _ : Fin a => -1) 1 x
  | 7 => fiberEntries (OuterChirp.periodic.entry (a := a)) 1 x
  | 8 => fiberEntries (chirpSpectrum a) 1 x
  | 9 => fiberEntries (OuterChirp.reflected.entry (a := a)) 1 x
  | 11 => physicalDilationPhase z 0 1 x
  | 12 => physicalDilationPhase z 2 3 x
  | 13 => physicalDilationPhase z 4 5 x
  | 15 => bitPhase arg (fun i => controlledPhase i 0 1) x
  | 16 => bitPhase arg (fun i => controlledPhase i 2 3) x
  | 17 => bitPhase arg (fun i => controlledPhase i 4 5) x
  | _ => 1

private theorem fiberEntry_norm {r a : ℕ} {d : Fin a → ℂ} {v : ℂ} (hd : ∀ x, ‖d x‖ = 1)
    (hv : ‖v‖ = 1) (x : Fin r ⊕ Fin r) : ‖fiberEntries d v x‖ = 1 := by
  cases x with
  | inl j => by_cases h : j.val < a <;> simp [fiberEntries, h, hd, hv]
  | inr j => simpa [fiberEntries] using hv

private theorem bitPhase_norm (arg : ℕ) (f : Fin k → Ambient k → ℂ)
    (hf : ∀ i j, ‖f i j‖ = 1) (x : Ambient k) : ‖bitPhase arg f x‖ = 1 := by
  by_cases h : arg < k <;> simp [bitPhase, h, hf]

theorem slotPhase_norm (a k : ℕ) [NeZero a] (tag arg : ℕ) (x : Ambient k) :
    ‖slotPhase a k tag arg x‖ = 1 := by
  have hc (t : ℝ) : ‖phase t‖ = 1 := by simp [phase, Complex.norm_exp]
  have ho (kind : OuterChirp) (i : Fin a) : ‖kind.entry i‖ = 1 := by
    cases kind <;> simp [OuterChirp.entry, bluesteinDiagonal, chirp, hc]
  have hz (i : Fin (2^k)) := (calibratedMultiplier_lt_half (NeZero.pos a) i).le
  unfold slotPhase
  dsimp only
  split
  · apply bitPhase_norm
    intro i j
    cases j <;> simp [Fourier.phase_norm]
  · exact fiberEntry_norm (ho _) norm_one _
  · exact fiberEntry_norm (fun _ => norm_one) (by simp) _
  · exact fiberEntry_norm (fun _ => by simp) norm_one _
  · exact fiberEntry_norm (ho _) norm_one _
  · exact fiberEntry_norm chirpSpectrum_norm norm_one _
  · exact fiberEntry_norm (ho _) norm_one _
  · exact physicalDilationPhase_norm _ hz _ _ _
  · exact physicalDilationPhase_norm _ hz _ _ _
  · exact physicalDilationPhase_norm _ hz _ _ _
  · exact bitPhase_norm _ _ (fun i j => controlledPhase_norm i _ _ j) _
  · exact bitPhase_norm _ _ (fun i j => controlledPhase_norm i _ _ j) _
  · exact bitPhase_norm _ _ (fun i j => controlledPhase_norm i _ _ j) _
  · exact norm_one

def phaseTags : List ℕ := [1,4,5,6,7,8,9,11,12,13,15,16,17]

omit [NeZero a] in
private theorem negative_reflection_table (har : a ≤ 2^k) :
    1 - (2 : ℝ) • (activeFiber har * (activeFiber har)ᴴ) =
      diagonal (fiberEntries (fun _ : Fin a => -1) 1) := by
  rw [← extend_active_diagonal har]
  have hneg : (diagonal (fun _ : Fin a => (-1 : ℂ)) : Matrix (Fin a) (Fin a) ℂ) = -1 := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_neg]
  rw [extend, hneg, sub_eq_add_neg (-1 : Matrix (Fin a) (Fin a) ℂ) 1]
  simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.mul_one, Matrix.add_mul, Matrix.neg_mul, two_smul]
  abel

omit [NeZero a] in
private theorem positive_reflection_table (har : a ≤ 2^k) :
    (2 : ℝ) • (activeFiber har * (activeFiber har)ᴴ) - 1 =
      diagonal (fiberEntries (fun _ : Fin a => 1) (-1)) := by
  rw [← neg_sub, negative_reflection_table, Matrix.diagonal_neg]
  apply congrArg
  funext x
  cases x with
  | inl j => by_cases h : j.val < a <;> simp [fiberEntries, h]
  | inr j => simp [fiberEntries]

private theorem bitLookup_diag (arg : ℕ) (f : Fin k → Ambient k → ℂ) :
    bitLookup arg (fun i => diagonal (f i)) = diagonal (bitPhase arg f) := by
  by_cases h : arg < k
  · simp [bitLookup, bitPhase, h]
  · simp only [bitLookup, dite_eq_right h]
    rw [show bitPhase arg f = fun _ => 1 by funext x; simp [bitPhase,h], Matrix.diagonal_one]

/-- The stored forward coefficient computes precisely the phase assigned to
that address in the decoded matrix. -/
theorem slotPhase_matrix (har : a ≤ 2^k) {tag : ℕ} (ht : tag ∈ phaseTags) (arg : ℕ) :
    lowerDecode har tag arg = diagonal (slotPhase a k tag arg) := by
  simp [phaseTags] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · by_cases hi : arg < k
    · simp [lowerDecode, decode, slotPhase, bitPhase, hi, radixGateMatrix_twiddle, firstHalf_phase]
    · have he : slotPhase a k 1 arg = fun _ => 1 := by funext x; simp [slotPhase, bitPhase, hi]
      simp [lowerDecode, decode, hi, he, Matrix.diagonal_one]
  · change extend (activeFiber har) (bluesteinDiagonal a) =
      diagonal (fiberEntries (OuterChirp.bluestein.entry (a := a)) 1)
    have he : bluesteinDiagonal a = diagonal (OuterChirp.bluestein.entry (a := a)) := by
      simp [OuterChirp.entry, bluesteinDiagonal]
    rw [he, extend_active_diagonal]
  · exact positive_reflection_table har
  · exact negative_reflection_table har
  · exact extend_active_diagonal har _
  · exact extend_active_diagonal har _
  · exact extend_active_diagonal har _
  · rfl
  · rfl
  · rfl
  · exact bitLookup_diag arg (fun i : Fin k => controlledPhase i 0 1)
  · exact bitLookup_diag arg (fun i : Fin k => controlledPhase i 2 3)
  · exact bitLookup_diag arg (fun i : Fin k => controlledPhase i 4 5)

theorem slotPhase_matrix_oriented (har : a ≤ 2^k) (x : Inst) (ht : x.1.length ∈ phaseTags) :
    evalSlot har x = diagonal (fun j =>
      if x.2.2 then star (slotPhase a k x.1.length x.2.1.length j)
      else slotPhase a k x.1.length x.2.1.length j) := by
  rw [evalSlot, slotPhase_matrix har ht]
  cases x.2.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true, Matrix.diagonal_conjTranspose]
  rfl

end
end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
