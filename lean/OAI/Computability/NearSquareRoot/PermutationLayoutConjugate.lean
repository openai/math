import OAI.Computability.NearSquareRoot.PermutationLayoutDirectory
import OAI.Computability.NearSquareRoot.PermutationLayoutMask
import OAI.Computability.NearSquareRoot.CRTPositionProgramNative

/-! # Natural-address action of the conjugated prepared sparse XOR -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout
open IntegerMultiplication IntegerMultiplication.Packed IntegerMultiplication.Adic
open IntegerMultiplication.Code IntegerMultiplication.Loom IntegerMultiplication.Strip
open IntegerMultiplication.Strip.Dims PositionProgram

noncomputable section
variable {p b G low c : ℕ}

private theorem forward_bit {k : ℕ} (π : Equiv.Perm (Fin k)) (w : Block 2 k) (j : Fin k) :
    prefixBit (permuteNative π w) j = prefixBit w (π j) := congrFun (permuteNative_bits π w) j

private theorem backward_bit {k : ℕ} (π : Equiv.Perm (Fin k)) (w : Block 2 k) (j : Fin k) :
    prefixBit ((permuteNative π).symm w) j = prefixBit w (π.symm j) :=
  congrFun (permuteNative_symm_bits π w) j

def naturalStage (π : Equiv.Perm (Fin (maskWidth p b G low))) (control : Block 2 p → Fin b → Bool)
    (w : Block 2 (maskWidth p b G low)) :=
  (permuteNative π).symm (flatMask (H:=G-1) p 0 low control (permuteNative π w))

variable (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ maskWidth p b G low)
  (π : Equiv.Perm (Fin (maskWidth p b G low))) (control : Block 2 p → Fin b → Bool)
  (w : Block 2 (maskWidth p b G low))

/-- Cyclically moving all original bits into and out of the prepared coordinates
preserves their identities. Only the target ports undergo the prefix-directed XOR. -/
theorem natural_target (q : Fin b) :
    prefixBit (naturalStage π control w) (π (targetPos pos fit q)) =
      (prefixBit w (π (targetPos pos fit q)) ^^ control (prefixWord (permuteNative π w)) q) := by
  rw [naturalStage,backward_bit,Equiv.symm_apply_apply,← forward_bit]
  let y := permuteNative π w
  let j := targetPos pos fit q
  have eq := mask_target pos fit control y q
  have ht (v : Block 2 (maskWidth p b G low)) : j.val < (least v).length := by simp
  rw [List.getElem?_eq_getElem (ht _),List.getElem?_eq_getElem (ht y),Option.map_some] at eq
  have dig (v : Bool) : title (maskDigit v) = v := by cases v <;> rfl
  exact (congrArg title (Option.some.inj eq)).trans (dig _)

theorem natural_other (j : Fin (maskWidth p b G low))
    (untouched : ∀ q : Fin b, j ≠ π (targetPos pos fit q)) :
    prefixBit (naturalStage π control w) j = prefixBit w j := by
  rw [naturalStage,backward_bit]
  have outside (q : Fin b) : π.symm j ≠ targetPos pos fit q :=
    fun h => untouched q (by simpa only [Equiv.apply_symm_apply] using congrArg π h)
  let y := permuteNative π w
  have h := mask_other pos fit control y (π.symm j) outside
  have ht (v : Block 2 (maskWidth p b G low)) : (π.symm j).val < (least v).length := by simp
  rw [List.getElem?_eq_getElem (ht _),List.getElem?_eq_getElem (ht y)] at h
  have eq := congrArg title (Option.some.inj h)
  exact eq.trans ((forward_bit π w (π.symm j)).trans (by rw [Equiv.apply_symm_apply]))

def prefixIndex (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ maskWidth p b G low) (j : Fin c) : Fin p :=
  ⟨j.val, by rw [maskWidth_eq p b G low pos] at fit; omega⟩

/-- The local prefix port actually read by the control program observes the
corresponding original physical bit before the placement permutation. -/
theorem prefix_source (j : Fin c) :
    prefixBit (prefixWord (permuteNative π w)) (prefixIndex pos fit j) =
      prefixBit w (π (controlPos fit j)) := by
  rw [prefixWord,flatPrefixPort_bit,forward_bit]
  congr 2
  apply Fin.ext
  simp [flatPrefixPort,controlPos,controlOffset,prefixIndex,guard_width b G pos]
  omega

end
end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
