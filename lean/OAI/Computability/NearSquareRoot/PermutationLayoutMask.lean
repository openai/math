import OAI.Computability.NearSquareRoot.PermutationLayoutSlots
import OAI.Computability.NearSquareRoot.CRTControlledFlat

/-! # Physical bit positions of a prepared sparse switch stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout

open IntegerMultiplication IntegerMultiplication.Packed IntegerMultiplication.Adic
open IntegerMultiplication.Code IntegerMultiplication.Loom IntegerMultiplication.Strip
open IntegerMultiplication.Strip.Dims

noncomputable section

/-- Each of the two guarded fields contains one additional sentinel group. -/
abbrev maskWidth (p b G low : ℕ) := p + cap b (G-1) 0 + 0 + cap b (G-1) 0 + low

theorem guard_width (b G : ℕ) (pos : 0 < G) : cap b (G-1) 0 = (b+1)*G := by
  simp [cap,width,Nat.sub_add_cancel pos]

theorem maskWidth_eq (p b G low : ℕ) (pos : 0 < G) :
    maskWidth p b G low = p + 2*((b+1)*G) + low := by
  unfold maskWidth
  rw [guard_width b G pos]
  omega

variable {p b G low c : ℕ}

def prefixWord (y : Block 2 (maskWidth p b G low)) : Block 2 p :=
  ((flatSpan p (cap b (G-1) 0) 0 low).cast.symm y).1

private theorem offset_rev (q : Fin b) :
    targetOffset b G low q.val = low+(b+1)*G+q.rev.val*G := by
  have eq : b-1-q.val = q.rev.val := by simp [Fin.rev]; omega
  rw [targetOffset,eq]

/-- The physical bit addressed by `targetPos q` reads control `q`. -/
theorem mask_target (pos : 0 < G) (fit : low+2*((b+1)*G)+c ≤ maskWidth p b G low)
    (control : Block 2 p → Fin b → Bool) (y : Block 2 (maskWidth p b G low)) (q : Fin b) :
    (least (flatMask (H := G-1) p 0 low control y))[(targetPos pos fit q).val]? =
      (least y)[(targetPos pos fit q).val]?.map
        (fun d => maskDigit (Bool.xor (title d) (control (prefixWord y) q))) := by
  have ht := flatMask_slot (H := G-1) p 0 low control y (targetPos pos fit q).val
  dsimp only at ht
  have den : G-1+1 = G := Nat.sub_add_cancel pos
  have posEq : (targetPos pos fit q).val = low+(b+1)*G+q.rev.val*G := offset_rev q
  have li : low + (b+1)*G ≤ (targetPos pos fit q).val := posEq ▸ Nat.le_add_right _ _
  have subtract : (targetPos pos fit q).val - (low+(b+1)*G) = q.rev.val*G := by rw [posEq]; omega
  simpa only [guard_width b G pos, Nat.add_zero, den, subtract, Nat.mul_div_cancel _ pos, Nat.mul_mod_left,
    li, q.rev.isLt, and_self, dite_true, Fin.eta, Fin.rev_rev, prefixWord] using ht

/-- A physical bit outside all the prescribed target addresses keeps its previous value. -/
theorem mask_other (pos : 0 < G) (fit : low+2*((b+1)*G)+c ≤ maskWidth p b G low)
    (control : Block 2 p → Fin b → Bool) (y : Block 2 (maskWidth p b G low))
    (j : Fin (maskWidth p b G low)) (other : ∀ q, j ≠ targetPos pos fit q) :
    (least (flatMask (H := G-1) p 0 low control y))[j.val]? = (least y)[j.val]? := by
  have ht := flatMask_slot (H := G-1) p 0 low control y j.val
  dsimp only at ht
  have den : G-1+1 = G := Nat.sub_add_cancel pos
  have absent : ¬ (low+(b+1)*G ≤ j.val ∧
      (j.val - (low+(b+1)*G))/G < b ∧ (j.val - (low+(b+1)*G))%G = 0) := by
    rintro ⟨hle,hi,hm⟩
    let n := j.val - (low+(b+1)*G)
    let t : Fin b := ⟨n/G,hi⟩
    apply other t.rev
    apply Fin.ext
    change j.val = targetOffset b G low t.rev.val
    rw [offset_rev t.rev,Fin.rev_rev]
    have split := Nat.mod_add_div n G
    change n%G = 0 at hm
    rw [hm,Nat.zero_add,Nat.mul_comm] at split
    change j.val = low+(b+1)*G+(n/G)*G
    rw [split]
    dsimp [n]
    omega
  simpa only [guard_width b G pos, Nat.add_zero, den, absent, dite_false] using ht

end
end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
