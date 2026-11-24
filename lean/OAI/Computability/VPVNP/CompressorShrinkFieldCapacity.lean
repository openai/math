import OAI.Computability.VPVNP.CompressorRecordsShrinkOutputBuild
import OAI.Computability.VPVNP.CursorDescriptorWords

/-!
# Word capacity of the selected shrinking arithmetic

The grid coefficients and degree transition determine all constant field
bounds before the input length is chosen. Residual lane count is at most
the old site count. On every selected cursor branch the incoming maximum
width is at most the input length. Together these discharge the arithmetic
fields of the shrinking output worker's actual word-format contract.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkOutput

open Compression ShrinkMotif CursorBounds CursorNetwork Filter BurstRAM

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

private noncomputable def transitionConstant (S : BlockSchedule k) (i : Fin S.steps) : ℕ :=
  let a := S.degreeExponent i.castSucc
  let b := S.degreeExponent i.succ
  2^(packingTagBits (2^a)) + (∑ t, subdivisions (2^a) (2*2^a+1) (2^b) t) + 2^b

set_option maxHeartbeats 1500000 in
/-- At all sufficiently large input lengths the only remaining physical
capacity obligation for `FitsWords` is the end of the packed output arena. -/
theorem eventually_fitsWords (B : S.Templates) (b : ℕ) (hb : 1 ≤ b) : ∀ᶠ n : ℕ in atTop,
    ∀ (i : Fin S.steps) {g : ℕ}
      (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g)),
      X.positions ≤ initialPositions b n → X.maxWireWidth ≤ n →
      ∀ (term : Word (wordBits b n)) (stride role retained : ℕ),
        stop (b := S.degreeExponent i.succ) X term.val stride role retained < 2^wordBits b n →
        FitsWords (b := S.degreeExponent i.succ) X B.shrink term stride role retained := by
  let K := B.shrink.selectorBits + fieldFactor B.shrink +
    Finset.univ.sup (transitionConstant S)
  have hfit := CursorRAM.eventual_word_room b hb ((PolynomiallyBounded.const K).mul PolynomiallyBounded.succ)
  filter_upwards [hfit,CursorRAM.eventual_word_room b hb (CursorRAM.bounded_positions b)] with n hi hP
  intro i g X hx hW term stride role retained hroom
  have hconst := (Nat.le_mul_of_pos_right K (Nat.succ_pos n)).trans_lt hi
  have hsum : transitionConstant S i ≤ Finset.univ.sup (transitionConstant S) := Finset.le_sup (Finset.mem_univ _)
  have hc : transitionConstant S i < 2^wordBits b n := hsum.trans_lt (by dsimp only [K] at hconst; omega)
  have hl : 2^g ≤ X.positions := by
    rw [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin]
    exact (Nat.pow_le_pow_right Nat.zero_lt_two (by unfold packingLaneBits; omega)).trans
      (Nat.le_mul_of_pos_left _ Fintype.card_pos)
  have hfield : fieldFactor B.shrink ≤ K := by dsimp [K]; omega
  refine ⟨hroom,?_,(Nat.mul_le_mul hfield (Nat.succ_le_succ hW)).trans_lt hi,hl.trans_lt (hx.trans_lt hP),?_,?_,?_⟩
  · dsimp only [K] at hconst; omega
  · let tags := 2^(packingTagBits (2^S.degreeExponent i.castSucc))
    let profile := ∑ j, subdivisions (2^S.degreeExponent i.castSucc) (2*2^S.degreeExponent i.castSucc+1) (2^S.degreeExponent i.succ) j
    let degree := 2^S.degreeExponent i.succ
    exact (Nat.le_add_right tags profile).trans_lt ((Nat.le_add_right (tags+profile) degree).trans_lt hc)
  · let tags := 2^(packingTagBits (2^S.degreeExponent i.castSucc))
    let profile := ∑ j, subdivisions (2^S.degreeExponent i.castSucc) (2*2^S.degreeExponent i.castSucc+1) (2^S.degreeExponent i.succ) j
    let degree := 2^S.degreeExponent i.succ
    exact (Nat.le_add_left profile tags).trans_lt ((Nat.le_add_right (tags+profile) degree).trans_lt hc)
  · exact (Nat.le_add_left (2^S.degreeExponent i.succ) _).trans_lt hc

end CompressorRecords.ShrinkOutput

end VPVNP
end Computability
end OAI
