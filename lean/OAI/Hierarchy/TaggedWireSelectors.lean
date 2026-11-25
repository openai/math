import OAI.ThreeFlat.Diagonal.MotifHistogram
import OAI.Hierarchy.TaggedData

namespace OAI
/-! # Fixed native counter words for every histogram in one repair pass -/

noncomputable section
namespace Hierarchy.WireTelescope
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical BigOperators

variable {n q W : ℕ} (letters copies : Fin n → ℕ)

abbrev BallChoices := (j : Fin n) → Histogram (Fin (letters j)) (copies j)

/-- Unused letters on a shorter physical menu have zero counter words. A row
that made no purchase is represented by a zero-copy histogram. -/
def counterRows (sel : BallChoices letters copies)
    (room : ∀ i,copies i<2^W) (i : Fin n) (j : Fin q) : Fin (2^W) :=
  if hj : j.val<letters i then
    ⟨((sel i).val ⟨j.val,hj⟩).val,(Nat.lt_succ_iff.mp ((sel i).val ⟨j.val,hj⟩).isLt).trans_lt (room i)⟩
  else 0

/-- The bit order agrees with the control machine's public word decoding. -/
def selectorTable (maxLetters : ∀ i,letters i≤q) (room : ∀ i,copies i<2^W) :
    BallChoices letters copies ↪ Tagged.Bits ((n*q)*W) where
  toFun x z :=
    let a := finProdFinEquiv.symm z
    let b := finProdFinEquiv.symm a.1
    Computability.VPVNP.RAMSerialization.wordBits W (counterRows letters copies x room b.1 b.2) a.2
  inj' := by
    intro x y eqn
    funext i
    apply Subtype.ext
    funext j
    let J : Fin q := j.castLE (maxLetters i)
    have word : counterRows letters copies x room i J = counterRows letters copies y room i J := by
      apply (Computability.VPVNP.RAMSerialization.wordBits W).injective
      funext k
      simpa only [Equiv.symm_apply_apply] using congrFun eqn (finProdFinEquiv (finProdFinEquiv (i,J),k))
    apply Fin.ext
    simpa only [counterRows,J,Fin.val_castLE,dite_eq_left j.isLt] using congrArg Fin.val word

theorem counter_of_active (sel : BallChoices letters copies)
    (maxLetters : ∀ i,letters i≤q) (room : ∀ i,copies i<2^W) (i : Fin n) (j : Fin (letters i)) :
    (counterRows letters copies sel room i (j.castLE (maxLetters i))).val=((sel i).val j).val := by
  simp [counterRows,j.isLt]

theorem idle_counter (sel : BallChoices letters copies)
    (room : ∀ i,copies i<2^W) (i : Fin n) (idle : copies i=0) (j : Fin q) :
    counterRows letters copies sel room i j=0 := by
  unfold counterRows
  split_ifs with valid
  · apply Fin.ext
    have h := ((sel i).val ⟨j.val,valid⟩).isLt
    change ((sel i).val ⟨j.val,valid⟩).val=0
    omega
  · rfl

end Hierarchy.WireTelescope

end
end OAI
