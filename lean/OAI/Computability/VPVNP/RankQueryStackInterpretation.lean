import OAI.Computability.VPVNP.RankQueryStackField

/-!
# Rank over the advised field from native scalar words

Interpretation commutes with the weighted Gram coefficients and the
reverse characteristic polynomial. This identifies the numerical rank
returned by the packed-word machine with matrix rank in the advised
finite extension.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

open Polynomial

namespace SchurKey

variable {A B : Type*} [CommRing A] [CommRing B] {n m : ℕ}

private theorem map_reverseCharpoly (f : A →+* B) (M : Matrix (Fin n) (Fin n) A) :
    Polynomial.map f M.charpolyRev = (M.map f).charpolyRev := by
  change (mapRingHom f) (1 - X • M.map C).det = _
  rw [RingHom.map_det, Matrix.charpolyRev]
  apply congrArg Matrix.det
  rw [map_sub, map_one]
  congr 1
  ext i j : 1
  change Polynomial.map f (X * C (M i j)) = X * C (f (M i j))
  simp

private theorem map_weightedGram (f : A →+* B) (M : Matrix (Fin n) (Fin m) A) :
    (weightedGram M).map (mapRingHom f) = weightedGram (M.map f) := by
  ext i j z
  change (Polynomial.map f ((weightedGram M) i j)).coeff z = _
  rw [coeff_map, ← weightedGramEntryCoeff_eq, ← weightedGramEntryCoeff_eq]
  unfold weightedGramEntryCoeff
  split_ifs <;> simp

/-- Correctness of a rank scan in an executable ring embedded in a field. -/
theorem computeRank_interpreted {F : Type*} [Field F] [DecidableEq A] [DecidableEq F]
    (f : A →+* F) (hf : Function.Injective f) (M : Matrix (Fin n) (Fin m) A) :
    computeRank M = (M.map f).rank := by
  let val := compute (weightedGramEntryCoeff M)
  have eqzero (u z : ℕ) : f (val u z) = 0 ↔ val u z = 0 := by rw [← f.map_zero, hf.eq_iff]
  have hs : computeRank M = scanRank n m (fun u z => f (val u z)) := by
    unfold computeRank scanRank
    simp only [eqzero, val]
  rw [hs]
  apply scanRank_correct
  intro u z
  change f (compute _ u z) = _
  rw [compute_correct (weightedGram M) _ (weightedGramEntryCoeff_eq M)]
  rw [← coeff_map f]
  change ((mapRingHom f) ((weightedGram M).charpolyRev.coeff u)).coeff z = _
  rw [← coeff_map (mapRingHom f), map_reverseCharpoly, map_weightedGram]
  rfl

end SchurKey

namespace Scalar

open SliceArithmetic

variable {p e n m : ℕ} [Fact p.Prime] [NeZero e] (c : Vector p e)

/-- Compute in binary coefficient words and interpret the output rank in the
advised irreducible extension. Only the input matrix entries are read. -/
theorem rank_correct [Fact (Irreducible (modulus c))] (M : Matrix (Fin n) (Fin m) (Scalar c)) :
    SchurKey.computeRank M = (M.map (interpretation c)).rank := by
  classical
  apply SchurKey.computeRank_interpreted
  exact interpret_injective c

end Scalar

end RankQuery.Stack

end VPVNP
end Computability
end OAI
