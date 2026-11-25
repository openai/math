import OAI.Computability.BorderVNP.CrossingFusionPolynomial
import OAI.Computability.BorderVNP.CrossingFusionVerifierAPI

/-!
# Product of the local signed crossing verifiers

A global witness contains one path for each crossing. Adjacent verifiers
read the same occupation mask. Their signed weights multiply, and the sum
over their private choices gives the product of the local table entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionStage

open VPVNP.Crossing MvPolynomial

/-- Local verifier for each factor in the orientation and side in question. -/
abbrev Checkers {m d : ℕ} (w : WireStates (leastEnergy m) (2^m)) (left : Bool)
    (b : Fin d → Bool) := ∀ i : Fin d, Checker w (i.val * leastEnergy m) (!(b i.rev))
      (if b i.rev then left else !left)

/-- The ordinal of a checked occupancy mask under the include-or-exclude ranking. -/
noncomputable def maskIndex (E : ℕ) : StateIndex.ValidMask E ≃ Fin (stateCountAt E) :=
  (StateIndex.validMaskEquiv E).trans (StateIndex.energyStateEquiv E)

variable {m d p : ℕ} {w : WireStates (leastEnergy m) (2^m)} {left : Bool} {b : Fin d → Bool}

/-- One occupation mask at each energy boundary, including the last state on the cut. -/
abbrev States (d H : ℕ) := (i : Fin (d+1)) → StateIndex.ValidMask (i.val * H)

/-- All private local guesses, kept in separate bit blocks. -/
abbrev LocalGuesses (f : Checkers w left b) := (i : Fin d) → Fin (f i).guesses → Bool

/-- Query bits for a single stage of the chain. -/
noncomputable def stageQuery (i : Fin d) (x : Fin d → Fin (2^m)) (j : Fin d → Fin (2*leastEnergy m))
    (v : States d (leastEnergy m)) : Query (2^m) (leastEnergy m) (i.val * leastEnergy m) → Bool :=
  queryBits (x i.rev) (j i.rev) (StateIndex.validMaskEquiv _ (v i.castSucc))
    (nextState rankedStates i.val (leastEnergy m) (maskIndex _ (v i.succ)))

/-- Signed Boolean outputs of one local path, with shared occupancy inputs. -/
noncomputable def stageFlags (f : Checkers w left b) (x : Fin d → Fin (2^m))
    (j : Fin d → Fin (2*leastEnergy m)) (v : States d (leastEnergy m))
    (a : LocalGuesses f) (i : Fin d) : Bool → Bool :=
  (f i).frame.eval (Sum.elim (stageQuery i x j v) (a i))

/-- The signed value of the whole witness is the product of the local signed values. -/
noncomputable def pathSign (f : Checkers w left b) (x : Fin d → Fin (2^m))
    (j : Fin d → Fin (2*leastEnergy m)) (v : States d (leastEnergy m)) (a : LocalGuesses f) : ℤ :=
  ∏ i, signValue (stageFlags f x j v a i)

private theorem sum_paths (f : Checkers w left b) (x : Fin d → Fin (2^m))
    (j : Fin d → Fin (2*leastEnergy m)) (v : States d (leastEnergy m)) :
    ∑ a : LocalGuesses f, pathSign f x j v a =
      chainWeight w left b x j (fun i => maskIndex _ (v i)) := by
  rw [chainWeight]
  simp only [pathSign, stageFlags]
  rw [← Fintype.prod_sum (fun (i : Fin d) (a : Fin (f i).guesses → Bool) =>
    signValue ((f i).frame.eval (Sum.elim (stageQuery i x j v) a)))]
  apply Finset.prod_congr rfl
  intro i _
  rw [sideFactor_numbered]
  simp only [stageQuery, Checker.correct, rankedStates, maskIndex,
    Fin.val_castSucc, Fin.val_succ, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- The fused side polynomial is the weighted sum of the explicitly indexed
terminal words, mode labels, admissible masks and local Boolean witnesses. -/
theorem polynomial_signed_paths (R : Type*) [CommRing R] (f : Checkers w left b)
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m) :
    sidePolynomial (binarySideTensor R w addr left b) =
    ∑ x : Fin d → Fin (2^m), ∑ j : Fin d → Fin (2*leastEnergy m),
      ∑ v : States d (leastEnergy m), ∑ a : LocalGuesses f,
        (pathSign f x j v a : MvPolynomial _ R) *
          sideMonomial R x (binaryBridge addr (j,maskIndex _ (v (Fin.last d)))) := by
  rw [binarySide_polynomial]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro j _
  let e := Equiv.piCongrRight (fun i : Fin (d+1) => maskIndex (i.val * leastEnergy m))
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_mul, ← Int.cast_sum, sum_paths]
  rfl

end Crossing.FusionStage

end BorderVNP
end Computability
end OAI
