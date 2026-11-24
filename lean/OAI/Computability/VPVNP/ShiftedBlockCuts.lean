import OAI.Computability.VPVNP.ShiftedModeIdentity
import OAI.Computability.VPVNP.ShiftedFactorization

/-!
# From shifted Fock modes to the two crossing factorizations

The tensor in a fixed source block is its integral vacuum pairing times the
Kronecker delta on the exterior-state indices. Its two summands factor through
energy cutoffs differing by twice the coefficient shift in doubled-energy units.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open scoped BigOperators

variable {S I J : Type*} [Fintype S]

/-- An integral four-index tensor written as the sum of two cut factorizations,
with the source block's binomial index included in each coordinate set. -/
def ShiftedBlockCuts (energy : S → ℤ) (H E s : ℤ) (d : ℕ)
    (C : I → J → ℤ) [DecidableEq S] : Prop :=
  ∃ (p : Fin (d + 1) × Cutoff energy (E + H + 2 * s) → I → Cutoff energy E → ℤ)
    (q : Fin (d + 1) × Cutoff energy (E + H + 2 * s) → J → Cutoff energy E → ℤ)
    (r : Fin (d + 1) × Cutoff energy (E + H - 2 * s) → I → Cutoff energy E → ℤ)
    (t : Fin (d + 1) × Cutoff energy (E + H - 2 * s) → J → Cutoff energy E → ℤ),
    ∀ i j (out input : Cutoff energy E),
      C i j * (if out = input then 1 else 0) =
        (∑ v, p v i out * q v j input) + ∑ v, r v i input * t v j out

omit [Fintype S] in
/-- A matrix entry in its energy-difference diagonal has exactly the specified
change of energy, including for negative shifts. -/
private theorem homogeneous_energyMode (energy : S → ℤ) (A : Matrix S S ℤ) (h : ℤ) :
    ModeHomogeneous energy h (fun b => energyMode energy A (2 * b + h)) := by
  intro b out input hn
  by_cases he : energy out - energy input = 2 * b + h
  · omega
  · exact (hn (by simp [energyMode, he])).elim

/-- Apply the two finite cut bounds to an energy-mode residue identity. -/
theorem shiftedBlockCuts_of_modes [DecidableEq S] (energy : S → ℤ)
    (h h' H E s : ℤ) (m d : ℕ) (hdeg : 2 * (d : ℤ) + 2 = h + h')
    (hh : h ≤ H) (hh' : h' ≤ H) (X : I → Matrix S S ℤ)
    (Y : J → Matrix S S ℤ) (C : I → J → ℤ)
    (hres : ∀ i j (out input : Cutoff energy E),
      (∑ a : Fin (d + 1), multiplier d a.val *
        (let q := 2 * s + h' - 2 * (a : ℕ)
         (energyMode energy (X i) (-q) * energyMode energy (Y j) q) out.val input.val -
           (-1 : ℤ) ^ (m * m) *
             (energyMode energy (Y j) q * energyMode energy (X i) (-q)) out.val input.val)) =
          C i j * (if out = input then 1 else 0)) :
    ShiftedBlockCuts energy H E s d C := by
  obtain ⟨p, q, r, t, hf⟩ := shiftedBlockFactorization energy h h' H E s m d
    (by omega) hh hh' (fun i b => energyMode energy (X i) (2 * b + h))
    (fun j b => energyMode energy (Y j) (2 * b + h'))
    (fun i => homogeneous_energyMode _ _ _) (fun j => homogeneous_energyMode _ _ _)
  refine ⟨p, q, r, t, ?_⟩
  intro i j out input
  rw [← hf i j out input, ← hres i j out input]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  have hfirst : 2 * firstExponent d s a + h = -(2 * s + h' - 2 * (a : ℕ)) := by
    unfold firstExponent
    omega
  have hsecond : 2 * secondExponent s a + h' = 2 * s + h' - 2 * (a : ℕ) := by
    unfold secondExponent
    omega
  rw [hfirst, hsecond]

open Lemmata.FockCircuits.FiniteIdentity

/-- The integral block tensor from the finite exterior-algebra operators in Appendix B.
All terminal states in the energy cutoff are included. -/
theorem fock_block_cuts (L K H E h h' m d : ℕ) (s : ℤ)
    (A : I → Index L) (B : J → Index L)
    (hA : ∀ i, Lemmata.FockCircuits.doubledEnergy (A i).val = h)
    (hB : ∀ j, Lemmata.FockCircuits.doubledEnergy (B j).val = h')
    (hcA : ∀ i, (A i).val.card = m) (hcB : ∀ j, (B j).val.card = m)
    (hd : 2 * d + 2 = h + h') (hh : h ≤ H) (hh' : h' ≤ H)
    (hcut : E + K + H + 4 ≤ 2 * L) (hs : |2 * (-s - 1)| ≤ K) :
    ShiftedBlockCuts (fun x : Index L => (Lemmata.FockCircuits.doubledEnergy x.val : ℤ))
      H E s d (fun i j => matrix ℤ L (Pi.single (A i) 1) ⟨∅, by simp⟩ (B j)) := by
  let energy : Index L → ℤ := fun x => Lemmata.FockCircuits.doubledEnergy x.val
  apply shiftedBlockCuts_of_modes energy h h' H E s m d (by omega) (by omega) (by omega)
    (fun i => matrix ℤ L (Pi.single (A i) 1)) (fun j => matrix ℤ L (Pi.single (B j) 1))
  intro i j out input
  have hin : Lemmata.FockCircuits.doubledEnergy input.val.val ≤ E := by
    have he : (Lemmata.FockCircuits.doubledEnergy input.val.val : ℤ) ≤ E := input.property
    exact_mod_cast he
  have hres := shifted_operator_identity ℤ L K (A i) (B j) out.val input.val d s
    (by simpa only [sourceEnergy_sort, hA, hB] using hd)
    (by simp only [sourceEnergy_sort, hA, hB]; omega)
    (by rwa [show -2 * s - 2 = 2 * (-s - 1) by ring])
  have hdiag (U : Index L) (b : ℤ) : diagonal ℤ L b (Pi.single U 1) =
      energyMode energy (matrix ℤ L (Pi.single U 1)) b := rfl
  rw [mul_comm (matrix _ _ _ _ _)]
  simpa only [Finset.length_sort, hcA, hcB, hB, multiplier, hdiag, Subtype.val_inj] using hres

end Crossing

end VPVNP
end Computability
end OAI
