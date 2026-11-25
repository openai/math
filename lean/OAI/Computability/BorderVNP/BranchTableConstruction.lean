import OAI.Computability.BorderVNP.BranchConstruction
import OAI.Computability.BorderVNP.BranchAdviceBitsTable
import OAI.Computability.BorderVNP.BranchParseFamily

/-!
# Proposition 9.2 for the degree-component universal circuit table

The coefficient vector includes every monomial of the prescribed total degree in the
paired variables. This theorem takes the image-closure inclusion obtained after the
common characteristic specialization and returns the finite arithmetic branch used by
the residue construction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

universe u v

namespace Branch

open MvPolynomial ParseTable BranchSpecialization

set_option maxHeartbeats 2000000 in
/-- The actual paired table yields one branch over a finite extension of the already
chosen constant field. It realizes every prescribed coefficient in a single discrete
valuation ring, and every affine equation uses the weighted parse-table advice. -/
theorem numbered_branch_of_tableClosure (E₀ : Type v) (K : Type u) [Field E₀] [Fintype E₀]
    [Field K] [IsAlgClosed K] [Algebra E₀ K] (k s : ℕ) (p : MvPolynomial (Fin (2*(k+1))) ℤ)
    (hc : Int.castRingHom K ∘ coeffVector (k+1) p ∈ imageClosure
      (polynomialImage (numberedTable K (2*(k+1)) k s))) :
    let n := k+1
    let m := parameterCount (2*n) k s
    let _ := Fintype.ofFinite (DegreeMonomial (Fin (2*n)) n)
    ∃ E : IntermediateField E₀ K, Finite E ∧
      Nat.card E ≤ Fintype.card E₀ *
        max (sliceGridBound m (2*k+1) ((n+1)^(2*n)) (Nat.card (DegreeMonomial (Fin (2*n)) n))) 1 *
        max (displacementDegree m (2*k+1) (2*k+2)) 1 ∧
      ∃ advice : CurveAdvice E m,
        let Y := numberedTable E (2*n) k s
        let c := Int.castRingHom E ∘ coeffVector n p
        let G := advice.equations Y c (pairedDegreeExponent n) ((n+1)^(2*n))
        (∀ i, (G i).totalDegree ≤ 2*k+3) ∧
          ∃ branch : GeometricBranch Y c (fun i => genericRow (G i)),
            Finite (IsLocalRing.ResidueField branch.place) := by
  classical
  intro n m inst
  let c := Int.castRingHom E₀ ∘ coeffVector n p
  have hcast {E : Type u} [Field E] (i : E₀ →+* E) : i ∘ c = Int.castRingHom E ∘ coeffVector n p := by
    have hc' : i.comp (Int.castRingHom E₀) = Int.castRingHom E := Subsingleton.elim _ _
    funext j
    exact RingHom.congr_fun hc' _
  have hclosure : algebraMap E₀ K ∘ c ∈ imageClosure (Set.range
      (fun x : Fin m → K => fun i => eval x
        (map (algebraMap E₀ K) (numberedTable E₀ (2*n) k s i)))) := by
    change _ ∈ imageClosure (polynomialImage (fun i => map (algebraMap E₀ K) (numberedTable E₀ (2*n) k s i)))
    rw [hcast (algebraMap E₀ K), funext (numberedTable_map (algebraMap E₀ K) (2*n) k s)]
    exact hc
  obtain ⟨E,hE,hsize,a,hd,hg⟩ := branch_of_imageClosure (numberedTable E₀ (2*n) k s)
    c (pairedDegreeExponent n) (2*k+1) ((n+1)^(2*n)) (parameterCount_pos (by dsimp [n]; omega) k s)
    (numberedTable_degree E₀ (2*n) k s) (pairedDegreeExponent_injective n) (pairedDegreeExponent_lt n) hclosure
  have eqY := funext (numberedTable_map (algebraMap E₀ E) (2*n) k s)
  have eqc := hcast (algebraMap E₀ E)
  refine ⟨E,hE,?_,a,?_,?_⟩
  · rw [Nat.card_eq_fintype_card (α := DegreeMonomial (Fin (2*n)) n)]
    exact hsize
  · rw [← eqY, ← eqc]
    exact hd
  · rw [← eqY, ← eqc]
    exact hg

end Branch

end BorderVNP
end Computability
end OAI
