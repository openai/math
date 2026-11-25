import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeAxis
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeDecomposition
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeRawWord
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeResidualWord
import OAI.LinearAlgebra.FiniteFourier.DyadicFourierWord

/-! # Protected words for conversion on a whole prime cyclic axis

Both directions use the same number of layers and restore the workspace.
Two copies of the padded transform workspace suffice for the two signed rows.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Matrix
open scoped Kronecker

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

private theorem map_rawTransform (φ : R →+* S) (D : Matrix (Fin m) (Fin m) R) :
    (atTwoRawTransform D).map φ = atTwoRawTransform (D.map φ) := by
  ext (i | i) (j | j) <;> simp [atTwoRawTransform, Matrix.map_apply, kroneckerMap_apply,
    Matrix.one_apply, apply_ite φ]

private theorem map_dft (φ : R →+* S) (q : R) :
    (dftMatrix m q).map φ = dftMatrix m (φ q) := by
  ext i j
  simp [dftMatrix]

private theorem rawFourier_pair_map (φ : R →+* S) {d : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    [NeZero m] (u : Rˣ) (hu : u^m = 1) (hm : IsUnit (m:R))
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))
    (hF : OccupiedWord W d (geometricMatrix m (φ (u:R)))) :
    OccupiedWord (Bool × W) (1+d)
      ((atTwoRawTransform ((↑hm.unit⁻¹:R) • dftMatrix m (u:R))).map φ) ∧
    OccupiedWord (Bool × W) (1+(1+d))
      ((atTwoRawTransform (dftMatrix m (↑u⁻¹:R))).map φ) := by
  let v := Units.map φ.toMonoidHom u
  have hv : v^m = 1 := by simp [v, ← map_pow, hu]
  have hm' : IsUnit (m:S) := by simpa using hm.map φ
  have hs' : Pairwise fun i j : Fin m => IsUnit ((v:S)^i.val - (v:S)^j.val) := by
    intro i j h
    simpa [v] using (hs i j h).map φ
  obtain ⟨hA,hB⟩ := occupiedWord_atTwoRawFourier_pair v hv hm' hs' hF
  have hunit : Units.map φ.toMonoidHom hm.unit = hm'.unit := Units.ext (by simp)
  have hnorm : φ (↑hm.unit⁻¹:R) = (↑hm'.unit⁻¹:S) := by
    change (↑((Units.map φ.toMonoidHom) hm.unit⁻¹) : S) = _
    rw [map_inv, hunit]
  rw [map_rawTransform, map_rawTransform, map_dft]
  have hAs : (((↑hm.unit⁻¹:R) • dftMatrix m (u:R)).map φ) =
      (↑hm'.unit⁻¹:S) • dftMatrix m (v:S) := by
    ext i j
    simp [Matrix.map_apply, smul_eq_mul, hnorm, dftMatrix, v]
  rw [hAs]
  exact ⟨hA,hB⟩

namespace AtTwoPrimeAxis

variable {M p : ℕ} [Fact p.Prime] {hM : Odd M} {hp : p % 4 = 3} {hp7 : 7 ≤ p}
  (a : AtTwoPrimeAxis M p hM hp hp7)

local notation "mₚ" => ((p-1)/2 : ℕ)
local notation "O₂" => CyclotomicCoefficients TwoLocalQuadratic M

/-- Reindexed cyclic addresses on which the square matrices act. -/
noncomputable def rowAddress (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    PrimeAxisRow ((p-1)/2) ≃ ZMod p := primeAxisAddress (PrimeAxisCosets.ofPrime p hp)

/-- Extending to a semilocal target preserves both conversions. A single
forward DFT word on a half-length row supplies both prime-axis words. -/
theorem conversionWord_of_fourier (φ : O₂ →+* S) [Finite (MaximalSpectrum S)]
    (hunit : ∀ x : S, ∃ t, IsUnit t ∧ IsUnit (x-t))
    {d : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (hF : OccupiedWord W d (geometricMatrix mₚ (φ (a.root:O₂)))) :
    OccupiedWord (Bool × W) (84+d) ((a.forward.map φ).submatrix id (rowAddress p hp)) ∧
    OccupiedWord (Bool × W) (84+d) ((a.backward.map φ).submatrix (rowAddress p hp) id) := by
  let := atTwoCoefficients_nontrivial hM.pos
  let : NeZero mₚ := ⟨by omega⟩
  let e := primeAxisSignedIndex mₚ
  have hpu := atTwoCoefficients_isUnit_odd M (primeAxis_odd_parameters hp).1
  have hm := atTwoCoefficients_isUnit_odd M (primeAxis_odd_parameters hp).2
  obtain ⟨hA,hB⟩ := rawFourier_pair_map φ a.root a.root_pow hm a.separated hF
  obtain ⟨hP,hQ⟩ := primeAxisResidual_layerWords a.factor hpu hm a.root_pow a.separated φ hunit
  have hMtx := congrArg (fun A => Matrix.map A φ)
    (primeAxisMatrix_decomposition a.factor hpu hm a.root_pow a.separated)
  have hInv := congrArg (fun A => Matrix.map A φ)
    (primeAxisInvMatrix_decomposition a.factor hpu hm a.root_pow a.separated)
  simp only [Matrix.map_mul] at hMtx hInv
  constructor
  · change OccupiedWord _ _ ((a.forward.submatrix id (rowAddress p hp)).map φ)
    rw [show (a.forward.submatrix id (rowAddress p hp)).map φ = _ from hMtx]
    exact LayerWord.pad (by omega) (hP.occupied.mul (hA.relabel e.symm))
  · change OccupiedWord _ _ ((a.backward.submatrix (rowAddress p hp) id).map φ)
    rw [show (a.backward.submatrix (rowAddress p hp) id).map φ = _ from hInv]
    exact LayerWord.pad (by omega) ((hB.relabel e.symm).mul hQ.occupied)

/-- In each integral jet, the prime-axis conversion fits in the ternary
Fourier workspace and has logarithmic depth uniformly for all primes up to `B`. -/
theorem conversionWord (h B : ℕ) (hle : mₚ ≤ B) (h3 : ∀ j, 3^j ≤ 8*B → 3^j ∣ M) :
    let φ := algebraMap O₂ (IntegralJet M h)
    let d := 84 + 6400*(1 + Nat.clog 2 (2+B))
    OccupiedWord (Bool × Fin (13*mₚ)) d ((a.forward.map φ).submatrix id (rowAddress p hp)) ∧
    OccupiedWord (Bool × Fin (13*mₚ)) d ((a.backward.map φ).submatrix (rowAddress p hp) id) := by
  let φ := algebraMap O₂ (IntegralJet M h)
  let := integralJet_semilocal M h
  apply a.conversionWord_of_fourier φ (integralJet_unit_split M h)
  apply protectedFourier_word_up_to (r := 3) (Or.inr rfl) (by omega) hle _ (integralJet_unit_split M h)
    (a.root.isUnit.map φ) _ (Or.inl rfl)
  · intro j hj
    obtain ⟨u,_,hu,hs⟩ := integralJet_axisRoot hM (h3 j hj) h
    exact ⟨isUnit_odd_inIntegralJet _ _ (hM.of_dvd_nat (h3 j hj)), u, hu, hs⟩
  · intro i j hij
    simpa using (a.separated i j hij).map φ

end AtTwoPrimeAxis

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
