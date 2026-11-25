import OAI.LinearAlgebra.SpectralBooks.CrossingPacket
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionPower
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport

/-! # Tree straightening for a packet of two crossing wires

Each wire is the two-site equality tensor grouped at its actual endpoints.
At cyclically ordered terminals `a,b,c,d` the crossing pairs `a,c` and
`b,d`. The two side matchings pair `a,b` with `c,d` and `a,d` with `b,c`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped BigOperators NNReal
noncomputable section

namespace SiteTensor

variable {I : Type} [Fintype I] [Nonempty I] (K : Type*) [Field K]

/-- Two independent equality tensors of dimension `q`, on the pairs
`(i,j)` and `(k,l)` with the other tensor legs trivial. -/
def wireMatching (q : ℕ) (i j k l : I) : Raw.{0} I K :=
  ((Raw.diagonal (Fin 2) K (Fin q)).group ![i, j]).mul
    ((Raw.diagonal (Fin 2) K (Fin q)).group ![k, l])

/-- A width-`m` matching has the class of `m` independent binary matchings. -/
theorem ofRaw_wireMatching_pow (i j k l : I) (m : ℕ) :
    ofRaw (wireMatching K (2 ^ m) i j k l) = ofRaw (wireMatching K 2 i j k l) ^ m := by
  simp only [wireMatching, ofRaw_mul, ofRaw_group_diagonal_fin_pow, mul_pow]

omit [Fintype I] [Nonempty I] in
private theorem grouped_bitWire_ne_zero (i j : I) :
    ((Raw.diagonal (Fin 2) K (Fin 2)).group ![i, j]).coeff ≠ 0 := by
  apply ((Raw.diagonal (Fin 2) K (Fin 2)).group_ne_zero_iff _).mpr
  intro h
  have hh := congrFun h (fun _ => (0 : Fin 2))
  change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : K) at hh
  simp [Raw.diagonal, funext_iff] at hh

private theorem ofRaw_wireMatching_ne_zero (i j k l : I) : ofRaw (wireMatching K 2 i j k l) ≠ 0 := by
  rw [wireMatching, ofRaw_mul]
  exact mul_ne_zero (fun h => grouped_bitWire_ne_zero K i j ((ofRaw_eq_zero_iff _).mp h))
    (fun h => grouped_bitWire_ne_zero K k l ((ofRaw_eq_zero_iff _).mp h))

private theorem log_wireMatching
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (i j k l : I) :
    Real.logb 2 (φ.val (ofRaw (wireMatching K 2 i j k l)) : ℝ) =
      rawWireDistance φ 1 i j + rawWireDistance φ 1 k l := by
  simpa only [wireMatching, rawWireDistance, rawLogPrice, one_mul] using
    rawLogPrice_mul φ 1 _ _ (grouped_bitWire_ne_zero K i j) (grouped_bitWire_ne_zero K k l)

/-- Tree's four-point inequality on binary wire prices bounds the spectral
value of the crossing by the larger value of the two adjacent matchings. -/
theorem wireMatching_le_max_of_fourPoint
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (a b c d : I)
    (four : rawWireDistance φ 1 a c + rawWireDistance φ 1 b d ≤
      max (rawWireDistance φ 1 a b + rawWireDistance φ 1 c d)
          (rawWireDistance φ 1 a d + rawWireDistance φ 1 b c)) :
    φ.val (ofRaw (wireMatching K 2 a c b d)) ≤
      max (φ.val (ofRaw (wireMatching K 2 a b c d))) (φ.val (ofRaw (wireMatching K 2 a d b c))) := by
  simp only [← log_wireMatching] at four
  have pos (i j k l : I) : 0 < (φ.val (ofRaw (wireMatching K 2 i j k l)) : ℝ) := by
    exact_mod_cast spectral_value_pos φ (ofRaw_wireMatching_ne_zero K i j k l)
  rw [le_max_iff] at four ⊢
  rcases four with h | h
  · left
    exact_mod_cast (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (pos a c b d) (pos a b c d)).mp h
  · right
    exact_mod_cast (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (pos a c b d) (pos a d b c)).mp h

/-- A packet of parallel crossing wires decomposes with the prescribed
overhead into local linear images of the two adjacent matchings. -/
def HasWirePacket (a b c d : I) (σ : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    let R := wireMatching K (2 ^ m) a c b d
    ∃ L : ℕ, (L : ℝ) ≤ (2 : ℝ) ^ (σ * m) ∧ ∃ z : Fin L → (∀ i, R.Leg i) → K,
      R.coeff = ∑ l, z l ∧ ∀ l, ∃ u v : ℕ, u + v = m ∧
        ({R with coeff := z l} : Raw I K).Restricts
          ((wireMatching K (2 ^ u) a b c d).mul (wireMatching K (2 ^ v) a d b c))

/-- At any tolerance `σ > 0` some packet of crossing bits is an ordinary
sum of at most `2^(σ*m)` local linear images of adjacent matchings. In each
summand the two side widths add to the original width `m`. -/
theorem exists_tree_wire_packet (a b c d : I)
    (tree : ∀ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop),
      rawWireDistance φ 1 a c + rawWireDistance φ 1 b d ≤
        max (rawWireDistance φ 1 a b + rawWireDistance φ 1 c d)
            (rawWireDistance φ 1 a d + rawWireDistance φ 1 b c)) {σ : ℝ} (hσ : 0 < σ) :
    HasWirePacket K a b c d σ := by
  obtain ⟨m, hm, hp⟩ := exists_relative_packet _ _ _
    (ofRaw_wireMatching_ne_zero K a c b d) (ofRaw_wireMatching_ne_zero K a b c d)
    (ofRaw_wireMatching_ne_zero K a d b c) (fun φ => wireMatching_le_max_of_fourPoint K φ a b c d
      (tree φ)) hσ
  obtain ⟨L, hL, z, hz, hrestr⟩ := hp _ (ofRaw_wireMatching_pow K a c b d m)
  refine ⟨m, hm, L, hL, z, hz, fun l => ?_⟩
  obtain ⟨u, v, huv, hr⟩ := hrestr l
  refine ⟨u, v, huv, ofRaw_le_iff.mp ?_⟩
  simpa only [ofRaw_mul, ofRaw_wireMatching_pow] using hr

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
