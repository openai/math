import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordGeometry
import OAI.LinearAlgebra.SpectralBooks.FinitePlacementDiameter
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TreeWirePacket

/-! # Restriction classes of chord graphs

A chord of width `m` carries `m` binary equality tensors between its
endpoints. An ordinary packet decomposition straightens two crossing chords
in the restriction order on the entire polygon.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace ChordGraph

open SiteTensor
open scoped BigOperators

variable {k : ℕ} (K : Type*) [Field K] [Nonempty (Fin k)]

/-- A binary equality tensor placed at the endpoints of one chord. -/
def wire (e : Chord k) : TensorClass.{0} (Fin k) K :=
  ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![e.1.1, e.1.2])

/-- Tensor product over the chords with their prescribed widths. -/
def graphClass (w : Widths k) : TensorClass.{0} (Fin k) K :=
  w.prod fun e m => wire K e ^ m

@[simp] theorem graphClass_zero : graphClass (k := k) K 0 = 1 :=
  Finsupp.prod_zero_index

@[simp] theorem graphClass_add (w w' : Widths k) :
    graphClass K (w + w') = graphClass K w * graphClass K w' :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

@[simp] theorem graphClass_single (e : Chord k) (m : ℕ) :
    graphClass K (Finsupp.single e m) = wire K e ^ m :=
  Finsupp.prod_single_index (pow_zero _)

@[simp] theorem graphClass_unitChord (e : Chord k) :
    graphClass K (unitChord e) = wire K e := by simp [unitChord]

@[simp] theorem graphClass_nsmul (m : ℕ) (w : Widths k) :
    graphClass K (m • w) = graphClass K w ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, graphClass_add, ih, pow_succ]

/-- Every wire is a restriction of the complete two-label diagonal. -/
theorem wire_le_two (e : Chord k) : wire K e ≤ 2 := by
  let D := Raw.diagonal (Fin k) K (Fin 2)
  calc
    wire K e ≤ ofRaw (D.group id) := ofRaw_le_iff.mpr
      (Raw.group_diagonal_restricts_of_comp id ![e.1.1, e.1.2] (Fin 2))
    _ = ofRaw D := ofRaw_eq_iff.mpr D.group_id_equivalent
    _ = 2 := ofRaw_diagonal_fin_eq_natCast (Fin k) K 2

/-- The entire graph is a restriction of the diagonal on all its bit labels. -/
theorem graphClass_le (w : Widths k) :
    graphClass K w ≤ ((2 ^ total w : ℕ) : TensorClass.{0} (Fin k) K) := by
  classical
  have htotal : total w = ∑ e ∈ w.support, w e := by
    change ∑ e ∈ w.support, 1 * w e = _
    simp
  rw [Nat.cast_pow, Nat.cast_ofNat, htotal, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun e _ => pow_le_pow_left' (wire_le_two K e) _

private theorem ofRaw_matching (i j s t : Fin k) (hij : i < j) (hst : s < t) (m : ℕ) :
    ofRaw (wireMatching K (2 ^ m) i j s t) =
      graphClass K (m • (unitChord (edge i j hij) + unitChord (edge s t hst))) := by
  rw [ofRaw_wireMatching_pow, graphClass_nsmul, graphClass_add, graphClass_unitChord,
    graphClass_unitChord]
  rfl

variable {a b c d : Fin k}

/-- The packet witness gives a direct-sum upper bound for a crossing packet.
Each leaf has the same total width and is a product of the two side matchings. -/
theorem chord_packet_of_wire_packet (hab : a < b) (hbc : b < c) (hcd : c < d) {σ : ℝ}
    (packet : HasWirePacket K a b c d σ) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : ℕ, (L : ℝ) ≤ (2 : ℝ) ^ (σ * m) ∧
      ∃ u v : Fin L → ℕ, (∀ l, u l + v l = m) ∧
        graphClass K (m • crossing hab hbc hcd) ≤
          ∑ l, graphClass K (u l • parallel hab hbc hcd + v l • nested hab hbc hcd) := by
  classical
  obtain ⟨m, hm, L, hL, z, hz, hr⟩ := packet
  choose u v huv hrestr using hr
  let R := wireMatching K (2 ^ m) a c b d
  have hsum : ofRaw R ≤ ∑ l, ofRaw ({R with coeff := z l} : Raw (Fin k) K) := by
    change ofCoeffs R.coeff ≤ ∑ l, ofCoeffs (z l)
    rw [show R.coeff = ∑ l, z l from hz]
    exact ordinary_sum_le z
  refine ⟨m, hm, L, hL, u, v, huv, ?_⟩
  calc
    _ = ofRaw R := (ofRaw_matching K a c b d (hab.trans hbc) (hbc.trans hcd) m).symm
    _ ≤ _ := hsum
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro l _
      exact (ofRaw_le_iff.mpr (hrestr l)).trans_eq (by
        rw [ofRaw_mul, ofRaw_matching K a b c d hab hcd,
          ofRaw_matching K a d b c (hab.trans (hbc.trans hcd)) hbc, graphClass_add]
        rfl)

end ChordGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
