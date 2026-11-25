import OAI.LinearAlgebra.SpectralBooks.WireIdentity
import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.ShortenPrice

namespace OAI
/-! # Physical wire charges for the individual protocol terms -/

namespace Hierarchy.AdaptiveProbe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped BigOperators
noncomputable section

variable {S L : ℕ} [Nonempty (Fin S)]

/-- Parallel installed links keep their own widths and fees. Their physical
wire tensor uses the combined width at each unordered pair of sites. -/
def installedWidths (ends : Fin L → Chord S) (bits : Fin L → ℕ) : Widths S :=
  ∑ i, bits i • unitChord (ends i)

omit [Nonempty (Fin S)] in
theorem installed_charge (ends : Fin L → Chord S) (bits : Fin L → ℕ) (d : Chord S → ℝ) :
    (∑ e, (installedWidths ends bits e : ℝ)*d e) = ∑ i, (bits i:ℝ)*d (ends i) := by
  classical
  simp only [installedWidths,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,Nat.cast_sum,
    Nat.cast_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [unitChord,Finsupp.single_apply,apply_ite, ite_mul]

/-- This price calculation holds for every placement, allowing all sites of
the same layer to coincide. Local tables are the actual matrices of the
given restriction to the declared binary wires. -/
theorem placed_term_le {F X : Type*} [Field F] [MetricSpace X]
    (P : SpectralPlacementPrices F X) (site : Fin S → X)
    (ends : Fin L → Chord S) (bits : Fin L → ℕ) (T : Raw.{0} (Fin S) F)
    (localTables : T.Restricts (raw F (installedWidths ends bits))) :
    P.price T site ≤ ∑ i, (bits i:ℝ)*dist (site (ends i).1.1) (site (ends i).1.2) := by
  rcases P.all_zero_or_normalized_at site with zero | ⟨φ,c,_,prices⟩
  · rw [zero]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) dist_nonneg
  · let W := Raw.diagonal (Fin 2) F (Fin 2)
    have priceWire (i j : Fin S) : c*rawWireDistance φ 1 i j = dist (site i) (site j) := by
      have eqn := (prices (W.group ![i,j])).symm.trans
        ((P.group W ![i,j] site).symm.trans (P.wire (site ∘ ![i,j])))
      simpa only [W,rawWireDistance,rawLogPrice,one_mul,Function.comp_apply,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using eqn
    apply (P.placed_mono site localTables).trans_eq
    rw [prices,rawLogPrice,ofRaw_raw,logb_graphClass,Finset.mul_sum]
    calc
      _ = ∑ e, (installedWidths ends bits e : ℝ)*dist (site e.1.1) (site e.1.2) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [←priceWire]
        ring
      _ = _ := installed_charge ends bits _

end
end Hierarchy.AdaptiveProbe

end OAI
