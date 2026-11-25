import OAI.Hierarchy.ProbeDiscrepancy

namespace OAI
/-! # Positive discrepancy threshold at a fixed physical radius -/

noncomputable section
namespace Hierarchy.Probe

open LinearAlgebra.SpectralBooks.ChordGraph

/-- An exactly passing connected price array admits a coordinate assignment with slack.
The same slackened inequalities persist on an open neighborhood of the array.
Minimizing the actual discrepancy on the remaining compact set supplies a single
positive threshold for every price array of this fixed labeled ball. -/
theorem flattening_threshold {F : Type*} [Field F] {S : ℕ} [Nonempty (Fin S)]
    {E A L Z : Type*} [Fintype E] [Nonempty E] [Fintype A] [Finite L]
    (edge : E → Chord S) (req : A → E) (conn : Connected edge)
    (box : Set (E → ℝ)) (compact : IsCompact box)
    (read : L → (E → ℝ) → ℝ) (continuous : ∀ l, Continuous (read l))
    (valid : Z → Prop) (model : Z → L → ℝ) {η : ℝ} (pos : 0<η)
    (realize : ∀ p ∈ box, ¬ Failed F edge req p →
      ∃ z, valid z ∧ ∀ l, |read l p-model z l|≤η/2) :
    ∃ ε : ℝ, 0<ε ∧ ∀ p ∈ box, discrepancy F edge req p≤ε →
      ∃ z, valid z ∧ ∀ l, |read l p-model z l|<η := by
  classical
  let U (z : Z) : Set (E → ℝ) := ⋂ l, {p | |read l p-model z l|<η}
  have openU (z : Z) : IsOpen (U z) := isOpen_iInter_of_finite fun l =>
    isOpen_lt ((continuous l).sub continuous_const).abs continuous_const
  let good : Set (E → ℝ) := ⋃ z : {z // valid z}, U z.val
  have openg : IsOpen good := isOpen_iUnion fun z => openU z.val
  have good_iff (p : E → ℝ) : p∈good ↔ ∃ z, valid z ∧ ∀ l, |read l p-model z l|<η := by
    simp [good,U]
  have zero (p : E → ℝ) (inside : p∈box) (out : p∉good) : 0 < discrepancy F edge req p := by
    apply (failed_iff_discrepancy_pos F edge req conn p).mp
    by_contra passed
    obtain ⟨z,hz,small⟩ := realize p inside passed
    exact out ((good_iff p).mpr ⟨z,hz,fun l => (small l).trans_lt (by linarith)⟩)
  let bad := box ∩ goodᶜ
  by_cases some : bad.Nonempty
  · have closed := compact.inter_right openg.isClosed_compl
    obtain ⟨p,hp,minimal⟩ := closed.exists_isMinOn some
      (discrepancy_one_lipschitz F edge req conn).continuous.continuousOn
    have positive := zero p hp.1 hp.2
    refine ⟨discrepancy F edge req p/2,by positivity,?_⟩
    intro q inq near
    apply (good_iff q).mp
    by_contra outside
    have lower : discrepancy F edge req p ≤ discrepancy F edge req q := minimal (show q∈bad from ⟨inq,outside⟩)
    linarith
  · exact ⟨1,zero_lt_one,fun p inside _ => (good_iff p).mp (by
      by_contra outside
      exact some ⟨p,inside,outside⟩)⟩

end Hierarchy.Probe

end
end OAI
