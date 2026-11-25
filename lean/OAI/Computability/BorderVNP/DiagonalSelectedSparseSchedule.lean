import OAI.Computability.BorderVNP.DiagonalSelectedSchedule
import OAI.Computability.BorderVNP.CellSparseExteriorBudget

/-! # Common stretched schedule for the physical sparse packet and signed cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales CellSparse RoutingISA CompactMachine Crossing PackedHistoryCircuit.Normalized

universe u v w

/-- The real compressed private packet, its restore-and-validate clock and its
signed value for all source directories at a fixed stretched length. -/
def SparseCellBudgetAt (A T B j H R k n r : ℕ) : Prop :=
  ∀ M E w p U : ℕ, M ≤ TeamScales.width n (1/5) → E ≤ TeamScales.width n (1/4) → 0 < w → w ≤ n →
    ∀ (D : Directory) (f : SparseExterior.Field), f.width+f.tail.length ≤ E →
    SparseExterior.Ordered f.width 0 f.spans → (∀ s ∈ f.spans, 0<s.bits.length) →
    D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
    D.records.length ≤ 4*(M+E+1)^3 → D.reportedCounts.length ≤ 4*(M+E+1)^3 →
    Packet.storedMass D ≤ A*(M+1)^2 → Packet.RawFields D p U → U.size+1 ≤ B*(logWidth r n+1)^j →
    (∀ row ∈ D.records, (Packet.record row).length ≤ H) → (∀ fs ∈ D.boxes, ∀ z ∈ fs, z.TableBound T) →
    (∀ bs ∈ D.reportedCounts, bs.length ≤ R*(logWidth r n+1)^k) → D.ProfileWidths →
    (CompactFrame.pack w (Packet.input D p f.bytes)).length ≤ TeamScales.width n (1/2) ∧ SparseExterior.clock w D p f ≤ n^25 ∧
      ∑ o ∈ choices SparseExterior.driver n (CompactFrame.pack w (Packet.input D p f.bytes)), o.2.value =
        (CellInput.mk D p f.values).weight

/-- On a fixed length and processor count, the calibrated native call bounds
also give the exact signed value of the restored logical cell. -/
theorem sparseCellBudget_of_privateCalls {A T B j H R k n r : ℕ}
    (paid : SparseExterior.PrivateCallsAt A T B j H R k n r) : SparseCellBudgetAt A T B j H R k n r := by
  intro M E w p U hM hE hw hwn D f hext ord pos static compact rec counts store raw digits format tabs refs hprof
  have bound := paid M E w p U hM hE hw hwn D f hext ord pos static compact rec counts store raw digits format tabs refs
  exact ⟨bound.1,bound.2,SparseExterior.cell_value D p f hw hprof bound.2⟩

/-- A single stretching exponent works for all scalar widths, physical exterior
data and directory values satisfying the certified local geometry. -/
theorem sparse_admissible (A T B j H R k : ℕ) : ∃ ω : ℝ, 0 < ω ∧ AdmissibleRange ω (SparseCellBudgetAt A T B j H R k) := by
  obtain ⟨ω,hω,valid⟩ := SparseExterior.eventually_private_cell A T B j H R k
  refine ⟨ω,hω,?_⟩
  filter_upwards [valid] with n hn
  intro r hr stretch
  apply sparseCellBudget_of_privateCalls
  intro M E w p U
  exact hn r M E w p U hr stretch

variable {D m : ℕ} [NeZero D] {F : Type u} [Field F]

/-- The selected history receipt and the actual zero-restoring private driver
share the same prime-field cube, epochs, stretch and length threshold. -/
theorem exists_selected_sparse_schedule (K : Type*) [Field K] (e : PaidIdentity F D m)
    (hm : 0 < m) (minimum : ℕ) :
    ∃ cube : FixedCube K, minimum ≤ cube.h*cube.b ∧
    ∃ S : SiteSchedule e, (∀ z ≥ S.floor, S.FitsLevels z ∧ S.HasLeaves z ∧ S.RunsEnriched.{v} z) ∧
    ∀ extra : ℕ, ∃ s : EpochScales S (cube.pred+1) extra, ∃ C p : ℕ,
    ∀ E d Q A T B j H R k : ℕ, ∀ limit : ℝ, 0 < limit →
    ∃ b : JointSchedule.{w} s (E+1) (max d p) Q A B j, b.ω ≤ limit ∧
      AdmissibleRange b.ω (selectedReceiptAt.{u,v} S s C p) ∧ AdmissibleRange b.ω (SparseCellBudgetAt A T B j H R k) ∧
      ∀ cut : ℕ, ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
        LengthBudget b cut n ∧ selectedReceiptAt.{u,v} S s C p n r ∧ SparseCellBudgetAt A T B j H R k n r := by
  obtain ⟨cube,hc,S,run,scales⟩ := exists_selected_physical_schedule.{u,v,w} K e hm minimum
  refine ⟨cube,hc,S,run,?_⟩
  intro extra
  obtain ⟨s,C,p,choose⟩ := scales extra
  refine ⟨s,C,p,?_⟩
  intro E d Q A T B j H R k limit hl
  obtain ⟨ω,hω,cell⟩ := sparse_admissible A T B j H R k
  obtain ⟨b,hb,frames,_,lengths⟩ := choose E d Q A T B j H R k (min limit ω) (lt_min hl hω)
  have valid := cell.shrink (hb.trans (min_le_right ..))
  refine ⟨b,hb.trans (min_le_left ..),frames,valid,?_⟩
  intro cut
  filter_upwards [lengths cut,valid.stretched b.rho_omega.le] with n hn localBudget
  exact ⟨hn.1,hn.2.1,localBudget⟩

end Diagonal

end BorderVNP
end Computability
end OAI
