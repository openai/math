import OAI.Computability.BorderVNP.PackedInheritedWorkCapacity
import OAI.Computability.BorderVNP.PackedBankProgramCapacity

/-! # Word room from the public descriptors and separately charged private work -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Epoch Epoch.Round Cover CellAddresses
open private localRecords_mono from OAI.Computability.BorderVNP.ShortenEpochRoundRecords
open scoped Classical

variable {D : ℕ} {P I : Type} [Fintype P] [Fintype I] {bits : P → ℕ} {K : Type*} {lev : ℕ}
variable (p : PlacedPack D P bits K I lev) (program : Site.Programs p.pack.layout)

/-- The programmed site's numeric extent is bounded using only its public
descriptor prior, its separately charged expanded work, and the physical
incident words. The opaque body syntax is not used in this estimate. -/
theorem size_lt_of_bankWithin {B w : ℕ} (cap : RecordsWithin p program.bankFields true B)
    (word : 2*B < 2^w) (v : p.pack.layout.Site) : (program v).program.size < 2^w := by
  let data := program.bankFields
  let one := localRecords p.pack.layout true data.prior data.payload (fun u => u=v)
  have hw : (program v).program.work ≤ one := by
    apply (Nat.le_add_right _ _ : (program v).program.work ≤ (program v).program.expandedLoad).trans
    change data.payload v ≤ one
    simp [one,localRecords,testedWidth,boxCost,recordCost]
    omega
  have hi : (program v).program.incoming ≤ one := (program v).size.le.trans
    (wireCapacity_le p.pack.layout id v data.prior data.payload)
  have hb : one ≤ B := (localRecords_mono p.pack.layout true data.prior data.payload
    (fun u hu => congrArg (fun z => productAddress lev (p.site z)) (show u=v from hu))).trans
    ((Nat.le_add_left _ 1).trans (cap _))
  exact (Nat.add_le_add (hw.trans hb) (hi.trans hb)).trans_lt ((two_mul B).symm.trans_lt word)

end Packing.Inherited.WorkWords

namespace PackedHistoryCircuit.Normalized.Stage

open Crossing Cover Epoch Epoch.Round Shortening Packing Packing.Inherited InheritedBank
open scoped Classical

variable {D m k d lev : ℕ} [NeZero D] {K P I Bin : Type} [Field K] [Fintype P] [Fintype I] [Fintype Bin]
variable {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d} (s : Stage m Bin lev child)
variable (e : PaidIdentity K D m) (q : s.Index e) (old : ∀ i, Site.Programs (child i).pack.layout)
variable {V E np : ℕ} (site : (s.result e q).pack.layout.Site ↪ Fin V) (edge : (s.result e q).pack.layout.Edge ↪ Fin E)
variable (port : Fin k × P ↪ Fin np) (seeds : ((I → Deck (lev+1)) × Bin) → ℕ) (position : e.Entry → ℕ)
variable (data : ∀ i, RecordData (child i).pack.layout)

/-- The true installed lineage at the selected output obeys its bank field
budget in both modes, before the destination's dense cable reindexing. -/
theorem privatePrograms_bankWithin {C T : ℕ} (cert : s.RecordFactor e C) (ex : Bool) (hT : 0<T)
    (cap : ∀ i, RecordsWithin (child i) (data i) ex T)
    (charge : ∀ i v, (old i v).program.publicNodes ≤ (data i).prior v ∧ (old i v).program.expandedLoad ≤ (data i).payload v) :
    RecordsWithin (s.result e q) (s.privatePrograms e q old site edge port seeds position).bankFields ex
      (loadMultiplier e*C*k*T) := by
  intro t
  have bounded := s.bankRecordData_within e q data cert ex T hT cap t
  have small := bankRecords_le (s.result e q).pack.layout (s.privatePrograms e q old site edge port seeds position)
    (s.bankRecordData e q data) ex (fun v =>
      ⟨s.privatePrograms_public_le e q old data site edge port seeds position (fun i u => (charge i u).1) v,
       s.privatePrograms_expanded_le e q old data site edge port seeds position (fun i u => (charge i u).2) v⟩)
    (fun v => productAddress lev ((s.result e q).site v) = t)
  exact (Nat.add_le_add_left small 1).trans bounded

end PackedHistoryCircuit.Normalized.Stage

end BorderVNP
end Computability
end OAI
