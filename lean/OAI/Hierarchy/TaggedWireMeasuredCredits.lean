import OAI.Hierarchy.TaggedWireRowCredit
import OAI.Hierarchy.ProbeNativePacketAmounts

namespace OAI
/-! # A true elected packet's contribution to a native credit destination -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram AdaptiveProbe
open ThreeFlat.Diagonal.MotifOuterTerms
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {d rows w : ℕ} {s : StockCommit} {m : Memory w}
variable {F E A : Type*} [Field F] [Fintype E] [Fintype A] {k : ℕ} [Nonempty (Fin k)]
  {edge : E → Chord k} {req : A → E} {P : Probe.Packet F edge req} {extra : ℕ}
  {ballot : Batch (P.terms+extra) d} {L : PortPlan s ballot m rows} {j : Fin rows}

omit [Nonempty (Fin k)] in
/-- Every elected role contributes its actual histogram width once. Padding,
including positions between real roles, contributes zero. -/
theorem NativePacketRow.credit (R : NativePacketRow P extra ballot L j)
    (accept : Fin s.occurrences → Prop) :
    L.rowCredit j accept =
      ∑ role : E, if accept (L.enum ⟨j,R.ports role⟩) then histWidth P.count R.h role else 0 := by
  classical
  let f : Fin d → ℕ := fun v =>
    if accept (L.enum ⟨j,v⟩) then installedBits s.columns m (L.enum ⟨j,v⟩) else 0
  change (∑ v, f v) = _
  calc
    _ = ∑ v ∈ Finset.univ.map R.ports, f v := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro v _ absent
      have quiet := (R.unused v (by
        intro e h
        exact absent (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,h⟩))).1
      simp [f,quiet]
    _ = ∑ e : E, f (R.ports e) := Finset.sum_map ..
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [f,(R.amounts e).1]

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
