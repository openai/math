import OAI.Hierarchy.ProtocolRAMCatalogueActiveBill
import OAI.Hierarchy.ProtocolRAMCatalogueAlignment

namespace OAI
/-! # Prices on the dense physical catalogue, including inactive padding -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open AdaptiveProbe ProbeStage ProbeStage.Native ReportSockets CoreBoard

/-- Extend a geometric edge length to a public dense port index. An inactive
padding ordinal has zero price; spent widths have their actual geometric price. -/
def extendedLength {E : Type*} {n : ℕ} (ord : E ↪ Fin n) (cost : E→ℕ) (i : Fin n) : ℝ := by
  classical
  exact if h : ∃e,ord e=i then (cost (Classical.choose h):ℝ) else 0

@[simp] theorem extendedLength_apply {E : Type*} {n : ℕ} (ord : E ↪ Fin n) (cost : E→ℕ) (e : E) :
    extendedLength ord cost (ord e)=cost e := by
  classical
  let h : ∃x,ord x=ord e := ⟨e,rfl⟩
  rw [extendedLength,dite_eq_left h,ord.injective (Classical.choose_spec h)]

theorem extendedLength_nonneg {E : Type*} {n : ℕ} (ord : E ↪ Fin n) (cost : E→ℕ) (i : Fin n) :
    0≤extendedLength ord cost i := by
  classical
  unfold extendedLength
  split <;> positivity

/-- Equality to the actual length field of every row with an installed bit. -/
theorem Alignment.extended_metric {h W k attempts M depth : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {b : Board} {marks : Marks h W k attempts} {rows : Fin b.rows→ProtocolRAMEmit.Row}
    {fixed : Fin b.rows→ℕ} (ord : Catalogue S π depth marks ↪ Fin b.rows)
    (A : Alignment b S π depth marks M rows fixed ord) (i : Fin b.rows) (positive : 0<fixed i) :
    extendedLength ord (lenCode S π depth marks M) i=((rows i).lengthCode:ℝ) := by
  let j : {i : Fin b.rows // 0<fixed i} := ⟨i,positive⟩
  calc
    _=extendedLength ord (lenCode S π depth marks M) (ord (A.ident j)) :=
      congrArg (extendedLength ord (lenCode S π depth marks M)) (A.original j).symm
    _=_ := (extendedLength_apply ord _ (A.ident j)).trans (by exact_mod_cast (A.metric j).symm)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
