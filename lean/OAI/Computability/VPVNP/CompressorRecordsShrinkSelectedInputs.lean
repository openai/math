import OAI.Computability.VPVNP.CompressorShrinkInputTerms
import OAI.Computability.VPVNP.CompressorRecordsSelectedArena

/-!
# Old directories available when a shrinking layout has been selected

The term bank starts after the deterministic input arena. Therefore both
greedy columns and the actual incidence arrays fit below the selected
layout's fresh score, position and role tables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkInput.Run

open BurstRAM Compression

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
variable {m : Memory w} (r : Run X T start m)

private theorem origin_bounds : start ≤ placementBase X start ∧ placementBase X start ≤ stop X start := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := range_bounds X start
  exact ⟨h₀,h₁.trans (h₂.trans h₃)⟩

include r

theorem selectedInputs (termBase stride : Word w) (later : stop X start ≤ termBase.val) :
    SelectedArena.OldInputs X termBase stride (placementBank X T start) T := by
  obtain ⟨hc,ho,hm,hs⟩ := r.inputBounds
  obtain ⟨h₀,h₁⟩ := origin_bounds (X := X) (start := start)
  have h : placementBase X start ≤ SelectedArena.origin X termBase stride :=
    h₁.trans (later.trans (Nat.le_add_right ..))
  exact ⟨hc.trans h, ho.trans h, hm.trans h, hs.trans h, (r.greedy.old 3).trans (h₀.trans h)⟩

theorem selectedActualInputs (termBase stride : Word w) (later : stop X start ≤ termBase.val) :
    T.actualIn.val+DemandRAM.oldCount X ≤ SelectedArena.origin X termBase stride ∧
      T.width.val+DemandRAM.oldCount X ≤ SelectedArena.origin X termBase stride := by
  obtain ⟨h₀,h₁⟩ := origin_bounds (X := X) (start := start)
  have h := h₀.trans (h₁.trans (later.trans (Nat.le_add_right termBase.val (SelectedArena.motifs X*stride.val))))
  exact ⟨(r.greedy.old 4).trans h,(r.greedy.old 5).trans h⟩

/-- Specialization to the native term bank after the compact AB/CD pairs. -/
theorem termInputs (stride : Word w) (room : termEnd X start stride.val < 2^w) :
    SelectedArena.OldInputs X (termHead X start) stride (placementBank X T start) T ∧
    T.actualIn.val+DemandRAM.oldCount X ≤ SelectedArena.origin X (termHead X start) stride ∧
    T.width.val+DemandRAM.oldCount X ≤ SelectedArena.origin X (termHead X start) stride := by
  let M := ShrinkTermSelection.bundles X * ShrinkTermSelection.ranks a
  change stop X start+2*M+M*stride.val < _ at room
  have h : stop X start ≤ (termHead (w := w) X start).val := by
    change stop X start ≤ (stop X start+2*M) % (2^w)
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  exact ⟨r.selectedInputs _ stride h,r.selectedActualInputs _ stride h⟩

end CompressorRecords.ShrinkInput.Run

end VPVNP
end Computability
end OAI
