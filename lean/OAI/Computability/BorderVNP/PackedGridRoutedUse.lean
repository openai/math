import OAI.Computability.BorderVNP.PackedGridSelectedRead
import OAI.Computability.BorderVNP.PackedGridRoutedFactors

/-! # Following a successful original unary report through equality subdivision -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing Diagonal.CellEntries CellSparse
open scoped Classical

variable {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits) (routes : N.WireRoutes)

/-- At an old site the actual routed local tensor reads its original lanes at the
endpoint hops, including self-loops. -/
theorem routed_local_row {R : Type*} [Zero R] [One R] (t : N.Tables R) (v : N.Site)
    (read : CellBox.Lane (N.subdivide routes) (.inl v) → Bool) :
    CellBox.localRow (N.subdivide routes) (N.subdivideTables routes t) (.inl v) read =
      CellBox.localRow N t v (read ∘ endpointLane N routes v) := by
  dsimp only [CellBox.localRow,Network.subdivideTables,Function.comp_apply]
  congr 1
  funext e k
  by_cases h : N.src e.val = v <;> simp [endpointLane,h]

/-- An old rule's physical outcome uses precisely the old lane view of the supplied
new words. Only the selected bit is compared at an old unary source. -/
theorem routed_old_pass (r : ∀ v, Rule N v) (v : N.Site)
    (read : CellBox.Lane (N.subdivide routes) (.inl v) → Bool) (use : Port → Bool) :
    (routedRule N routes r (.inl v)).passes read use =
      (r v).passes (read ∘ endpointLane N routes v) use := by
  cases hr : r v <;> simp [routedRule,hr,Rule.passes,Function.comp_def]

variable {b : ℕ} {T Param Gadget : Type*} [Fintype T] [Fintype Param]
    {tags : N.Tables (Entry Param Gadget)} (sites : PowerSites T Param Gadget b N tags)

/-- Equality subdivision preserves the true or false unary bit at each named old
site, for all choices of the incident routed words. -/
theorem routed_old_selected (w : PowerSlot T Param b)
    (read : CellBox.Lane (N.subdivide routes) (.inl (sites.site w)) → Bool) :
    CellBox.localRow (N.subdivide routes) (sites.subdivision routes).toWords.selected
        (.inl (sites.site w)) read w =
      CellBox.localRow N sites.toWords.selected (sites.site w)
        (read ∘ endpointLane N routes (sites.site w)) w := by
  let v := sites.site w
  have own : (sites.subdivision routes).site w = .inl v := rfl
  have ht := routed_local_row N routes tags v read
  unfold CellBox.localRow at ht ⊢
  dsimp only [v] at own ht
  simp only [PowerSites.toWords, own, true_and]
  rw [ht]
  exact decide_eq_decide.mpr (and_iff_right rfl)

/-- An original unary report proven correct before routing is correct on the
actual local assignment of every surviving routed occurrence. -/
theorem report_at_routed_source (rules : ∀ v, Rule N v) (w : PowerSlot T Param b)
    (port : Port) (use : Port → Bool)
    (original : ∀ read, (rules (sites.site w)).passes read use = true →
      use port = CellBox.localRow N sites.toWords.selected (sites.site w) read w)
    (read : CellBox.Lane (N.subdivide routes) (.inl (sites.site w)) → Bool)
    (ok : (routedRule N routes rules (.inl (sites.site w))).passes read use = true) :
    use port = CellBox.localRow (N.subdivide routes) (sites.subdivision routes).toWords.selected
      (.inl (sites.site w)) read w :=
  (original _ ((routed_old_pass N routes rules _ read use).symm.trans ok)).trans
    (routed_old_selected N routes sites w read).symm

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
