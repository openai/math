import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarTreeTotals
import OAI.LinearAlgebra.SpectralBooks.PlanarSlotIntervals
import Mathlib.Order.Interval.Finset.Nat

/-! # Preorder names from the local tree equations

Starting at a vertex's preorder name, the next positions run through the
consecutive intervals belonging to its children, in increasing port order.
At the root these intervals together with the root position fill the entire
range of vertex names.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (root : V) (parent : V → V) (slot size name : V → ℕ)
    (hslot : ∀ v, Set.InjOn slot ↑(treeChildren root parent v))
    (hsize : ∀ v, size v = 1 + ∑ w ∈ treeChildren root parent v, size w)
    (hrootSize : size root = Fintype.card V) (hrootName : name root = 1)
    (hname : ∀ w, w ≠ root → name w = name (parent w) + 1 +
      ∑ u ∈ (treeChildren root parent (parent w)).filter (fun u => slot u < slot w), size u)

include hslot hsize hrootSize hrootName hname

/-- The names form the entire interval from one to the number of vertices. -/
theorem preorderName_image_eq :
    Finset.univ.image name = Finset.Ico 1 (1 + Fintype.card V) := by
  classical
  have cover (v : V) : ∀ k < size v, ∃ x, name x = name v + k := by
    induction v using (measure size).wf.induction with
    | h v ih =>
      intro k hk
      cases k with
      | zero => exact ⟨v, by simp⟩
      | succ k =>
        have hs := hsize v
        have hk' : k < ∑ w ∈ treeChildren root parent v, size w := by omega
        obtain ⟨w, hw, hleft, hright⟩ :=
          exists_slot_interval _ slot size (hslot v) hk'
        have hw' : w ≠ root ∧ parent w = v := (Finset.mem_filter.mp hw).2
        have hle := Finset.single_le_sum (f := size) (fun _ _ => Nat.zero_le _) hw
        have hlt : size w < size v := by omega
        let offset := ∑ u ∈ (treeChildren root parent v).filter (fun u => slot u < slot w), size u
        change offset ≤ k at hleft
        change k < offset + size w at hright
        have hn : name w = name v + 1 + offset := by simpa only [hw'.2] using hname w hw'.1
        obtain ⟨x, hx⟩ := ih w hlt (k - offset) (by omega)
        exact ⟨x, by omega⟩
  have sub : Finset.Ico 1 (1 + Fintype.card V) ⊆ Finset.univ.image name := by
    intro j hj
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Ico.mp hj
    obtain ⟨x, hx⟩ := cover root (j - 1) (by omega)
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by omega⟩
  apply (Finset.eq_of_subset_of_card_le sub ?_).symm
  simpa using (Finset.card_image_le (s := Finset.univ) (f := name))

/-- The local preorder numbering equations give an injective vertex name. -/
theorem preorderName_injective : Function.Injective name := by
  have himg := preorderName_image_eq root parent slot size name hslot hsize hrootSize hrootName hname
  have injOn := Finset.injOn_of_card_image_eq (s := Finset.univ) (f := name)
    (by rw [himg]; simp)
  exact fun _ _ h => injOn (Finset.mem_univ _) (Finset.mem_univ _) h

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
