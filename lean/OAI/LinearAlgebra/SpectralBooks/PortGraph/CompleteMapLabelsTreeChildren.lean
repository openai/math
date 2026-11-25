import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsViews

/-! # Reading children from the two port numbers on a wire -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph.MapLabels

open PlanarPatch PlanarCertSize PortView
open scoped Classical

/-- The arrival slot belongs to a tree child precisely when the child designates it as its parent. -/
def childAt {N : ℕ} (z : PortView (BaseAlphabet N) 1) (i : Fin 4) : Option (BaseAlphabet N) :=
  (z.2 i).bind fun (j,w) => if vertexVal w .parentPort = j.val+1 then some w else none

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)

theorem portStep_reverse {v w : V} {i j : Fin 4}
    (h : M.graph.portStep M.slots v i = some (w,j)) : M.graph.portStep M.slots w j = some (v,i) := by
  by_cases hi : ∃ p, M.slots v p = i
  · obtain ⟨⟨⟨e,s⟩,rfl⟩,rfl⟩ := hi
    rw [portStep_port, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    cases s <;> exact M.graph.portStep_port M.slots _
  · rw [portStep_missing _ _ _ _ hi] at h
    contradiction

variable {N : ℕ} (b : V → BaseAlphabet N)
  (hd : DistanceChecks (underlying M.graph.tail M.graph.head) M.root (fun v => vertexVal (b v) .distance))
  (hp : ∀ v, vertexVal (b v) .parentPort = if h : v=M.root then 0 else
    M.slotNat v (canonicalParentPort M.graph M.slotNat M.slotNat_injective hd v h)+1)

private theorem childAt_iff_step (v : V) (i : Fin 4) (a : BaseAlphabet N) :
    childAt (actual M.slots b 1 v) i = some a ↔
      ∃ w j, M.graph.portStep M.slots v i = some (w,j) ∧ vertexVal (b w) .parentPort = j.val+1 ∧ b w=a := by
  cases he : M.graph.portStep M.slots v i with
  | none => simp [childAt, actual, he]
  | some p =>
    rcases p with ⟨w,j⟩
    by_cases eq : vertexVal (b w) .parentPort = j.val + 1 <;> simp [childAt, actual, he, eq]

include hp in
/-- Slots accepted by the local parent test recover exactly the children in the canonical
tree, retaining their parent's port order. -/
theorem childAt_actual_iff (v : V) (i : Fin 4) (a : BaseAlphabet N) :
    childAt (actual M.slots b 1 v) i = some a ↔
      ∃ w ∈ treeChildren M.root (canonicalParent M.graph M.slotNat M.slotNat_injective hd) v,
        canonicalSiblingSlot M.graph M.slotNat M.slotNat_injective hd w = i.val ∧ b w = a := by
  rw [childAt_iff_step]
  constructor
  · rintro ⟨w,j,he,hj,rfl⟩
    have hn : w ≠ M.root := by
      rintro rfl
      simp [hp] at hj
    let p := canonicalParentPort M.graph M.slotNat M.slotNat_injective hd w hn
    have hj' : M.slots w p = j := Fin.ext (by
      rw [hp, dite_eq_right hn] at hj
      exact Nat.add_right_cancel hj)
    have hrev := portStep_reverse M he
    rw [← hj', portStep_port, Option.some.injEq, Prod.mk.injEq] at hrev
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn,
      (canonicalParent_eq_otherEnd _ _ _ hd w hn).trans hrev.1⟩,
      (canonicalSiblingSlot_eq _ _ _ hd w hn).trans (congrArg Fin.val hrev.2), rfl⟩
  · rintro ⟨w,hw,hs,rfl⟩
    obtain ⟨hn, hv⟩ := (Finset.mem_filter.mp hw).2
    let p := canonicalParentPort M.graph M.slotNat M.slotNat_injective hd w hn
    have hdst : otherEnd M.graph p = v := (canonicalParent_eq_otherEnd _ _ _ hd w hn).symm.trans hv
    have hslot : M.slots _ (reversePort M.graph p) = i :=
      Fin.ext ((canonicalSiblingSlot_eq _ _ _ hd w hn).symm.trans hs)
    have he := M.graph.portStep_port M.slots p
    change M.graph.portStep M.slots w (M.slots w p) =
      some (otherEnd M.graph p, M.slots _ (reversePort M.graph p)) at he
    rw [hslot, hdst] at he
    exact ⟨w, M.slots w p, portStep_reverse M he, (hp w).trans (dite_eq_right hn), rfl⟩

end PortGraph.MapLabels

end SpectralBooks
end LinearAlgebra
end OAI
