import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarTreeTotals

/-! # Bounds for the subtree counts in a planar map certificate

Every child contributes its entire count to its parent. At the root, summing
the local counts groups each wire by its tail and each marked dart by its
incident vertex. This keeps parallel wires and the two ports of a loop distinct.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  {r : V} {parent : V → V} {depth weight total : V → ℕ}

/-- Nonnegative subtree totals increase along every parent edge. -/
theorem subtreeTotal_le_parent (ht : SubtreeTotals r parent weight total) {v : V} (hv : v ≠ r) :
    total v ≤ total (parent v) := by
  have hmem : v ∈ treeChildren r parent (parent v) := by simp [treeChildren, hv]
  calc
    total v ≤ ∑ w ∈ treeChildren r parent (parent v), total w :=
      single_le_sum (fun _ _ => Nat.zero_le _) hmem
    _ ≤ total (parent v) := by rw [ht (parent v)]; omega

/-- Following decreasing depths to the root bounds every accepted count. -/
theorem subtreeTotal_le_root (hd : ∀ w, w ≠ r → depth (parent w) < depth w)
    (ht : SubtreeTotals r parent weight total) (v : V) : total v ≤ total r := by
  induction v using (measure depth).wf.induction with
  | h v ih =>
    by_cases hv : v = r
    · exact hv ▸ le_rfl
    · exact (subtreeTotal_le_parent ht hv).trans (ih _ (hd v hv))

theorem subtreeSize_le_card (hd : ∀ w, w ≠ r → depth (parent w) < depth w)
    (ht : SubtreeTotals r parent (fun _ => 1) total) (v : V) : total v ≤ Fintype.card V :=
  (subtreeTotal_le_root hd ht v).trans_eq (root_subtreeSize_eq_card ht)

variable {A E : Type*} {s : Finset A} {owner : A → V}

/-- Assigning each object to one owner counts exactly the selected objects at the root. -/
theorem rootTotal_eq_card_fibers
    (ht : SubtreeTotals r parent (fun v => (s.filter (fun a => owner a = v)).card) total) :
    total r = s.card :=
  (root_total_eq_sum ht).trans (card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)).symm

/-- Each certified subtree counts at most all the selected objects. -/
theorem subtreeTotal_le_card_fibers (hd : ∀ w, w ≠ r → depth (parent w) < depth w)
    (ht : SubtreeTotals r parent (fun v => (s.filter (fun a => owner a = v)).card) total)
    (v : V) : total v ≤ s.card :=
  (subtreeTotal_le_root hd ht v).trans_eq (rootTotal_eq_card_fibers ht)

variable [Fintype E] (G : PortGraph V E)

omit [Fintype V] in
/-- The local number of outgoing ports is exactly the number of wires with
this tail, even when the other endpoint is the same vertex. -/
theorem count_tail_ports (v : V) :
    (univ.filter (fun p : G.Port v => p.val.2 = false)).card =
      (univ.filter (fun e => G.tail e = v)).card := by
  apply card_bij (fun p _ => p.val.1)
  · intro p hp
    obtain ⟨⟨e, b⟩, hb⟩ := p
    have h : b = false := (mem_filter.mp hp).2
    subst b
    exact mem_filter.mpr ⟨mem_univ _, hb⟩
  · intro p hp q hq he
    exact Subtype.ext (Prod.ext he ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm))
  · intro e he
    exact ⟨⟨(e, false), (mem_filter.mp he).2⟩, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩

omit [Fintype V] in
/-- Restricting a dart marking to one vertex can be read on just its incident ports. -/
theorem count_marked_ports [DecidableEq E] (marked : Finset (E × Bool)) (v : V) :
    (univ.filter (fun p : G.Port v => p.val ∈ marked)).card =
      (marked.filter (fun p => G.vertex p.1 p.2 = v)).card := by
  apply card_bij (fun p _ => p.val)
  · exact fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).2, p.property⟩
  · exact fun _ _ _ _ => Subtype.ext
  · intro p hp
    obtain ⟨hm, hv⟩ := mem_filter.mp hp
    exact ⟨⟨p, hv⟩, mem_filter.mpr ⟨mem_univ _, hm⟩, rfl⟩

/-- Each directed wire contributes once at its tail, including a loop. -/
theorem subtreeTailTotal_le_card (hd : ∀ w, w ≠ r → depth (parent w) < depth w)
    (ht : SubtreeTotals r parent (fun v => (univ.filter (fun e => G.tail e = v)).card) total)
    (v : V) : total v ≤ Fintype.card E :=
  subtreeTotal_le_card_fibers hd ht v

/-- Each marked face minimum is one dart. The bound holds for any set of
marked darts, including the empty marking of a dartless map. -/
theorem subtreeFaceTotal_le_card (marked : Finset (E × Bool))
    (hd : ∀ w, w ≠ r → depth (parent w) < depth w)
    (ht : SubtreeTotals r parent
      (fun v => (marked.filter (fun p => G.vertex p.1 p.2 = v)).card) total)
    (v : V) : total v ≤ Fintype.card (E × Bool) :=
  (subtreeTotal_le_card_fibers hd ht v).trans (card_le_univ marked)

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
