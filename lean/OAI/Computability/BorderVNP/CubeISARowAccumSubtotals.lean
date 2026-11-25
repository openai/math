import OAI.Computability.BorderVNP.CubeISARowAccumPhysical
import OAI.Computability.BorderVNP.CubeISAOwnedPackets
import OAI.Computability.BorderVNP.CubeISAOwnedSingletons

/-! # The local mixed-radix tallies equal the physical declaration row

A strict row runs the packet counter and both singleton orientations.
A diagonal row has only one singleton orientation. The sums below are over
exactly the accepted positions of those counters and their physical bit slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RowAccum

open Physical Owned
open scoped Classical BigOperators

variable {n d blocks h K : ℕ}

private theorem fiberSum {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] (f : X → ℕ) :
    (∑ x : {x // P x}, f x.val) = ∑ x : X, if P x then f x else 0 := by
  exact (Finset.sum_subtype (Finset.univ.filter P) (fun _ => by simp) f).symm.trans (Finset.sum_filter ..)

private theorem rowSum {width : ℕ} (i j : Fin (n+1)) (r : Sym2 (Fin d))
    (f : Item n d blocks width → Fin (n+1) → ℕ) :
    (∑ p : {p : Packet n d blocks // itemRow i (.inl p : Item n d blocks width) = r}, f (.inl p.val) j) +
    (∑ z : {z : SingleSlot n d blocks width // itemRow i (.inr z : Item n d blocks width) = r},
      f (.inr z.val) j) = subtotals itemRow f i r j := by
  rw [fiberSum (fun p : Packet n d blocks => itemRow i (.inl p : Item n d blocks width) = r)
    (fun p => f (.inl p) j), fiberSum (fun z : SingleSlot n d blocks width =>
      itemRow i (.inr z : Item n d blocks width) = r) (fun z => f (.inr z) j),
    subtotals, Fintype.sum_sum_type]

/-- For unequal row symbols the packet slots and the two disjoint singleton scans
give the actual declared count at every candidate coordinate. -/
theorem strictRow_subtotal (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i j : Fin (n+1)) (sym : Symbols d) :
    (∑ t : {t : Fin (packetTrials n d blocks) // packetTrialValid t},
        crossCount b s select (.inl (packetRowEquiv i sym t).val) j) +
    (∑ k : SingleScan blocks (h*b) i sym.val.1 sym.val.2 ⊕ SingleScan blocks (h*b) i sym.val.2 sym.val.1,
        crossCount b s select (.inr (singleStrictRowEquiv blocks (h*b) i _ _ sym.property.ne k).val) j) =
      subtotals itemRow (crossCount b s select) i (Sym2.mk sym.val.1 sym.val.2) j := by
  let e := (packetRowEquiv (blocks := blocks) i sym).trans
    (Equiv.subtypeEquivRight fun p => (packet_itemRow_eq_iff (width := h*b) i sym p).symm)
  let g := singleStrictRowEquiv blocks (h*b) i sym.val.1 sym.val.2 sym.property.ne
  exact (congrArg₂ (· + ·)
    (Equiv.sum_comp e (fun p => crossCount b s select (.inl p.val) j))
    (Equiv.sum_comp g (fun z => crossCount b s select (.inr z.val) j))).trans (rowSum ..)

/-- For a diagonal row there are no packet contributions and one ordered singleton
scan gives the entire row. In particular the selected cut itself has zero width. -/
theorem diagonalRow_subtotal (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i j : Fin (n+1)) (a : Fin d) :
    (∑ k : SingleScan blocks (h*b) i a a,
        crossCount b s select (.inr (singleDiagRowEquiv blocks (h*b) i a k).val) j) =
      subtotals itemRow (crossCount b s select) i (Sym2.mk a a) j := by
  let g := singleDiagRowEquiv blocks (h*b) i a
  rw [Equiv.sum_comp g (fun z => crossCount b s select (.inr z.val) j)]
  have empty (p : Packet n d blocks) : itemRow i (.inl p : Item n d blocks (h*b)) ≠ Sym2.mk a a :=
    fun eq => packet_row_not_diag i p (eq ▸ Sym2.mk_isDiag_iff.mpr rfl)
  rw [← rowSum i j (Sym2.mk a a) (crossCount b s select),
    fiberSum (fun p : Packet n d blocks => itemRow i (.inl p : Item n d blocks (h*b)) = Sym2.mk a a)
      (fun p => crossCount b s select (.inl p) j)]
  simp [empty]

end Cube.RowAccum

end BorderVNP
end Computability
end OAI
