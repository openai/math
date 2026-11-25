import OAI.Computability.BorderVNP.PackedRoutingPrefix
import OAI.Computability.BorderVNP.PackedCellCapacity

/-! # Incoming data bits at each actual packed cell

A populated row of the seven-word directory uses a subinterval of a private description or
a live site word. Its source processor and offset can be recovered from that word and lane.
Consequently the incident widths can be charged once to retained private boxes and attached
external intervals. The reserved gap in the native address space carries no incoming bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open Crossing Shortening Finset
open scoped Classical
open private rawBit_injective from OAI.Computability.BorderVNP.TransmissionDataAddresses

private theorem embedded_sum_le {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) (f : J → ℕ) :
    ∑ i, f (e i) ≤ ∑ j, f j := by
  rw [← Finset.sum_map univ e f]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

private theorem sum_lanes {I : Type*} [Fintype I] (width : I → ℕ) (test : I → Prop) [DecidablePred test] :
    (∑ b : (i : I) × Fin (width i), if test b.1 then 1 else 0) = testedWidth width test := by
  rw [Fintype.sum_sigma, testedWidth]
  apply sum_congr rfl
  intro i _
  by_cases hi : test i <;> simp [hi]

/-- Even when a destination description or live word straddles several processors, each
of its lanes can be counted at most once by the compact delivery directory. -/
theorem Layout.populated_incoming (d : Layout) (pp lp : ℕ → ℕ × ℕ) (bounds : d.DestinationBounds)
    (c : ℕ) :
    testedWidth (fun i : Fin (d.directory pp lp).length => (d.directory pp lp)[i.val].width)
        (fun i => (d.directory pp lp)[i.val].cell = c) ≤
      (∑ j : Fin d.entries, if (pp j.val).1 = c then d.description else 0) +
      ∑ a : Fin d.teams × Fin d.sites, if (lp (a.1.val*d.sites+a.2.val)).1 = c then d.block else 0 := by
  let toSlot : d.PopulatedBit pp lp ↪ d.DestinationSlot :=
    ⟨d.destinationKey pp lp bounds ∘ d.rawBit pp lp,
      (d.destinationKey_injective pp lp bounds).comp (rawBit_injective d pp lp)⟩
  have owner (b : d.PopulatedBit pp lp) :
      (d.directory pp lp)[b.1.val].cell = (d.keyPlacement pp lp (toSlot b).1).1 :=
    (congrArg Row.cell (d.populatedRow pp lp b.1)).trans
      (d.destinationKey_placement pp lp bounds (d.rawBit pp lp b)).1
  rw [←sum_lanes]
  simp_rw [owner]
  have bound := embedded_sum_le toSlot (fun b => if (d.keyPlacement pp lp b.1).1 = c then 1 else 0)
  rw [sum_lanes d.keyWidth (fun k => (d.keyPlacement pp lp k).1 = c),testedWidth,
    Fintype.sum_sum_type] at bound
  refine bound.trans_eq (congrArg₂ (· + ·) ?_ ?_)
  · apply sum_congr rfl
    intro j _
    by_cases h : (pp j.val).1 = c <;> simp [Layout.keyPlacement,Layout.keyWidth,h]
  · apply sum_congr rfl
    intro a _
    by_cases h : (lp (a.1.val*d.sites+a.2.val)).1 = c <;> simp [Layout.keyPlacement,Layout.keyWidth,h]

/-- The native destination widths fit the receiving cell's retained payloads and physical
free port widths. Both injections are used, since distinct descriptions and distinct live
words may have the same cell owner. -/
theorem Layout.incoming_le_records {D C : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (d : Layout) (N : Network D P bits) (cell : N.Site → Fin C) (pp lp : ℕ → ℕ × ℕ)
    (bounds : d.DestinationBounds) (old : Fin d.entries ↪ N.Site)
    (live : (Fin d.teams × Fin d.sites) ↪ P) (prior payload : N.Site → ℕ)
    (desc : ∀ j, d.description ≤ payload (old j)) (block : ∀ a, bits (live a) = d.block)
    (privateCell : ∀ j : Fin d.entries, (pp j.val).1 = (cell (old j)).val)
    (liveCell : ∀ a : Fin d.teams × Fin d.sites,
      (lp (a.1.val*d.sites+a.2.val)).1 = (cell (N.attach (live a))).val)
    (c : Fin C) :
    testedWidth (fun i : Fin (d.directory pp lp).length => (d.directory pp lp)[i.val].width)
      (fun i => (d.directory pp lp)[i.val].cell = c.val) ≤
        localRecords N true prior payload (fun v => cell v = c) := by
  have b := d.populated_incoming pp lp bounds c.val
  simp_rw [privateCell,liveCell,← Fin.ext_iff] at b
  have privateBound := embedded_sum_le old
    (fun v => if cell v = c then boxCost true (prior v) (payload v) else 0)
  have liveBound := embedded_sum_le live
    (fun p => if cell (N.attach p) = c then recordCost true (bits p) else 0)
  have pr : (∑ j : Fin d.entries, if cell (old j) = c then d.description else 0) ≤
      testedWidth (fun v => boxCost true (prior v) (payload v)) (fun v => cell v = c) := by
    refine le_trans (sum_le_sum (s := univ) ?_) (privateBound.trans_eq ?_)
    swap
    · unfold testedWidth
      exact sum_congr rfl fun j _ => by by_cases h : cell j = c <;> simp [h]
    intro j _
    by_cases hj : cell (old j) = c
    · simp only [hj, ite_true, boxCost, recordCost]
      have := desc j
      omega
    · simp [hj]
  have lv : (∑ a : Fin d.teams × Fin d.sites, if cell (N.attach (live a)) = c then d.block else 0) ≤
      testedWidth (fun p => recordCost true (bits p)) (fun p => cell (N.attach p) = c) := by
    refine le_trans (sum_le_sum (s := univ) ?_) (liveBound.trans_eq ?_)
    swap
    · unfold testedWidth
      exact sum_congr rfl fun p _ => by by_cases h : cell (N.attach p) = c <;> simp [h]
    intro a _
    by_cases ha : cell (N.attach (live a)) = c <;> simp [ha,recordCost,block]
  unfold localRecords
  dsimp only
  omega

end Packing.Directory

end BorderVNP
end Computability
end OAI
