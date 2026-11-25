import OAI.Computability.BorderVNP.PackedBundleBankConfig

/-! # Word fit from the true capacity of each physical receive bank

Only descriptions placed in the same cell enter its stride bound. The fixed-stride
allocator supplies the remaining global address room.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open RoutingISA

variable (banks : CellBanks.Layout) (l : PrivatePlacement.Layout) {w : ℕ}
variable (bankFit : banks.Fits w) (before placed mid : ℕ → ℕ)

include bankFit

private theorem bank_end (c : Fin banks.cells) : banks.bank c.val+banks.stride < 2^w := by
  have step := Nat.mul_le_mul_right banks.stride (show c.val+1 ≤ banks.cells from c.isLt)
  rw [Nat.add_mul,one_mul] at step
  have hb := bankFit.bankRoom
  unfold CellBanks.Layout.bank
  omega

/-- The common configuration word fits whenever the reserved gap fits one stride. -/
theorem bankConfig_fits (gap : ℕ) (capacity : gap ≤ banks.stride) (c : Fin banks.cells) :
    banks.bank c.val+gap < 2^w :=
  (Nat.add_le_add_left capacity _).trans_lt (bank_end banks bankFit c)

/-- The absolute metadata slot in the actual post-allocation RAM is bounded by
the end of its owner's stride. This proves the per-header address premise of
`SectionSpec.of_cellBanks` from the native placement's own per-cell census. -/
theorem bankHeader_fits (layoutFit : l.Fits w before) (cells : l.cells = banks.cells)
    (run : l.Image before l.entries placed)
    (keep : ∀ i : Fin l.entries, mid (l.raw+2*i.val) = placed (l.raw+2*i.val) ∧
      mid (l.raw+2*i.val+1) = placed (l.raw+2*i.val+1))
    (apart : l.raw+2*l.entries ≤ banks.dest ∨ banks.dest+2*banks.cells ≤ l.raw)
    (capacity : ∀ c : Fin banks.cells, before (l.supplied+c.val)+l.gap+
      PrivatePlacement.prefixCounts (l.owner before) l.desc l.entries c.val ≤ banks.stride)
    (i : Fin l.entries) (copies base fine incoming cap : ℕ) :
    (rawHeader (banks.written mid banks.cells) l.raw banks.dest i.val copies base fine incoming cap).siteSlot <
      2^w := by
  have hi := i.isLt
  let c : Fin banks.cells := ⟨l.owner before i.val,cells ▸ layoutFit.owners i.val hi⟩
  have hc := capacity c
  have endRoom := bank_end banks bankFit c
  have hpre : PrivatePlacement.prefixCounts (l.owner before) l.desc i.val c.val ≤
      PrivatePlacement.prefixCounts (l.owner before) l.desc l.entries c.val :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hi.le)
  let mem := banks.written mid banks.cells
  have owner : mem (l.raw+2*i.val) = c.val :=
    (banks.written_outside mid banks.cells _ (by omega)).trans ((keep i).1.trans (run.owner_eq layoutFit hi))
  have slot : mem (l.raw+2*i.val+1) = before (l.supplied+c.val)+l.gap+
      PrivatePlacement.prefixCounts (l.owner before) l.desc i.val c.val :=
    (banks.written_outside mid banks.cells _ (by omega)).trans ((keep i).2.trans (run.slots i.val hi))
  change mem (banks.dest+2*mem (l.raw+2*i.val)+1)+mem (l.raw+2*i.val+1) < _
  rw [owner,slot,show mem (banks.dest+2*c.val+1) = banks.bank c.val from (banks.written_at mid c.isLt).2]
  omega

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
