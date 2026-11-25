import OAI.Computability.BorderVNP.CubeISAPacketTallyRow
import OAI.Computability.BorderVNP.CubeISASingleTallyPhysical

/-! # Native recomputation of the actual physical declaration row

A strict symbol pair runs its own packet loop and both disjoint singleton
orientations. A diagonal pair needs only its one singleton loop. Starting
with zero row words gives precisely the row of the physical declaration
tested by the two groups, with no reliance on a supplied subtotal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.DeclaredRow

open Cube Cube.Physical Cube.Physical.Owned VPVNP.BurstRAM

variable {n d blocks K h : ℕ}

/-- The sum of selected packet contributions in one strict row. -/
def packetCount (B s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (sym : Symbols d) (j : Fin (n+1)) : ℕ :=
  ∑ t : {t : Fin (packetTrials n d blocks) // packetTrialValid t},
    crossCount B s select (.inl (packetRowEquiv i sym t).val) j

/-- The three local loops partition the strict row, including all singleton offsets. -/
theorem strict_partition (B s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i j : Fin (n+1)) (sym : Symbols d) :
    packetCount B s select i sym j +
      SingleTally.countAt B s select i sym.val.1 sym.val.2 j +
      SingleTally.countAt B s select i sym.val.2 sym.val.1 j =
    subtotals itemRow (crossCount B s select) i (Sym2.mk sym.val.1 sym.val.2) j := by
  have hsum := RowAccum.strictRow_subtotal B s select i j sym
  rw [Fintype.sum_sum_type, ← Nat.add_assoc] at hsum
  exact hsum

/-- Strict-row code executes the packet tally and both ordered singleton passes. -/
def strict (n : ℕ) : Code :=
  .seq (Owned.rowLoop (Owned.packetCandidate n) PacketTally.callback)
    (.seq (SingleTally.oriented n) (.seq SingleTally.swap (SingleTally.oriented n)))

/-- Exact trace allowance of the sparse strict-row traversal. -/
def strictCost (i : Fin (n+1)) (sym : Symbols d) (blocks B K h : ℕ) : ℕ :=
  ((∑ t : Fin (packetTrials n d blocks), (6*n+22 + if packetTrialValid t then
    PacketTally.cost n K h else 1))+1) +
    ((4+SingleTally.rowCost i sym.val.1 sym.val.2 (blocks*(h*B))) +
    (3+(4+SingleTally.rowCost i sym.val.2 sym.val.1 (blocks*(h*B)))))

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)

/-- A real selector tuple stored at its packet bank addresses yields its
full physical subtotal. No memory outside the local row and decoder scratch
is modified. The starting subtotal may be nonzero. -/
theorem strict_run (r : Bank w) (m : Memory w) (i : Fin (n+1)) (sym : Symbols d)
    (B s base scratch bank stride : ℕ) (select : Packet n d blocks → Selector n K h)
    (ready : Owned.packetReady (blocks := blocks) i sym stride bank 0 (.ofWords r m))
    (cfg : SingleTally.Config i sym.val.1 sym.val.2 base (blocks*(h*B)) (.ofWords r m))
    (header : PacketTally.Header (readings m) (readings r 8) n K h base scratch s)
    (room : PacketTally.Rooms w n d blocks K h base scratch (readings r 8) bank stride)
    (ctr : singlePairTrials n d < 2^w) (labelFit : d^(n+1) ≤ 2^w) (dim : n+1 < 2^w)
    (packetFit : ∀ j : Fin (n+1), readings m (base+j.val)+packetTrials n d blocks*(h*s) < 2^w)
    (stored : ∀ p : {p : Packet n d blocks // p.1.1 i = sym},
      SelectorRead.Stored (readings m) (bank+packetIndex p.val*stride) (select p.val))
    (fit : ∀ j : Fin (n+1), readings m (base+j.val) +
      subtotals itemRow (crossCount B s select) i (Sym2.mk sym.val.1 sym.val.2) j < 2^w) :
    BoundedRun pub mac (strict n) r m (strictCost i sym blocks B K h) fun z =>
      (∀ j : Fin (n+1), z.mem (base+j.val) = readings m (base+j.val) +
        subtotals itemRow (crossCount B s select) i (Sym2.mk sym.val.1 sym.val.2) j) ∧
      ∀ x, PacketTally.Outside n h base scratch x → z.mem x = readings m x := by
  let PC := packetCount B s select i sym
  let S := SingleTally.countAt B s select i sym.val.1 sym.val.2
  let T := SingleTally.countAt B s select i sym.val.2 sym.val.1
  have total (j : Fin (n+1)) : PC j + S j + T j =
      subtotals itemRow (crossCount B s select) i (Sym2.mk sym.val.1 sym.val.2) j :=
    strict_partition B s select i j sym
  apply (PacketTally.physical_row_run pub mac r m i sym B s base scratch bank stride select
    ready header room packetFit stored).seq
  intro u mu hp
  have pu (j : Fin (n+1)) : readings mu (base+j.val) = readings m (base+j.val) + PC j := hp.1 j
  have conf := cfg.transfer fun q hq h18 _ => hp.2.2.1 q hq h18
  have headroom (j : Fin (n+1)) : readings mu (base+j.val) + S j < 2^w := by
    have hh := fit j
    rw [← total j] at hh
    rw [pu]
    omega
  apply (SingleTally.oriented_run pub mac i sym.val.1 sym.val.2 base B s select u mu conf ctr labelFit
    dim room.rowWords headroom).seq
  intro v mv hv
  have vv (j : Fin (n+1)) : readings mv (base+j.val) = readings m (base+j.val) + PC j + S j :=
    (hv.2.1 j).trans (congrArg (·+S j) (pu j))
  apply (SingleTally.swap_run pub mac i sym.val.1 sym.val.2 base (blocks*(h*B)) v mv hv.1).seq
  intro y my hy
  have yv : readings my = readings mv := hy.2
  have lastroom (j : Fin (n+1)) : readings my (base+j.val) + T j < 2^w := by
    rw [yv,vv]
    have hh := fit j
    rw [← total j] at hh
    omega
  apply (SingleTally.oriented_run pub mac i sym.val.2 sym.val.1 base B s select y my hy.1 ctr labelFit
    dim room.rowWords lastroom).mono le_rfl
  intro z hz
  constructor
  · intro j
    rw [hz.2.1 j,yv,vv,← total j]
    simp only [T, Nat.add_assoc]
  · intro x hx
    rw [hz.2.2 x hx.1,yv]
    exact (hv.2.2 x hx.1).trans (hp.2.1 x hx)

/-- A diagonal row is exactly the physical ordered singleton pass. -/
theorem diagonal_run (r : Bank w) (m : Memory w) (i : Fin (n+1)) (a : Fin d)
    (B s base : ℕ) (select : Packet n d blocks → Selector n K h)
    (cfg : SingleTally.Config i a a base (blocks*(h*B)) (.ofWords r m))
    (ctr : singlePairTrials n d < 2^w) (labelFit : d^(n+1) ≤ 2^w)
    (dim : n+1 < 2^w) (room : base+(n+1) ≤ 2^w)
    (fit : ∀ j : Fin (n+1), readings m (base+j.val) +
      subtotals itemRow (crossCount B s select) i (Sym2.mk a a) j < 2^w) :
    BoundedRun pub mac (SingleTally.oriented n) r m (4+SingleTally.rowCost i a a (blocks*(h*B))) fun z =>
      (∀ j : Fin (n+1), z.mem (base+j.val) = readings m (base+j.val) +
        subtotals itemRow (crossCount B s select) i (Sym2.mk a a) j) ∧
      ∀ x, x < base ∨ base+(n+1) ≤ x → z.mem x = readings m x := by
  have he (j : Fin (n+1)) : SingleTally.countAt B s select i a a j =
      subtotals itemRow (crossCount B s select) i (Sym2.mk a a) j :=
    RowAccum.diagonalRow_subtotal B s select i j a
  exact (SingleTally.oriented_run pub mac i a a base B s select r m cfg ctr labelFit dim room
    (fun j => (he j).symm ▸ fit j)).mono le_rfl fun _ hz =>
      ⟨fun j => (hz.2.1 j).trans (congrArg (readings m (base+j.val)+·) (he j)), hz.2.2⟩

end RoutingISA.DeclaredRow

end BorderVNP
end Computability
end OAI
