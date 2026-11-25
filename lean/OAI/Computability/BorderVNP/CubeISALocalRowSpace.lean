import OAI.Computability.BorderVNP.CubeISALocalRowAddress
import OAI.Computability.BorderVNP.CubePhysicalDeclarationWords

/-! # Address separation and arithmetic bounds for the physical per-role tally -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned
open BorderVNP.Cube.Tally OwnedRowSetup

variable {l : Layout} {w n b h K s frame actual claimed : ℕ}

/-- The descriptor starts at the exclusive end of the global packet allocation. -/
theorem head_eq (l : Layout) (n b h K s : ℕ) : head l n b h K s =
    l.bank + (l.d*l.d)^(n+1)*2*l.blocks*bankWidth n b h K s := by
  unfold head metadataHead packetTrials
  rw [pow_succ]
  ring

/-- A legal selector prefix fits its physical packet's reservation. -/
theorem selector_room (n b h K s : ℕ) : selectorWidth n K h ≤ bankWidth n b h K s := by
  unfold bankWidth supplyBase
  omega

/-- Every packet ordinal occupies a position in the reserved oriented rectangular bank. -/
theorem index_lt {d blocks : ℕ} (p : Packet n d blocks) : packetIndex p < (d*d)^(n+1)*2*blocks := by
  let x := finFunctionFinEquiv (fun j => finProdFinEquiv (p.1.1 j).val)
  have hx : x.val < (d*d)^(n+1) := x.isLt
  have hb := Bool.toNat_le p.1.2
  have up : x.val*2+p.1.2.toNat+1 ≤ (d*d)^(n+1)*2 := by omega
  have mul := Nat.mul_le_mul_right blocks up
  rw [Nat.add_mul,one_mul] at mul
  change (x.val*2+p.1.2.toNat)*blocks+p.2.val < _
  have := p.2.isLt
  omega

/-- Every actual selector bit lies after the shared declaration array and before
the temporary native descriptor. -/
theorem packetWord_between (p : Packet n l.d l.blocks) (j : Fin (selectorWidth n K h)) :
    let x := l.bank+packetIndex p*bankWidth n b h K s+j.val
    l.bank ≤ x ∧ x < head l n b h K s := by
  intro x
  have hp := Nat.mul_le_mul_right (bankWidth n b h K s) (index_lt p)
  rw [Nat.succ_mul] at hp
  have hj := j.isLt.trans_le (selector_room n b h K s)
  dsimp only [x]
  rw [head_eq]
  omega

/-- Actual nonoverlapping reservations furnish all packet-tallier room and
preservation facts, including its full metadata and rectangular bank. -/
theorem packetRooms (space : Space l w n b h K s frame actual claimed) :
    PacketTally.Rooms w n l.d l.blocks K h actual (head l n b h K s+8) (head l n b h K s)
      l.bank (bankWidth n b h K s) := by
  have bound := space.endRoom
  have bank := bank_le_head l n b h K s
  have ac := space.beforeClaim
  have cl := space.beforeBank
  refine ⟨by omega,space.trials,space.positive,selector_room ..,(head_eq l n b h K s) ▸ (by omega),
    by omega,by omega,.inr (by omega),?_,?_⟩
  · intro k hk
    exact ⟨.inr (by omega),.inl (by omega)⟩
  · intro a left right
    rw [← head_eq] at right
    exact ⟨.inr (by omega),.inl (by omega)⟩

/-- Claims are protected from the local subtotal and the packet decoder's digit writes. -/
theorem claimOutside (space : Space l w n b h K s frame actual claimed) (lo hi : Fin l.d)
    (j : Fin (n+1)) :
    PacketTally.Outside n h actual (head l n b h K s+8) (atPair claimed l.d n lo.val hi.val+j.val) := by
  have bank := row_before_bank space lo hi
  have bankEnd := bank_le_head l n b h K s
  have ac := space.beforeClaim
  have start : claimed ≤ atPair claimed l.d n lo.val hi.val := by simp [atPair]
  have hi := j.isLt
  exact ⟨.inr (by omega),.inl (by omega)⟩

/-- The numerical declaration cap bounds every recomputed incident subtotal at
every grouping coordinate, even before the least-coordinate check. -/
theorem subtotal_le_cap {d blocks : ℕ} (select : Packet n d blocks → Selector n K h)
    (i j : Fin (n+1)) (pair : Sym2 (Fin d)) :
    subtotals itemRow (crossCount b s select) i pair j ≤ declarationCap n d blocks b h s := by
  apply le_trans _ (cutWidth_le_cap b s select j)
  rw [← sum_pair_lengths b s select i j]
  exact Finset.single_le_sum (f := fun row => subtotals itemRow (crossCount b s select) i row j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ pair)

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
