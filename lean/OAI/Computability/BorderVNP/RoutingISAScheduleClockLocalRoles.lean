import OAI.Computability.BorderVNP.CubeTeamDeclarationEntries
import OAI.Computability.BorderVNP.CubeTeamOwnedRoleCosts
import OAI.Computability.BorderVNP.CubeTeamOwnedDiagonalSound

/-! # The native clock of arbitrary local row returns

A different team may reject its own row. The local bound follows from
the actual scatter trace and this row's checked words alone.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube BorderVNP.Cube.Tally Physical Physical.Owned Scatter TeamRows TeamRowClock
open Padding.Banks TeamRowSources RoutingISA.Owned RoutingISA.OwnedStages VPVNP.BurstRAM DiagonalResidueRAM

variable {w n d blocks b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem returning_test_cost {c : Code} {regs m es t mt} {ticks : ℕ} {ok : Prop} {P : NatState → Prop}
    (checked : TestRun pub mac c regs m ticks ok P) (det : c.deterministic=true)
    (run : Runs pub mac c regs m es t mt) : traceCost es ≤ ticks := by
  obtain ⟨fs,u,mu,other,bound,_⟩ := checked.complete (checked.sound run).1
  rw [(run.unique_of_deterministic det other).1]
  exact bound

/-- Arbitrary returned strict role, including both differently owned
endpoint views. No assumption is made on any unvisited declaration row. -/
theorem strictRole_return_cost (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h)
    {r m es t mt} {src : Set ℕ} (ready : SideReady D A pub src r m) (actual claimed : ℕ)
    (rows : Sym2 (Fin d) → Fin (n+1) → ℕ)
    (input : CheckImage (OwnedStages.layout D A.power A.header) src n actual claimed rows m)
    (space : LocalRow.Space (OwnedStages.layout D A.power A.header) w n b h K s (readings pub 0) actual claimed)
    (labels : d^(n+1) ≤ 2^w) (packets : packetTrials n d blocks*(h*s) < 2^w)
    (cap : declarationCap n d blocks b h s < 2^w)
    (separate : ∀ x ∈ src, x<A.out ∨ A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ x)
    (run : Runs pub mac (strictRole n b h K s) r m es t mt) :
    traceCost es ≤ physicalRoleTicks blocks b h K s D.axis
      (TeamRowSources.oriented D.pair D.high).1 (TeamRowSources.oriented D.pair D.high).2 := by
  obtain ⟨gs,u,mu,hs,rfl,side,check⟩ := CellDispatch.seq_split run
  obtain ⟨_,_,_,_,_,sideCap,_⟩ := strictSide_recover D A pub mac src r m ready side
  obtain ⟨v,z,stored⟩ := strict_check_words D A actual claimed rows ready input space separate side
  have test := LocalRow.strictChecked_run pub mac u mu (v.layout d blocks b h) D.axis D.pair b h K s
    v.actual v.claimed D.select rows z.loaded z.actual z.claimed z.table z.space rfl labels packets cap
    stored z.entry.zero z.entry.one z.entry.axis z.entry.left z.entry.right
  have cost := returning_test_cost test (LocalRow.strictChecked_deterministic ..) check
  rw [strictRole_ticks D A]
  exact (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add sideCap cost)

/-- Returning repeated-symbol role, using only the actual singleton bank
and the checker's own computed subtotals. -/
theorem diagonalRole_return_cost {l : TeamRowPrepare.Layout} (A : Padding.Banks.Data n l.d blocks b h K s)
    (power actual claimed : ℕ) (rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ) (g : Fin l.d) {r m es t mt}
    (ready : DiagonalReady A l power g pub r m)
    (protection : OwnedStages.Protected (rowLayout A l power) n (pub 0).val (source l power n))
    (input : CheckImage (rowLayout A l power) (source l power n) n actual claimed rows m)
    (space : LocalRow.Space (rowLayout A l power) w n b h K s (readings pub 0) actual claimed)
    (labels : l.d^(n+1) ≤ 2^w) (cap : declarationCap n l.d blocks b h s < 2^w)
    (run : Runs pub mac (diagonalRole n b h K s) r m es t mt) :
    traceCost es ≤ physicalRoleTicks blocks b h K s A.axis g g := by
  let key := TeamRowSources.key (g,g)
  let D := A.single g g (l.view key) (l.crossing key)
  let L := rowLayout A l power
  obtain ⟨gs,u,mu,hs,rfl,stage,checker⟩ := CellDispatch.seq_split run
  have hist := singleStage_recover pub mac L D (source l power n) r m
    ready.entry ready.selector ready.crossing ready.loaded ready.fit ready.prepared ready.fields.1 ready.fields.2
    ready.labels ready.bank ready.room.frameFit ready.room.keys ready.room.allocation stage
  let recovered := D.withTape (ChoiceTape.extend (gs.flatMap TeamRAM.Event.choices))
  have after : mu=(recovered.before m (singlePairTrials n l.d)).2 := hist.2.2.2.2.2
  have prepared := D.prepared_withTape (ChoiceTape.extend (gs.flatMap TeamRAM.Event.choices)) m ready.prepared
  have same x (hx : x ∈ source l power n) : mu x=m x :=
    (congrFun after x).trans (recovered.before_source m prepared _ x hx)
  have im := input.transfer same
  have en := ready.entry.keep hist.2.2.1
  have test := LocalRow.diagonalChecked_run pub mac u mu L A.axis g b h K s actual claimed A.select rows
    (protection.loaded ready.loaded same) im.actualAt im.claimedAt im.table space rfl labels cap
    en.zero en.one en.axis en.left en.right
  have cost := returning_test_cost test (LocalRow.diagonalChecked_deterministic ..) checker
  have eq := TeamRows.physicalCostAt_diagonal l A rfl g (l.view key) (l.crossing key)
  rw [TeamRows.physicalCostAt_key l blocks b h K s A.axis rfl (g,g)] at eq
  rw [eq]
  exact (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add hist.2.1 cost)

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
