import OAI.Computability.VPVNP.RAMTapeSortRowCrossPass
import OAI.Computability.VPVNP.RAMTapeSortRowBranch

/-! # The cross-site branch of the physical sorting row -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRow

open RAMBoundary Boundary

theorem program_cross_runs {w B : ℕ} (s : Stacks Port) (block : Fin B → RawSlot w)
    (i j : Fin B) (keepMin : Bool) (sent peer : RawSlot w) (st rt : List Bool)
    (h : Ready s block i j false keepMin) (hs : s .crossSend = recordBytes sent ++ st)
    (hr : s .crossReceive = recordBytes peer ++ rt) :
    ∃ t ≤ 4096*(B+1)*(w+1), program.Runs t s
      (result s keepMin (block i) peer (some sent) st rt) := by
  let out := result s keepMin (block i) peer (some sent) st rt
  have hp := crossPass_runs s block i j keepMin sent peer st rt h hs hr
  have run := program_of_cross h.localFlag hp
  simp only [Function.update_self, Function.update_idem, h.partner_eq, List.length_replicate] at run
  have hclear : Function.update out Port.partner [] = out := by
    change Function.update out Port.partner (out .partner) = out
    exact Function.update_eq_self ..
  rw [hclear] at run
  have hc := rowCost_le (w := w) i.isLt.le i.isLt.le
  have hj := j.isLt
  refine ⟨_, ?_, run⟩
  omega

end RAMTape.SortRow

end VPVNP
end Computability
end OAI
