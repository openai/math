import OAI.Computability.BorderVNP.RoutingISASignedPrepInputCut
import OAI.Computability.BorderVNP.RoutingISASignedPrepJoint

/-! # Chronological readback of a rebuilt signed preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube

variable {w dim b h K s : ℕ} (id : TableEntry dim b h K s → ℕ)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {start : Bank w} {initial : Memory w}

/-- Replaying a fitted public schedule, the original routed RAM and the
owned reconstruction returns exactly the seven physical visits, including
their complete intermediate register files and memories. -/
theorem visits_rebuilt (sched : Returns (schedule dim K h) pub mac start initial)
    (empty : sched.val.1.flatMap TeamRAM.Event.choices=[])
    (r : Returns route pub mac sched.val.2.1 sched.val.2.2)
    (c : Returns (CubeConstants.install id) pub mac r.val.2.1 r.val.2.2)
    (o : Returns (TeamRows.ownedGroups dim b h K s) pub mac c.val.2.1 c.val.2.2)
    (tail : LocalTail pub mac o.val.2.1 o.val.2.2) :
    (visitsEquiv id pub mac start initial).symm
      ((fixedScheduleEquiv id sched empty) ⟨r,(inputCut id pub mac c).symm ⟨o,tail⟩⟩) =
      ⟨sched,r,c,o,tail.1,tail.2.1,tail.2.2⟩ := by
  apply (visitsEquiv id pub mac start initial).injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- The projected route and owned-run state omit the dependent type of the
following reports. They suffice for transporting the public scanner receipts. -/
theorem visits_rebuilt_observation (sched : Returns (schedule dim K h) pub mac start initial)
    (empty : sched.val.1.flatMap TeamRAM.Event.choices=[])
    (r : Returns route pub mac sched.val.2.1 sched.val.2.2)
    (c : Returns (CubeConstants.install id) pub mac r.val.2.1 r.val.2.2)
    (o : Returns (TeamRows.ownedGroups dim b h K s) pub mac c.val.2.1 c.val.2.2)
    (tail : LocalTail pub mac o.val.2.1 o.val.2.2) :
    let full := (fixedScheduleEquiv id sched empty) ⟨r,(inputCut id pub mac c).symm ⟨o,tail⟩⟩
    let vis := (visitsEquiv id pub mac start initial).symm full
    (vis.routing.val,vis.constants.val,vis.owned.val)=(r.val,c.val,o.val) :=
  congrArg (fun v : Visits id pub mac start initial => (v.routing.val,v.constants.val,v.owned.val))
    (visits_rebuilt id sched empty r c o tail)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
