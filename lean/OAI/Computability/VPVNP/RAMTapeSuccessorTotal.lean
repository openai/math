import OAI.Computability.VPVNP.RAMTapeSuccessorChecks
import OAI.Computability.VPVNP.RAMTapeSuccessorSharedValues

/-!
# Return and rejection of the successor guard on shared words

The two checked fields decide whether the continuation is reached. On a valid site the
reader takes its exact scan cost and the guard takes two further instructions. One extra
instruction in the all-branch budget lets the explicit rejecting halt execute when the
incoming verdict is false.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successors

open BurstRAM RAMLayout

variable {d e w : ℕ} (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
  (a : SendArrays d (2^e) w) (s : Stacks Port) (v : Word d)

/-- The verdict stacks at the end of this physical scan test precisely the two local predicates. -/
theorem shared_verdicts_iff :
    ((sharedFinish hc a v s (.verdict .send)).head? = some true ∧
      (sharedFinish hc a v s (.verdict .receive)).head? = some true) ↔
      SuccessorSendOK hw hc a v ∧ SuccessorReceiveOK hw hc a v :=
  (finish_good_iff hw hc s (decide (v.val+1 < 2^d)) (decide (0 < v.val))
    (sharedField a v 0) (sharedField a v 1) ((List.ofFn (incidentBits a v)).drop (16*w))).trans
      (shared_fields_iff hw hc a v)

variable (initial : Word w) (hv : s .address = BurstRAM.wordBits v)
  (hin : s .incident = List.ofFn (RAMLayout.incidentBits a v))
  (hwidth : s .width = List.replicate w true) (hcap : s .cap = BurstRAM.wordBits ⟨2^d * 2^e, hc⟩)
  (hi : s .initial = BurstRAM.wordBits initial) (ht : s .tmp = []) (hu : s .capTmp = [])
  (hblank : ∀ side i, s (.word side i) = [])
include hv hin hwidth hcap hi ht hu hblank

/-- On a canonical pair the exact run preserves the typed output stacks for the next pass. -/
theorem checked_shared_runs (hgood : SuccessorSendOK hw hc a v ∧ SuccessorReceiveOK hw hc a v) :
    checked.Runs (steps d w (decide (0 < v.val)) + 2) s (guardResult (sharedFinish hc a v s)) := by
  have hread := read_incident_runs s v ⟨_, hc⟩ initial _ hv hin hwidth hcap hi ht hu hblank
  have hguard := (shared_verdicts_iff hw hc a s v).mpr hgood
  exact hread.followedBy (guard_runs (sharedFinish hc a v s) hguard.1 hguard.2)

/-- With three guard ticks every malformed pair has stopped. A canonical pair must satisfy
its continuation with the one unused guard tick and the physical output of the scan. -/
theorem checked_shared_allStops (c : ℕ → Stacks Port → Prop) (fuel : ℕ) :
    checked.body.AllStops c (fuel + 3 + steps d w (decide (0 < v.val))) s ↔
      ((SuccessorSendOK hw hc a v ∧ SuccessorReceiveOK hw hc a v) →
        c (fuel + 1) (guardResult (sharedFinish hc a v s))) := by
  have hread := read_incident_runs s v ⟨_, hc⟩ initial _ hv hin hwidth hcap hi ht hu hblank
  exact (checked_allStops_of_read hread c fuel).trans
    (imp_congr_left (shared_verdicts_iff hw hc a s v))

end RAMTape.Successors

end VPVNP
end Computability
end OAI
