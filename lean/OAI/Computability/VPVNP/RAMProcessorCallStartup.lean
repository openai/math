import OAI.Computability.VPVNP.RAMProcessorCallInvariant
import OAI.Computability.VPVNP.RAMProcessorLogged

/-! # State and native semantics of a freshly charged physical call -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k H F : ℕ} {hw : 2 ≤ w}

/-- State just after charging call startup and initializing the fresh private instruction
configuration, when cumulative cost is below the cap. -/
def Snapshot.prepared (s : Snapshot w p r k) (T : Template p r k) (hlt : s.cost.val < s.cap.val) :=
  (s.afterStart (s.cap-s.cost) ((Nat.succ_le_of_lt hlt).trans_lt s.cap.isLt)).afterFresh T

theorem CallReady.cost_lt {s : Snapshot w p r k} {first ys} (h : CallReady hw H F first s ys)
    (hd : SiteTests.iteration.eval s.tests = .dispatch) : s.cost.val < s.cap.val := by
  rw [SiteTests.iteration_eval] at hd
  split_ifs at hd with hcap hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  exact hr.2.trans_le h.boundary

theorem CallReady.prepared {s : Snapshot w p r k} {first ys} (h : CallReady hw H F first s ys)
    (T : Template p r k) (hlt : s.cost.val < s.cap.val) (hs : 0 < s.siteLeft) :
    InCall hw H F (s.prepared T hlt) ys s.cost 0 := by
  have hg := CallCredit.GlobalCredit.remaining_val s.cap s.cost hlt.le
  refine ⟨⟨h.publicH,h.publicFuel,h.positive,h.boundary,?_,?_,?_,?_,?_,?_,h.tag,h.address,h.value,?_,nofun⟩,
    rfl,rfl,?_⟩
  · change ys.length+(s.siteLeft-1) ≤ 4*H
    have hr := h.room
    omega
  · exact ⟨h.buffer.fit, rfl, rfl, h.buffer.remaining, h.buffer.buffer, h.buffer.output⟩
  · change 0+s.publicFuel ≤ F
    simp [h.publicFuel]
  · change s.publicH-1 ≤ H
    rw [h.publicH]
    omega
  · exact (length_wordBits s.cost).le
  · exact (length_wordBits (0 : Word w)).le
  · intro _
    change (s.cap-s.cost).val-1+(s.cost.val+1) = s.cap.val
    omega
  · change s.cost.val+(1+0) = s.cost.val+1
    omega

/-- Run the template from the current snapshot using its fuel and choices and the least of its
call, global and site probe allowances. -/
def Snapshot.localResult (T : Template p r k) (s : Snapshot w p r k) :=
  (runLocalCall (T.instantiate w s.pub).logProgram s.fuel s.cfg
    (min s.callLeft (min s.globalLeft.val s.siteLeft)) s.choices).output

theorem nativeCall_prepared (T : Template p r k) (s : Snapshot w p r k) (hH : 0 < s.publicH)
    (hs : 0 < s.siteLeft) (hlt : s.cost.val < s.cap.val) :
    nativeCall T s = (s.prepared T hlt).localResult T := by
  let M := T.instantiate w s.pub
  change (runChargedCall M.program s.publicFuel (M.program.start s.cfg.persistent) s.publicH (s.cap.val-s.cost.val) s.siteLeft s.choices).output = _
  rw [← Machine.chargedCall_logged M s.publicFuel s.cfg.persistent s.publicH _ s.siteLeft s.choices]
  let post := s.prepared T hlt
  let a := min post.callLeft (min post.globalLeft.val post.siteLeft)
  have hg := CallCredit.GlobalCredit.remaining_val s.cap s.cost hlt.le
  have he : min s.publicH (min (s.cap.val-s.cost.val) s.siteLeft) = a+1 := by
    change min s.publicH (min (s.cap.val-s.cost.val) s.siteLeft) =
      min (s.publicH-1) (min ((s.cap-s.cost).val-1) (s.siteLeft-1))+1
    omega
  unfold runChargedCall
  rw [he]
  rfl

theorem CallReturn.startProgress {s u : Snapshot w p r k} {old new : List (WordRecord w)}
    {rep tail} (T : Template p r k) (hlt : s.cost.val < s.cap.val)
    (hr : CallReturn (s.prepared T hlt) u old new s.cost 0 rep tail) :
    Progress s u old new [rep] tail := by
  refine ⟨hr.pub,hr.H,hr.fuel,hr.cap,hr.boundary,hr.target,?_,?_,hr.bits,?_⟩
  · apply Cut.ext
    · have hc : u.cost.val = (s.cost.val+1)+rep.probes := hr.cost
      change u.cost.val = s.cost.val + RAMBuckets.cost Report.probes [rep]
      simp [RAMBuckets.cost, hc, Nat.add_assoc]
    · exact hr.state
  ·
    have he : u.siteLeft = s.siteLeft-1-rep.probes := hr.siteLeft
    rw [he, Nat.sub_sub]
    simp [RAMBuckets.cost]
  · simpa only [probeRecords, List.append_nil, Fin.val_zero] using hr.records

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
