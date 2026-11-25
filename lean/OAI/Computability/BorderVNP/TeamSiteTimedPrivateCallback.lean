import OAI.Computability.BorderVNP.TeamSiteTimedBurst
import OAI.Computability.BorderVNP.TeamSiteTimedBudget
import OAI.Computability.BorderVNP.TeamSiteTimedFrame

/-! # The complete metered physical burst callback, including signed resumption -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM TeamPrivateFragment
open RAMSerialization (WordRecord)
variable {Q Γ : Type} {p reg k routines m g w H N : ℕ}

/-- The real processor gathers the declared interval, executes its trusted metered routine,
multiplies the sign, and resumes with the new record suffix and restored external frame. -/
theorem private_callback (P : TeamOpcode.Program p reg k routines) (lib : Fin routines → Macro Q Γ m g)
    (mark : Fin routines → Γ) (last : Bool) (sg : Option Bool) (j : Fin routines) (addr len : Fin reg)
    (pc : Fin p) {hw : 2 ≤ w+1} {rs : List (WordRecord (w+1))}
    {base : Stacks (TeamClocked.Port (Layout.Port reg k ((m+1)*g)))}
    (work : Work.Ready hw H rs (base ∘ loopPort)) (meter : MeterReady base N)
    (start length tick cap : Word w)
    (address : base (loopPort (isa (.reg addr))) = wordBits start)
    (count : base (loopPort (isa (.reg len))) = wordBits length)
    (stamp : base (loopPort (.clock .stamp)) = wordBits tick)
    (maxBurst : base (loopPort (.clock .maxBurst)) = wordBits cap)
    (legal : length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)
    (free : rs.length+2*length.val ≤ 4*H) (vs : List (Word w)) (hv : vs.length = length.val)
    {steps bits sign tracks}
    (native : Run ((lib j).timedTable (mark j)) steps (lib j).start ((lib j).timedInitial (mark j) N vs)
      bits sign tracks) (hn : steps ≤ N) (suffix : List Bool) :
    ∃ t out, t ≤ 1+TeamBurstCallback.entryCost w length.val+TeamBurstProbe.loopTime w length.val 0+
      TimedBudget.meterCoefficient m g*(N+1+vs.length*w)+1 ∧
      StackRuns (replay (code P lib mark)) t
        (loopLabel last (.clock sg (.exit (.callback (.call j addr len pc)))),TeamBurstProbe.choices vs++bits++suffix) base
        (loopLabel last (Loop.resume (Loop.times sg sign) pc),suffix) out ∧
      Work.Ready hw H (rs++TeamBurstProbe.records start tick vs) (out ∘ loopPort) ∧
      out ∘ loopPort ∘ Port.clock = base ∘ loopPort ∘ Port.clock ∧ Framed base out := by
  obtain ⟨t,stage,ht,gather,hbank,hclock,hframe⟩ := burst_gather P lib mark last sg j addr len pc work
    start length tick cap address count stamp maxBurst legal free vs hv (bits++suffix)
  have frame : Framed base stage := hframe
  let bs := TeamPrivateCall.inputBits vs
  have inputs := ready_of_site bs (frame.meter meter) hbank.privateInput
  have call := run_call P lib mark last sg j pc bs N native suffix stage inputs
  let out := installStacks (TeamPrivateMeterCall.wired reg k m g) stage (TeamPrivateMeterCall.finished N)
  have back : StackRuns (replay (code P lib mark)) 1
      (loopLabel last (.privateCall sg j pc (.result sign)),suffix) out
      (loopLabel last (Loop.resume (Loop.times sg sign) pc),suffix) out := .cons (.goto rfl) (.nil ..)
  have cost := TimedBudget.meter_steps (lib j) (mark j) bs N native (by omega)
  rw [show bs.length = vs.length*w from TeamPrivateCall.inputBits_length vs] at cost
  refine ⟨t+(TeamPrivateMeterCall.steps bs N steps tracks+2)+1,out,?_,?_,?_,?_,frame.trans (returned_frame (frame.meter meter))⟩
  · exact Nat.add_le_add_right (Nat.add_le_add ht cost) 1
  · simpa only [List.append_assoc] using (gather.trans call).trans back
  · rw [show out ∘ loopPort = Work.clearPrivate (stage ∘ loopPort) from returned_loop stage N]
    exact hbank.clearPrivate
  · change (out ∘ loopPort) ∘ Port.clock = _
    rw [show out ∘ loopPort = Work.clearPrivate (stage ∘ loopPort) from returned_loop stage N]
    exact hclock

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
