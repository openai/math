import OAI.Computability.BorderVNP.TeamSiteTimedOrdinary
import OAI.Computability.BorderVNP.TeamSiteTimedPrivateCallback
import OAI.Computability.BorderVNP.TeamSiteTimedReplay

/-! # Complete charged callbacks at the true native timeout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP BurstRAM RAMTape TeamPrivateFragment TeamSite.Work
open RAMSerialization (WordRecord)
open TeamEventRecords (physicalSlots)
variable {w H p r k a m g : ℕ} {hw : 2 ≤ w+1} {Q Γ : Type}
local notation "FullBank" => Stacks (TeamClocked.Port (Layout.Port r k ((m+1)*g)))

private theorem collect_budget (w m g N q : ℕ) :
    1 + TeamBurstCallback.entryCost w q + TeamBurstProbe.loopTime w q 0 + 1 ≤
      eventBudget w m g (N+1) q := by
  unfold eventBudget TeamBurstCallback.entryCost TeamBurstProbe.loopTime
  ring_nf
  omega

/-- The actual fixed clocked processor implements every successful native event, including
a zero-weight timeout on a malformed private input. It charges one reset per private
call and leaves the template, the enclosing frame and its exact records ready. -/
theorem callback_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ)
    (N : ℕ) (last : Bool) (sg : Option Bool) (out : TeamOpcode.Exit p r a) (bank : PrivateRAM.LogConfig w p r)
    (e : TeamRAM.Event w) (next : TeamOpcode.State w p r) (win : Window w) (tick : Word w)
    (pub : Fin k → Word w) {rs : List (WordRecord (w+1))} {base : FullBank}
    (work : Ready hw H rs (base ∘ loopPort)) (meter : MeterReady base N)
    (clock : base ∘ loopPort ∘ Port.clock = win.callbackBank pub bank.reg tick)
    (action : (out.action (fun j => (lib j).timedEval (mark j) N) bank).action = some e.action)
    (advance : (out.action (fun j => (lib j).timedEval (mark j) N) bank).advance e.choices e.old = some (next,e.sign))
    (cap : e.action.extra ≤ win.cap.val) (time : tick.val+e.action.extra ≤ 2^w)
    (free : rs.length+2*e.old.length ≤ 4*H) (suffix : List Bool) :
    ∃ t b, t ≤ eventBudget w m g (N+1) e.action.extra + TimedBudget.meterCoefficient m g*(N+1+e.action.extra*w) ∧
      StackRuns (replay (code P lib mark)) t
        (loopLabel last (.clock sg (.exit (.callback out))),eventBits e ++ suffix) base
        (loopLabel last (Loop.resume (Loop.times sg (signBit e.sign)) next.pc),suffix) b ∧
      Ready hw H (rs++physicalSlots tick.val e) (b ∘ loopPort) ∧
      b ∘ loopPort ∘ Port.clock = win.callbackBank pub next.reg tick ∧ Framed base b := by
  by_cases ord : ∀ j addr len pc, out ≠ .call j addr len pc
  · obtain ⟨t,b,ht,run,wr,cb⟩ := ordinary_callback P lib mark (fun j => (lib j).timedEval (mark j) N)
      (N+1) sg out bank e next win tick pub work clock ord action advance free suffix
    have lift := regular_lift P lib mark last base run
    let z := installStacks loopPort base b
    have hz : z ∘ loopPort = b := loop_install base b
    exact ⟨t,z,ht.trans (Nat.le_add_right ..),lift,hz ▸ wr,
      (congrArg (· ∘ Port.clock) hz).trans cb,framed_install base b⟩
  · push Not at ord
    obtain ⟨j,addr,len,pc,rfl⟩ := ord
    rcases e with ⟨ac,vs,bits,weight⟩
    change (if (bank.reg addr).val+(bank.reg len).val ≤ 2^w
      then some (.burst (bank.reg addr).val (bank.reg len).val) else none) = some ac at action
    split at action <;> try contradiction
    rename_i legal
    obtain rfl := Option.some.inj action
    change (if vs.length = (bank.reg len).val then ((lib j).timedEval (mark j) N vs bits).map
      (fun z => (⟨pc,bank.reg⟩,z)) else none) = some (next,weight) at advance
    split at advance <;> try contradiction
    rename_i length
    obtain ⟨z,he,eq⟩ := Option.map_eq_some_iff.mp advance
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    obtain ⟨n,hn,sign,u,native,rfl⟩ := ((lib j).timedEval_iff ..).mp he
    have range : (bank.reg addr).val+vs.length ≤ 2^w := length.symm ▸ legal
    have ticks : tick.val+vs.length ≤ 2^w := length.symm ▸ time
    obtain ⟨t,b,ht,run,wr,cb,fr⟩ := private_callback P lib mark last sg j addr len pc work meter
      (bank.reg addr) (bank.reg len) tick win.cap (congrFun clock (.isa (.reg addr))) (congrFun clock (.isa (.reg len)))
      (congrFun clock .stamp) (congrFun clock .maxBurst) ⟨cap,legal⟩ (length ▸ free) vs length native hn suffix
    have eqSlots := TeamEventRecords.burst_slots (bank.reg addr) tick vs bits (TeamPrivateCall.sign sign) range ticks
    rw [length] at eqSlots
    rw [eqSlots] at wr
    have init := collect_budget w m g N (bank.reg len).val
    simp only [eventBits,List.append_assoc,signBit_sign,TeamTranscript.Action.extra]
    refine ⟨t,b,?_,by simpa only [List.append_assoc] using run,wr,cb.trans clock,fr⟩
    rw [length] at ht
    omega

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
