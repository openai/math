import OAI.Computability.BorderVNP.TeamSiteTimedCallback

/-! # One full timed native RAM instruction on the installed physical site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM TeamPrivateFragment
open RAMSerialization (WordRecord)
open TeamEventRecords (physicalSlots)
open private charged_result old_length_le from OAI.Computability.BorderVNP.TeamSiteRun

variable {Q Γ : Type} {w p r k a m g H : ℕ} {hw : 2 ≤ w+1}
local notation "FullBank" => Stacks (TeamClocked.Port (Layout.Port r k ((m+1)*g)))

/-- The true guarded RAM fetch, its actual native callback, and its timestamp reset
form one replay at the physical site. All burst and private choices occur exactly in
the native event's bit string. -/
theorem event_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ)
    (N : ℕ) (pub : Fin k → Word w) (last : Bool) (s next : TeamOpcode.State w p r) (c : Window w)
    (sg : Option Bool) (e : TeamRAM.Event w) (rs : List (WordRecord (w+1))) (base : FullBank) (rest : List Bool)
    (safe : c.Safe) (fits : c.Fits e.action.extra) (cap : e.action.extra ≤ c.cap.val)
    (act : (P.fetch pub (fun j => (lib j).timedEval (mark j) N) s).action = some e.action)
    (go : (P.fetch pub (fun j => (lib j).timedEval (mark j) N) s).advance e.choices e.old = some (next,e.sign))
    (clock : base ∘ loopPort ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs (base ∘ loopPort))
    (meter : MeterReady base N) (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ t out, t ≤ instructionBudget w m g (N+1) e.action.extra + TimedBudget.meterCoefficient m g*(N+1+e.action.extra*w) ∧
      StackRuns (replay (code P lib mark)) t (loopLabel last (.clock sg (.enter s.pc)),eventBits e++rest) base
        (loopLabel last (.clock (Loop.times sg (signBit e.sign)) (.enter next.pc)),rest) out ∧
      Work.Ready hw H (rs++physicalSlots (c.elapsed.val+1) e) (out ∘ loopPort) ∧
      out ∘ loopPort ∘ Port.clock = (c.charge e.action.extra).bank pub next ∧
      (rs++physicalSlots (c.elapsed.val+1) e).length + 2*(c.charge e.action.extra).block.val ≤ 4*H ∧
      Framed base out := by
  let M : TeamOpcode.Macros w a := fun j => (lib j).timedEval (mark j) N
  let prep := TeamOpcode.prepare P pub s
  let win := c.charge e.action.extra
  let tick := c.first
  let cb := win.callbackBank pub prep.2.reg tick
  let mid := installStacks Port.clock (base ∘ loopPort (m:=m) (g:=g)) cb
  let full := installStacks loopPort base mid
  have cr := charged_result P pub M s c e act cap fits
  obtain ⟨n,hn,guard⟩ := regular_clock P lib mark sg pub s c.block c.global c.elapsed c.cap safe (base ∘ loopPort)
    clock (eventBits e++rest)
  rw [cr] at guard
  have staged := regular_lift P lib mark last base guard
  have back : full ∘ loopPort = mid := loop_install base mid
  have cm : (full ∘ loopPort) ∘ Port.clock = cb := by
    rw [back]; exact funext fun u => installStacks_at (fun _ _ he => Port.clock.inj he) ..
  have frame := framed_install base mid
  have wr : Work.Ready hw H rs (full ∘ loopPort) := back ▸ ready.installClock cb
  rw [← TeamOpcode.prepare_action] at act go
  have first := c.first_val safe fits
  obtain ⟨hblock,_,htime,_⟩ := c.charged_values e.action.extra safe fits
  have tickBound : tick.val+e.action.extra ≤ 2^w := by
    have he := (c.charge e.action.extra).elapsed.isLt
    change c.first.val + _ ≤ _; rw [first]; omega
  have count := old_length_le _ _ _ act go
  have room := fits.1
  obtain ⟨t,b,ht,call,hr,cbank,fr⟩ := callback_run P lib mark N last sg prep.1 prep.2 e next win tick pub
    wr (frame.meter meter) cm act go cap tickBound (by omega) rest
  let clean := Function.update (b ∘ loopPort (m:=m) (g:=g)) (.clock .stamp) []
  let out := installStacks loopPort b clean
  have hc : out ∘ loopPort = clean := loop_install b clean
  have reset := regular_lift P lib mark last b
    (regular_reset P lib mark (Loop.times sg (signBit e.sign)) next.pc (b ∘ loopPort) rest)
  have tickLen : ((b ∘ loopPort) (.clock .stamp)).length = w :=
    (congrArg List.length (congrFun cbank .stamp)).trans (BurstRAM.length_wordBits _)
  rw [tickLen] at reset
  rw [show tick.val = c.elapsed.val+1 from first] at hr
  refine ⟨_,out,?_,(staged.trans call).trans reset,hc ▸ hr.reset,?_,?_,frame.trans (fr.trans (framed_install b clean))⟩
  · unfold instructionBudget
    omega
  · change (out ∘ loopPort) ∘ Port.clock = _
    rw [hc]
    exact reset_clock win pub next tick (b ∘ loopPort) cbank
  · rw [List.length_append,hblock]
    have hlen := slots_length_le (c.elapsed.val+1) e
    omega

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
