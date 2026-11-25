import OAI.Computability.BorderVNP.TeamSiteTimedRegular
import OAI.Computability.BorderVNP.TeamSiteWorkBurst

/-! # Reading the real burst argument before a trusted native private call -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM TeamPrivateFragment
open RAMSerialization (WordRecord)
open private burstClock from OAI.Computability.BorderVNP.TeamSiteWorkBurst

variable {Q Γ : Type} {p reg k routines m g w H : ℕ}
variable (P : TeamOpcode.Program p reg k routines) (lib : Fin routines → Macro Q Γ m g)
variable (mark : Fin routines → Γ)
local notation "SitePort" => TeamSite.Port reg k ((m+1)*g)
local notation "FullPort" => TeamClocked.Port (Layout.Port reg k ((m+1)*g))

/-- The guarded word-gather fragment on the regular work bank, cut exactly at
the private machine entry and reusable by both the integer and field processors. -/
theorem regular_burst_gather (sg : Option Bool) (j : Fin routines) (addr len : Fin reg) (pc : Fin p)
    {hw : 2 ≤ w+1} {rs : List (WordRecord (w+1))} {base : Stacks SitePort}
    (h : Work.Ready hw H rs base)
    (start length tick cap : Word w)
    (address : base (isa (.reg addr)) = wordBits start)
    (count : base (isa (.reg len)) = wordBits length)
    (stamp : base (.clock .stamp) = wordBits tick)
    (maxBurst : base (.clock .maxBurst) = wordBits cap)
    (legal : length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)
    (free : rs.length+2*length.val ≤ 4*H) (vs : List (Word w)) (hv : vs.length = length.val)
    (suffix : List Bool) :
    ∃ t out, t ≤ 1+TeamBurstCallback.entryCost w length.val+TeamBurstProbe.loopTime w length.val 0 ∧
      StackRuns (replay (regular P lib mark)) t
        (.clock sg (.exit (.callback (.call j addr len pc))),TeamBurstProbe.choices vs++suffix)
        base (.privateCall sg j pc (.load .start),suffix) out ∧
      Work.Bank hw H (rs++TeamBurstProbe.records start tick vs) (TeamPrivateCall.inputBits vs) out ∧
      out ∘ Port.clock = base ∘ Port.clock := by
  let s := base
  let label := Loop.Label.burst (P := P) (Q := Q) (m := m+1) (g := g) sg j addr len pc
  let resume := Loop.Label.privateCall (P := P) (Q := Q) (m := m+1) (g := g) sg j pc (.load .start)
  have ready := h.burstReady addr len address count stamp maxBurst
  obtain ⟨t,u,ht,run,step,raw,marks,width,saved,regs,st,cap',guard,high⟩ :=
    TeamBurstCallback.replay_callback (regular P lib mark) Loop.burstPort Loop.burstPort_injective label resume
      (fun _ => rfl) s ready legal free vs hv suffix
  rw [installStacks_eq Loop.burstPort_injective s (s ∘ Loop.burstPort) (fun _ => rfl), Work.installBurst] at run
  refine ⟨t+1,Work.withBurst s u,by omega,.cons (.goto rfl) run,?_,burstClock s u regs st cap'⟩
  refine ⟨?_,step.scratch,step.lifted,step.buffer,step.fields,?_,
    raw.trans (TeamBurstProbe.bytes_eq_inputBits _),h.temp,h.tracks⟩
  · intro i
    cases i with
    | address => rw [show Work.withBurst s u (probe (.operand .address)) = _ from step.address,length_wordBits]
    | tick => rw [show Work.withBurst s u (probe (.operand .tick)) = _ from step.time,length_wordBits]
    | before => rw [show Work.withBurst s u (probe (.operand .before)) = [] from step.before]; simp
    | after => rw [show Work.withBurst s u (probe (.operand .after)) = [] from step.after]; simp
  · intro aux
    cases aux with
    | reverse => change (u (.step .privateReverse)).length ≤ w; rw [show u (.step .privateReverse) = [] from step.bytes]; simp
    | marks => change (u (.step .marks)).length ≤ w; simp [marks]
    | width => change (u (.step .width)).length ≤ w; simp [width]
    | saved => change (u (.step .saved)).length ≤ w; simp [saved]
    | high => change (u .high).length ≤ w; simp [high]
    | guard i =>
      change (u (.guard i)).length ≤ w
      rw [guard]
      cases i with
      | length => change (base (isa (.reg len))).length ≤ w; simp [count]
      | address => exact h.aux (.guard .address)
      | cap => exact h.aux (.guard .cap)
      | _ => exact Nat.zero_le _

/-- The true timed site gathers every old-word bit in order and reaches its genuine
private entry. The checked record suffix, registers, and stacks outside the site
work bank are all determined at this point. -/
theorem burst_gather (last : Bool) (sg : Option Bool) (j : Fin routines) (addr len : Fin reg) (pc : Fin p)
    {hw : 2 ≤ w+1} {rs : List (WordRecord (w+1))} {base : Stacks FullPort}
    (h : Work.Ready hw H rs (base ∘ TeamClocked.Port.user ∘ Layout.site))
    (start length tick cap : Word w)
    (address : base (.user (Layout.site (isa (.reg addr)))) = wordBits start)
    (count : base (.user (Layout.site (isa (.reg len)))) = wordBits length)
    (stamp : base (.user (Layout.site (.clock .stamp))) = wordBits tick)
    (maxBurst : base (.user (Layout.site (.clock .maxBurst))) = wordBits cap)
    (legal : length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)
    (free : rs.length+2*length.val ≤ 4*H) (vs : List (Word w)) (hv : vs.length = length.val)
    (suffix : List Bool) :
    ∃ t out, t ≤ 1+TeamBurstCallback.entryCost w length.val+TeamBurstProbe.loopTime w length.val 0 ∧
      StackRuns (replay (code P lib mark)) t
        (.site (.block (.loop last (.clock sg (.exit (.callback (.call j addr len pc)))))),TeamBurstProbe.choices vs++suffix)
        base (.site (.block (.loop last (.privateCall sg j pc (.load .start)))),suffix) out ∧
      Work.Bank hw H (rs++TeamBurstProbe.records start tick vs) (TeamPrivateCall.inputBits vs)
        (out ∘ TeamClocked.Port.user ∘ Layout.site) ∧
      out ∘ TeamClocked.Port.user ∘ Layout.site ∘ Port.clock = base ∘ TeamClocked.Port.user ∘ Layout.site ∘ Port.clock ∧
      ∀ x, (∀ a : SitePort, TeamClocked.Port.user (Layout.site a) ≠ x) → out x = base x := by
  obtain ⟨t,out,cost,run,bank,clock⟩ := regular_burst_gather P lib mark sg j addr len pc h
    start length tick cap address count stamp maxBurst legal free vs hv suffix
  let bank' := installStacks loopPort base out
  have image : bank' ∘ TeamClocked.Port.user ∘ Layout.site = out := funext (installStacks_at loopPort_injective base out)
  refine ⟨t,bank',cost,regular_lift P lib mark last base run,image ▸ bank,?_,fun x hx => installStacks_outside _ _ hx⟩
  change (bank' ∘ TeamClocked.Port.user ∘ Layout.site) ∘ Port.clock = _
  rw [image]
  exact clock

/-- A failed range guard halts at the real timed site's rejecting label without consuming choices. -/
theorem burst_reject (last : Bool) (sg : Option Bool) (j : Fin routines) (addr len : Fin reg) (pc : Fin p)
    {hw : 2 ≤ w+1} {rs : List (WordRecord (w+1))} {base : Stacks FullPort}
    (h : Work.Ready hw H rs (base ∘ TeamClocked.Port.user ∘ Layout.site))
    (start length tick cap : Word w)
    (address : base (.user (Layout.site (isa (.reg addr)))) = wordBits start)
    (count : base (.user (Layout.site (isa (.reg len)))) = wordBits length)
    (stamp : base (.user (Layout.site (.clock .stamp))) = wordBits tick)
    (maxBurst : base (.user (Layout.site (.clock .maxBurst))) = wordBits cap)
    (bad : ¬ (length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)) (suffix : List Bool) :
    ∃ t ≤ 1+TeamBurstCallback.rejectCost w, ∃ out,
      let q : Label P Q m g := .site (.block (.loop last (.burst sg j addr len pc (.entry TeamBurstEntry.rejection))))
      StackRuns (replay (code P lib mark)) t
        (.site (.block (.loop last (.clock sg (.exit (.callback (.call j addr len pc)))))),suffix)
        base (q,suffix) out ∧ code P lib mark q = .halt false := by
  let s := base ∘ loopPort
  let label := Loop.Label.burst (P := P) (Q := Q) (m := m+1) (g := g) sg j addr len pc
  let resume := Loop.Label.privateCall (P := P) (Q := Q) (m := m+1) (g := g) sg j pc (.load .start)
  obtain ⟨t,ht,b,run,halt⟩ := TeamBurstCallback.start_invalid_label (regular P lib mark) Loop.burstPort
    Loop.burstPort_injective label resume (fun _ => rfl) s (h.burstReady addr len address count stamp maxBurst) bad
  rw [installStacks_eq Loop.burstPort_injective s ((base ∘ TeamClocked.Port.user ∘ Layout.site) ∘ Loop.burstPort) (fun _ => rfl)] at run
  have lift := regular_lift P lib mark last base (replay_segment run suffix)
  refine ⟨t+1,by omega,_,.cons (.goto rfl) lift,?_⟩
  change ((((regular P lib mark (label (.entry TeamBurstEntry.rejection))).rename Endpoint.Port.site
    (Endpoint.Label.loop last)).rename Processor.endpoint Processor.Label.block).rename TeamClocked.Port.user Label.site) =
    .halt false
  rw [halt]; rfl

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
