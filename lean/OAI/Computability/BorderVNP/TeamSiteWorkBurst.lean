import OAI.Computability.BorderVNP.TeamSiteWork
import OAI.Computability.BorderVNP.TeamBurstProbeGeometry

/-! # Shared physical bank across a private-call burst and native return

The guarded burst reads its operands from the charged RAM, emits the timed
records in order, and passes the words to the native machine through their
shared private-input port. On return the private workspace is empty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Work

open VPVNP BurstRAM RAMTape TeamPrivateFragment
open RAMSerialization (WordRecord)

variable {Q Γ : Type} {r k w p a d m g H : ℕ} {hw : 2 ≤ w+1}
variable {rs : List (WordRecord (w+1))}

/-- Replace only the physical ports accessible to the burst submachine. -/
def withBurst (s : Stacks (Port r k d)) (u : Stacks (TeamBurstCallbackSetup.Port r)) : Stacks (Port r k d)
  | .clock (.isa (.reg i)) => u (.reg i)
  | .clock .stamp => u .stamp
  | .clock .maxBurst => u .maxBurst
  | .burst j => u (.step j)
  | .guard j => u (.guard j)
  | .high => u .high
  | j => s j

/-- Mounting the complete burst leaves all private tape and non-register ISA stacks untouched. -/
theorem installBurst (s : Stacks (Port r k d)) (u : Stacks (TeamBurstCallbackSetup.Port r)) :
    installStacks Loop.burstPort s u = withBurst s u := by
  apply installStacks_frame Loop.burstPort_injective
  · intro j; cases j <;> rfl
  · intro j hj
    cases j with
    | clock j =>
      cases j with
      | isa i =>
        cases i with
        | reg i => exact (hj (.reg i) rfl).elim
        | _ => rfl
      | stamp => exact (hj .stamp rfl).elim
      | maxBurst => exact (hj .maxBurst rfl).elim
      | _ => rfl
    | burst i => exact (hj (.step i) rfl).elim
    | guard i => exact (hj (.guard i) rfl).elim
    | high => exact (hj .high rfl).elim
    | _ => rfl

private theorem burstClock (s : Stacks (Port r k d)) (u : Stacks (TeamBurstCallbackSetup.Port r))
    (regs : ∀ i, u (.reg i) = s (isa (.reg i))) (stamp : u .stamp = s (.clock .stamp))
    (cap : u .maxBurst = s (.clock .maxBurst)) : withBurst s u ∘ Port.clock = s ∘ Port.clock := by
  funext j
  cases j with
  | isa j => cases j with
    | reg i => exact regs i
    | _ => rfl
  | stamp => exact stamp
  | maxBurst => exact cap
  | _ => rfl

/-- A valid physical burst produces the exact record suffix, fills the private
input in chronological order, and retains every clock and architectural port.
Its last transition already enters the real private loader. -/
theorem burst_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (j : Fin a) (addr len : Fin r) (pc : Fin p)
    {s : Stacks (Port r k (m*g))} (h : Ready hw H rs s) (start length tick cap : Word w)
    (address : s (isa (.reg addr)) = wordBits start) (count : s (isa (.reg len)) = wordBits length)
    (stamp : s (.clock .stamp) = wordBits tick) (maxBurst : s (.clock .maxBurst) = wordBits cap)
    (legal : length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)
    (free : rs.length+2*length.val ≤ 4*H) (vs : List (Word w)) (hv : vs.length = length.val) (suffix : List Bool) :
    ∃ t out, t ≤ 1 + TeamBurstCallback.entryCost w length.val + TeamBurstProbe.loopTime w length.val 0 ∧
      StackRuns (replay (Loop.code P lib)) t
        (.clock sg (.exit (.callback (.call j addr len pc))), TeamBurstProbe.choices vs++suffix) s
        (.privateCall sg j pc (.load .start),suffix) out ∧
      Bank hw H (rs++TeamBurstProbe.records start tick vs) (TeamPrivateCall.inputBits vs) out ∧
      out ∘ Port.clock = s ∘ Port.clock := by
  let label := Loop.Label.burst (P := P) (Q := Q) (m := m) (g := g) sg j addr len pc
  let resume := Loop.Label.privateCall (P := P) (Q := Q) (m := m) (g := g) sg j pc (.load .start)
  let base := s ∘ Loop.burstPort
  have ready := h.burstReady addr len address count stamp maxBurst
  obtain ⟨t,u,ht,run,step,raw,marks,width,saved,regs,st,cap',guard,high⟩ :=
    TeamBurstCallback.replay_callback (Loop.code P lib) Loop.burstPort Loop.burstPort_injective label resume
      (fun _ => rfl) s ready legal free vs hv suffix
  rw [installStacks_eq Loop.burstPort_injective s base (fun _ => rfl), installBurst] at run
  have first : StackRuns (replay (Loop.code P lib)) 1
      (.clock sg (.exit (.callback (.call j addr len pc))), TeamBurstProbe.choices vs++suffix) s
      (label (TeamBurstCallback.start addr len),TeamBurstProbe.choices vs++suffix) s := .cons (.goto rfl) (.nil ..)
  refine ⟨_,_,by omega,first.trans run,?_,burstClock s u regs st cap'⟩
  refine ⟨?_,step.scratch,step.lifted,step.buffer,step.fields,?_,
    raw.trans (TeamBurstProbe.bytes_eq_inputBits _),h.temp,h.tracks⟩
  · intro i
    cases i with
    | address => rw [show withBurst s u (probe (.operand .address)) = _ from step.address, length_wordBits]
    | tick => rw [show withBurst s u (probe (.operand .tick)) = _ from step.time, length_wordBits]
    | before => rw [show withBurst s u (probe (.operand .before)) = [] from step.before]; simp
    | after => rw [show withBurst s u (probe (.operand .after)) = [] from step.after]; simp
  · intro aux
    cases aux with
    | reverse => change (u (.step .privateReverse)).length ≤ w; rw [show u (.step .privateReverse) = [] from step.bytes]; simp
    | marks => change (u (.step .marks)).length ≤ w; simp [marks]
    | width => change (u (.step .width)).length ≤ w; simp [width]
    | saved => change (u (.step .saved)).length ≤ w; simp [saved]
    | high => change (u .high).length ≤ w; simp [high]
    | guard i =>
      change (u (.guard i)).length ≤ w; rw [guard]
      cases i with
      | length => change (s (isa (.reg len))).length ≤ w; simp [count]
      | address => exact h.aux (.guard .address)
      | cap => exact h.aux (.guard .cap)
      | _ => exact Nat.zero_le _

/-- An invalid burst takes a deterministic finite prefix to a genuine rejecting
halt in the site loop. No RAM-word or private choices are consumed. -/
theorem reject_burst_label (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (j : Fin a) (addr len : Fin r) (pc : Fin p)
    {s : Stacks (Port r k (m*g))} (h : Ready hw H rs s) (start length tick cap : Word w)
    (address : s (isa (.reg addr)) = wordBits start) (count : s (isa (.reg len)) = wordBits length)
    (stamp : s (.clock .stamp) = wordBits tick) (maxBurst : s (.clock .maxBurst) = wordBits cap)
    (bad : ¬ (length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)) (suffix : List Bool) :
    ∃ t ≤ 1 + TeamBurstCallback.rejectCost w, ∃ b,
      StackRuns (replay (Loop.code P lib)) t
        (.clock sg (.exit (.callback (.call j addr len pc))),suffix) s ((.burst sg j addr len pc (.entry TeamBurstEntry.rejection)),suffix) b ∧
      Loop.code P lib (.burst sg j addr len pc (.entry TeamBurstEntry.rejection)) = .halt false := by
  let label := Loop.Label.burst (P := P) (Q := Q) (m := m) (g := g) sg j addr len pc
  let resume := Loop.Label.privateCall (P := P) (Q := Q) (m := m) (g := g) sg j pc (.load .start)
  obtain ⟨t,ht,b,run,reject⟩ := TeamBurstCallback.start_invalid_label (Loop.code P lib) Loop.burstPort
    Loop.burstPort_injective label resume (fun _ => rfl) s
    (h.burstReady addr len address count stamp maxBurst) bad
  rw [installStacks_eq Loop.burstPort_injective s (s ∘ Loop.burstPort) (fun _ => rfl)] at run
  have first : StackRuns (replay (Loop.code P lib)) 1
      (.clock sg (.exit (.callback (.call j addr len pc))),suffix) s
      (label (TeamBurstCallback.start addr len),suffix) s := .cons (.goto rfl) (.nil ..)
  exact ⟨_,by omega,_,first.trans (replay_segment run suffix),reject⟩

/-- An invalid private call halts with zero weight before any old-word guess. -/
theorem reject_burst (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (j : Fin a) (addr len : Fin r) (pc : Fin p)
    {s : Stacks (Port r k (m*g))} (h : Ready hw H rs s) (start length tick cap : Word w)
    (address : s (isa (.reg addr)) = wordBits start) (count : s (isa (.reg len)) = wordBits length)
    (stamp : s (.clock .stamp) = wordBits tick) (maxBurst : s (.clock .maxBurst) = wordBits cap)
    (bad : ¬ (length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)) (suffix : List Bool) :
    ∃ t ≤ 1 + TeamBurstCallback.rejectCost w, ∃ q b,
      StackRuns (replay (Loop.code P lib)) t
        (.clock sg (.exit (.callback (.call j addr len pc))),suffix) s (q,suffix) b ∧
      Loop.code P lib q = .halt false := by
  obtain ⟨t,ht,b,run,halt⟩ := reject_burst_label P lib sg j addr len pc h start length tick cap
    address count stamp maxBurst bad suffix
  exact ⟨t,ht,_,b,run,halt⟩

/-- The native compiler receives exactly one occupied stack, containing the shared
burst argument. Every loader and private tape scratch location is empty. -/
theorem Bank.privateInput {s : Stacks (Port r k (m*g))} {bits : List Bool}
    (h : Bank hw H rs bits s) : s ∘ privateTape = TeamPrivateInput.initial bits := by
  funext i
  rcases i with bit | i
  · cases bit <;> first | exact h.raw | exact h.temp
  · exact h.tracks i

/-- Native return clears precisely the private stack ports. -/
def clearPrivate (s : Stacks (Port r k d)) : Stacks (Port r k d)
  | .burst .privateInput | .privateTemp | .track _ => []
  | j => s j

/-- Framing the native interpreter's empty return bank clears its shared raw
input, temporary stack, and all its work tapes. -/
theorem installPrivate (s : Stacks (Port r k (m*g))) :
    installStacks privateTape s (fun _ => []) = clearPrivate s := by
  apply installStacks_frame privateTape_injective
  · rintro (b | i) <;> first | cases b <;> rfl | rfl
  · intro i hi
    cases i with
    | burst j => cases j with
      | privateInput => exact (hi (.inl false) rfl).elim
      | _ => rfl
    | privateTemp => exact (hi (.inl true) rfl).elim
    | track j => exact (hi (.inr j) rfl).elim
    | _ => rfl

/-- A native return preserves the completed physical record prefix. -/
theorem Bank.clearPrivate {s : Stacks (Port r k d)} {bits : List Bool} (h : Bank hw H rs bits s) :
    Ready hw H rs (clearPrivate s) := by
  refine ⟨h.short,h.scratch,h.lifted,h.buffer,h.fields,?_,rfl,rfl,fun _ => rfl⟩
  intro j; have hj := h.aux j; cases j <;> exact hj

/-- Execute the mounted signed native subroutine in the site loop, consume its true
choices, multiply the returned sign, and deliver the common resume label. -/
theorem native_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (j : Fin a) (pc : Fin p) (vs : List (Word w))
    {s : Stacks (Port r k (m*g))} (h : Bank hw H rs (TeamPrivateCall.inputBits vs) s)
    {n choices sign u} (native : Run (TeamPrivateTape.trackTable (lib j).alphabet (lib j).table)
      n (lib j).start ((lib j).initial vs) choices sign u) (suffix : List Bool) :
    ∃ t ≤ (2*g+4)*(vs.length*w) + n*(3*(m*g)+2) + 2*(m*g)+6,
      StackRuns (replay (Loop.code P lib)) t (.privateCall sg j pc (.load .start),choices++suffix) s
        (Loop.resume (Loop.times sg sign) pc,suffix) (clearPrivate s) := by
  obtain ⟨t,ht,run⟩ := (lib j).run vs native suffix s h.privateInput
  let label := Loop.Label.privateCall (P := P) (Q := Q) (m := m) (g := g) sg j pc
  have lift := TeamLink.replay_lift run (Loop.code P lib) id Function.injective_id label s (by
    intro q hq; cases q <;> first | rfl | simp [Macro.rows,TeamPrivateCompiler.code] at hq)
  have hid (b : Stacks (Port r k (m*g))) : installStacks id s b = b :=
    funext (installStacks_at Function.injective_id s b)
  rw [hid,hid,installPrivate] at lift
  have last : StackRuns (replay (Loop.code P lib)) 1 (label (.result sign),suffix) (clearPrivate s)
      (Loop.resume (Loop.times sg sign) pc,suffix) (clearPrivate s) := .cons (.goto rfl) (.nil ..)
  exact ⟨_,by omega,lift.trans last⟩

/-- Exact joined execution of one valid private-call instruction on the common bank.
The physical record prefix, register/clock frame, chronological choice spelling,
and multiplied sign all survive return to the next instruction. -/
theorem private_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (j : Fin a) (addr len : Fin r) (pc : Fin p)
    {s : Stacks (Port r k (m*g))} (h : Ready hw H rs s) (start length tick cap : Word w)
    (address : s (isa (.reg addr)) = wordBits start) (count : s (isa (.reg len)) = wordBits length)
    (stamp : s (.clock .stamp) = wordBits tick) (maxBurst : s (.clock .maxBurst) = wordBits cap)
    (legal : length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)
    (free : rs.length+2*length.val ≤ 4*H) (vs : List (Word w)) (hv : vs.length = length.val)
    {n choices sign u} (native : Run (TeamPrivateTape.trackTable (lib j).alphabet (lib j).table)
      n (lib j).start ((lib j).initial vs) choices sign u) (suffix : List Bool) :
    ∃ t out, t ≤ 1 + TeamBurstCallback.entryCost w length.val + TeamBurstProbe.loopTime w length.val 0 +
        ((2*g+4)*(vs.length*w) + n*(3*(m*g)+2) + 2*(m*g)+6) ∧
      StackRuns (replay (Loop.code P lib)) t
        (.clock sg (.exit (.callback (.call j addr len pc))), TeamBurstProbe.choices vs++(choices++suffix)) s
        (Loop.resume (Loop.times sg sign) pc,suffix) out ∧
      Ready hw H (rs++TeamBurstProbe.records start tick vs) out ∧ out ∘ Port.clock = s ∘ Port.clock := by
  obtain ⟨t,b,ht,burst,ready,clock⟩ := burst_run P lib sg j addr len pc h start length tick cap
    address count stamp maxBurst legal free vs hv (choices++suffix)
  obtain ⟨t',ht',run⟩ := native_run P lib sg j pc vs ready native suffix
  exact ⟨_,_,Nat.add_le_add ht ht',burst.trans run,ready.clearPrivate,clock⟩

end TeamSite.Work

end BorderVNP
end Computability
end OAI
