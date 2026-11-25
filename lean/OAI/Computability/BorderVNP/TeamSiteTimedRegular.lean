import OAI.Computability.BorderVNP.TeamSiteTimedDispatch
import OAI.Computability.BorderVNP.TeamSiteRun

/-! # Replaying ordinary loop segments inside the trusted-clock processor

At the private loader boundary an ordinary segment stops. The next segment is
the separately installed, metered native call. All ordinary registers, record
ports and program counters retain their existing physical embeddings.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM TeamPrivateFragment TeamSite.Work
open RAMSerialization (WordRecord)
variable {Q Γ : Type} {w p r k a m g H : ℕ} {hw : 2 ≤ w+1}

/-- Actual location of a local RAM work port, including the shared physical record buffer. -/
abbrev loopPort (q : TeamSite.Port r k ((m+1)*g)) : TeamClocked.Port (Layout.Port r k ((m+1)*g)) :=
  .user (Layout.site q)

theorem loopPort_injective : Function.Injective (loopPort (r:=r) (k:=k) (m:=m) (g:=g)) :=
  (fun _ _ h => Layout.site_injective (TeamClocked.Port.user.inj h))

/-- Genuine outer site label for a local RAM instruction. -/
abbrev loopLabel {P : TeamOpcode.Program p r k a} (last : Bool) (q : Loop.Label P Q (m+1) g) : Label P Q m g :=
  .site (.block (.loop last q))

/-- Elementary loop fragments are cut at entry to the separately metered macro. -/
noncomputable def regular (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ) :
    StackCode (TeamSite.Port r k ((m+1)*g)) (Loop.Label P Q (m+1) g)
  | .privateCall _ _ _ (.load .start) => .halt false
  | q => Loop.code P (fun j => extend (lib j) (mark j)) q

variable (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ)

private theorem regular_row (last : Bool) (q : Loop.Label P Q (m+1) g)
    (h : (regular P lib mark q).returns = false) :
    code P lib mark (loopLabel last q) = (regular P lib mark q).rename loopPort (loopLabel last) := by
  have away : ∀ sg j pc, q ≠ .privateCall sg j pc (.load .start) := by
    rintro sg j pc rfl
    contradiction
  rw [site_row P lib mark _ (fun _ _ _ _ eq => by
    cases eq
    exact away _ _ _ rfl)]
  have mount (op : StackOp (TeamSite.Port r k ((m+1)*g)) (Loop.Label P Q (m+1) g)) :
      (((op.rename Endpoint.Port.site (.loop last)).rename Processor.endpoint .block).rename
        TeamClocked.Port.user Label.site) = op.rename loopPort (loopLabel last) := by
    cases op <;> rfl
  cases q with
  | close sg live | reject => contradiction
  | privateCall sg j pc q =>
    cases q with
    | load t =>
      cases t <;> first | exact (away sg j pc rfl).elim | (simp only [Processor.code,Endpoint.code,regular]; exact mount _)
    | run _ | result _ => simp only [Processor.code,Endpoint.code,regular]; exact mount _
  | _ => simp only [Processor.code,Endpoint.code,regular]; exact mount _

/-- An ordinary loop segment replays on the actual larger processor, preserving
all external ports, including the independent reusable timer. -/
theorem regular_lift (last : Bool) {t q bs q' rest out}
    (base : Stacks (TeamClocked.Port (Layout.Port r k ((m+1)*g))))
    (h : StackRuns (replay (regular P lib mark)) t (q,bs) (base ∘ loopPort) (q',rest) out) :
    StackRuns (replay (code P lib mark)) t (loopLabel last q,bs) base
      (loopLabel last q',rest) (installStacks loopPort base out) := by
  have x := TeamLink.replay_lift h (code P lib mark) loopPort loopPort_injective (loopLabel last) base
    (regular_row P lib mark last)
  rwa [installStacks_eq loopPort_injective base (base ∘ loopPort) (fun _ => rfl)] at x

/-- The guarded opcode fetch, charge, and transition to its callback are entirely
outside private invocation and consume no branch bits. -/
theorem regular_clock (sg : Option Bool) (pub : Fin k → Word w) (s : TeamOpcode.State w p r)
    (block left elapsed max : Word w) (safe : elapsed.val+left.val < 2^w)
    (base : Stacks (TeamSite.Port r k ((m+1)*g)))
    (hc : base ∘ TeamSite.Port.clock = TeamLocalClock.bank pub s block left elapsed max) (bits : List Bool) :
    let x := TeamLocalClock.Loop.result P pub s block left elapsed max
    ∃ n ≤ 1050*(w+1)^2, StackRuns (replay (regular P lib mark)) n (.clock sg (.enter s.pc),bits) base
      (.clock sg (.exit x.1),bits) (installStacks TeamSite.Port.clock base x.2) := by
  intro x
  obtain ⟨n,hn,run⟩ := TeamLocalClock.Loop.step P pub s block left elapsed max safe
  have lift := run.lift TeamSite.Port.clock (fun _ _ h => TeamSite.Port.clock.inj h) (Loop.Label.clock sg) base
    (target := regular P lib mark) (by intro q h; cases q <;> first | rfl | simp [TeamLocalClock.Loop.rows] at h)
  have he := installStacks_eq (fun _ _ h => TeamSite.Port.clock.inj h) base
    (TeamLocalClock.bank pub s block left elapsed max) (congrFun hc)
  exact ⟨n,hn,by simpa only [he] using replay_segment lift bits⟩

/-- The shared timestamp clear runs after every admitted callback, including private zero. -/
theorem regular_reset (sg : Option Bool) (pc : Fin p) (s : Stacks (TeamSite.Port r k ((m+1)*g))) (bs : List Bool) :
    StackRuns (replay (regular P lib mark)) ((s (.clock .stamp)).length+1)
      (Loop.resume sg pc,bs) s (.clock sg (.enter pc),bs) (Function.update s (.clock .stamp) []) :=
  replay_segment (TeamLink.routine_id (SliceArithmetic.CallClear.clear_runs _ s) (regular P lib mark)
    (.reset sg pc) (.clock sg (.enter pc)) (fun _ => rfl)) bs

/-- An ordinary adaptive read or write uses its actual old-word bits and emits the
canonical record pair while preserving the timer boundary. -/
theorem regular_memory (sg : Option Bool) (pc : Fin p) (op : TeamMemoryCallback.Op r)
    (old : Word w) (suffix : List Bool) {rs : List (WordRecord (w+1))}
    {s : Stacks (TeamSite.Port r k ((m+1)*g))} (h : Ready hw H rs s) (pub : Fin k → Word w)
    (state : TeamOpcode.State w p r) (meter : Fin 6 → Word w) (tick cap : Word w)
    (clock : s ∘ TeamSite.Port.clock = TeamLocalClock.banks pub state.logged meter cap (wordBits tick))
    (free : rs.length+2 ≤ 4*H) :
    ∃ t out, t ≤ 186*w+227 ∧ StackRuns (replay (regular P lib mark)) t
      (.clock sg (.exit (.callback (memoryExit pc op))), (wordBits old).reverse ++ suffix) s
      (Loop.resume sg pc,suffix) out ∧ Ready hw H (rs ++ TeamMemoryCallback.pair op state.reg tick old) out ∧
      out ∘ TeamSite.Port.clock = TeamLocalClock.banks pub
        (TeamOpcode.State.logged ⟨pc,TeamMemoryCallback.registers op state.reg old⟩) meter cap (wordBits tick) := by
  have ready := h.memoryReady (pub := pub) (reg := state.reg) (tick := tick)
    (funext fun j => congrFun clock (.isa j)) (congrFun clock .stamp) (congrFun clock .copyScratch)
  obtain ⟨t,b,ht,run,out⟩ := TeamMemoryCallback.run op old suffix ready free
  let label := Loop.Label.memory (P := P) (Q := Q) (m := m+1) (g := g) sg pc op
  have path := TeamLink.replay_lift run (regular P lib mark) memory memory_injective label s (by
    intro j hj; cases j <;> first | rfl | simp [TeamMemoryCallback.code] at hj)
  have first : StackRuns (replay (regular P lib mark)) 1
      (.clock sg (.exit (.callback (memoryExit pc op))), (wordBits old).reverse ++ suffix) s
      (label (TeamMemoryCallback.entry op), (wordBits old).reverse ++ suffix) s := by
    cases op <;> exact .cons (.goto rfl) (.nil ..)
  have last : StackRuns (replay (regular P lib mark)) 1 (label .done,suffix) (withMemory s b)
      (Loop.resume sg pc,suffix) (withMemory s b) := .cons (.goto rfl) (.nil ..)
  rw [installStacks_eq memory_injective s (s ∘ memory) (fun _ => rfl), installMemory] at path
  refine ⟨_,_,by omega,(first.trans path).trans last,h.withMemory out,?_⟩
  funext j
  cases j with
  | isa j => exact congrFun out.registers j
  | stamp => exact out.time
  | copyScratch => exact out.tmp
  | meter j => exact congrFun clock (.meter j)
  | maxBurst => exact congrFun clock .maxBurst

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
