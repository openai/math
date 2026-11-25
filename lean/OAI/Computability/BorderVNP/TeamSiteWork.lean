import OAI.Computability.BorderVNP.TeamSiteLoop
import OAI.Computability.BorderVNP.TeamBurstCallbackReplay

/-! # Work stacks at a team processor's instruction boundaries

The record emitter is shared by ordinary loads, stores and private bursts.
The same bank invariant applies while the ordered words of a burst are waiting
on the private input stack. All architectural and clock words have separate ports.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Work

open VPVNP BurstRAM RAMTape TeamPrivateFragment
open RAMSerialization (WordRecord)

variable {w H p r k d a m g : ℕ} {hw : 2 ≤ w+1} {Q Γ : Type}

/-- Additional workspace cleared when a new burst begins. -/
inductive Aux
  | reverse | marks | width | saved | high | guard (i : TeamBurstGuard.Port)

/-- Physical location of the guard, counter, and private-input assembly scratch. -/
def Aux.port : Aux → Port r k d
  | .reverse => .burst .privateReverse
  | .marks => .burst .marks
  | .width => .burst .width
  | .saved => .burst .saved
  | .high => .high
  | .guard i => .guard i

/-- A complete shared workspace at a callback boundary. The private input can be
occupied between a burst and the native routine to which it is passed. -/
structure Bank (hw : 2 ≤ w+1) (H : ℕ) (rs : List (WordRecord (w+1)))
    (input : List Bool) (s : Stacks (Port r k d)) : Prop where
  /-- The four old probe operands each fit one RAM word. -/
  short : ∀ i, (s (probe (.operand i))).length ≤ w
  /-- Shared widening and arithmetic scratch is available. -/
  scratch : s (probe .temp) = []
  /-- Four widened emitter words fit the sorting word width. -/
  lifted : ∀ i, (s (probe (.lifted i))).length ≤ w+1
  /-- Slots already serialized, with their exact order and remaining capacity. -/
  buffer : RecordBuffer.Holds hw H rs (s ∘ probe ∘ TeamProbeEmit.Port.buffer)
  /-- Reusable serializer fields fit one sorting word. -/
  fields : ∀ j, (s (probe (.buffer (.field j)))).length ≤ w+1
  /-- Remaining scratch discarded before a new burst takes at most a word per port. -/
  aux : ∀ i : Aux, (s i.port).length ≤ w
  /-- The real binary input supplied to the private call. -/
  raw : s (.burst .privateInput) = input
  /-- The private loader's other work stack is empty. -/
  temp : s .privateTemp = []
  /-- Native tapes start empty on every call. -/
  tracks : ∀ j, s (.track j) = []

/-- At an ordinary instruction boundary, the private input has also been cleared. -/
abbrev Ready (hw : 2 ≤ w+1) (H : ℕ) (rs : List (WordRecord (w+1))) (s : Stacks (Port r k d)) :=
  Bank hw H rs [] s

variable {rs : List (WordRecord (w+1))} {input : List Bool} {s : Stacks (Port r k d)}

/-- After raw input initialization the only occupied site ports belong to the
architectural clock and record buffer. Any such bank with the specified
serialized prefix is ready for the first instruction. -/
theorem initial_ready (s : Stacks (Port r k d))
    (empty : ∀ j, (∀ u, j ≠ .clock u) → (∀ u, j ≠ probe (.buffer u)) → s j = [])
    (holds : RecordBuffer.Holds hw H rs (s ∘ probe ∘ TeamProbeEmit.Port.buffer))
    (fields : ∀ j, (s (probe (.buffer (.field j)))).length ≤ w+1) : Ready hw H rs s := by
  have blank (j) (hc : ∀ u, j ≠ .clock u) (hb : ∀ u, j ≠ probe (.buffer u)) : s j = [] :=
    empty j hc hb
  refine ⟨?_,blank _ (by simp) (by simp),?_,holds,fields,?_,
    blank _ (by simp) (by simp),blank _ (by simp) (by simp),fun j => blank _ (by simp) (by simp)⟩
  · intro i; rw [blank _ (by simp) (by simp)]; simp
  · intro i; rw [blank _ (by simp) (by simp)]; simp
  · intro i; cases i <;> rw [blank _ (by simp [Aux.port]) (by simp [Aux.port])] <;> simp

/-- Replacing only clock and architecture stacks preserves the entire work invariant. -/
theorem Bank.installClock (h : Bank hw H rs input s) (c : Stacks (TeamLocalClock.Port r k)) :
    Bank hw H rs input (installStacks Port.clock s c) := by
  have burst (j) : installStacks Port.clock s c (.burst j) = s (.burst j) :=
    installStacks_outside _ _ (by simp)
  have pr : installStacks Port.clock s c ∘ probe = s ∘ probe := funext fun j => burst _
  have aux (i : Aux) : installStacks Port.clock s c i.port = s i.port := by
    cases i <;> apply installStacks_outside <;> simp [Aux.port]
  refine ⟨fun i => (burst _ ▸ h.short i), (burst _).trans h.scratch,
    fun i => (burst _ ▸ h.lifted i), ?_, fun j => (burst _ ▸ h.fields j),
    fun i => (aux i ▸ h.aux i), (burst _).trans h.raw, ?_, ?_⟩
  · change RecordBuffer.Holds hw H rs ((installStacks Port.clock s c ∘ probe) ∘ _)
    rw [pr]; exact h.buffer
  · exact (installStacks_outside _ _ (by simp)).trans h.temp
  · exact fun j => (installStacks_outside _ _ (by simp)).trans (h.tracks j)

/-- Clearing the previous probe's timestamp preserves the complete workspace. -/
theorem Bank.reset (h : Bank hw H rs input s) :
    Bank hw H rs input (Function.update s (.clock .stamp) []) := by
  have eq := installStacks_eq (fun _ _ he => Port.clock.inj he) s (s ∘ Port.clock) (fun _ => rfl)
  rw [← eq, installStacks_update (fun _ _ he => Port.clock.inj he)]
  exact h.installClock _

/-- The common bank gives all operands and scratch required by one ordinary opcode. -/
theorem Bank.memoryReady (h : Bank hw H rs input s) {pub : Fin k → Word w} {reg : Fin r → Word w}
    {tick : Word w} (registers : s ∘ isa = ISA.bank pub 0 reg [])
    (stamp : s (.clock .stamp) = wordBits tick) (scratch : s (.clock .copyScratch) = []) :
    TeamMemoryCallback.Ready hw H pub reg tick rs (s ∘ memory) :=
  ⟨registers,stamp,scratch,h.short,h.scratch,h.lifted,h.buffer,h.fields⟩

/-- The same blank-input bank can be used for any pair of private-call registers,
including equal registers. The burst cap is supplied by the separate clock bank. -/
theorem Bank.burstReady (h : Ready hw H rs s) (addr len : Fin r) {a q tick cap : Word w}
    (address : s (isa (.reg addr)) = wordBits a) (length : s (isa (.reg len)) = wordBits q)
    (stamp : s (.clock .stamp) = wordBits tick) (maxBurst : s (.clock .maxBurst) = wordBits cap) :
    TeamBurstCallbackSetup.Ready hw H addr len a q tick cap rs (s ∘ Loop.burstPort) := by
  refine ⟨address,length,stamp,maxBurst,?_,h.lifted,h.buffer,h.fields⟩
  intro i hi
  simp only [TeamBurstCallbackSetup.overwritten,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h' <;> subst i
  all_goals first
    | exact h.short _
    | exact h.aux .width
    | exact h.aux .saved
    | exact h.aux .marks
    | exact h.aux .reverse
    | exact h.aux .high
    | exact h.aux (.guard _)
    | (change (s (probe .temp)).length ≤ w; simp [h.scratch])
    | (change (s (.burst .privateInput)).length ≤ w; simp [h.raw])

/-- The physical view of an ordinary callback's returned local bank. -/
def withMemory (s : Stacks (Port r k d)) (b : Stacks (TeamMemoryCallback.Port r k)) : Stacks (Port r k d)
  | .clock (.isa j) => b (.inl j)
  | .clock .stamp => b (.inr (.inr false))
  | .clock .copyScratch => b (.inr (.inr true))
  | .burst (.probe j) => b (.inr (.inl j))
  | j => s j

/-- Mounting the ordinary callback changes precisely the stacks in its port map. -/
theorem installMemory (s : Stacks (Port r k d)) (b : Stacks (TeamMemoryCallback.Port r k)) :
    installStacks memory s b = withMemory s b := by
  apply installStacks_frame memory_injective
  · rintro (i | j | bit) <;> first | cases bit <;> rfl | rfl
  · intro i hi
    cases i with
    | clock j =>
      cases j with
      | isa j => exact (hi (.inl j) rfl).elim
      | stamp => exact (hi (.inr (.inr false)) rfl).elim
      | copyScratch => exact (hi (.inr (.inr true)) rfl).elim
      | _ => rfl
    | burst j =>
      cases j with
      | probe j => exact (hi (.inr (.inl j)) rfl).elim
      | _ => rfl
    | _ => rfl

/-- Ordinary loads and stores replace the emitter prefix and retain the full burst
and private workspace, so either kind of operation may follow. -/
theorem Bank.withMemory {rs' : List (WordRecord (w+1))} {pub : Fin k → Word w}
    {reg : Fin r → Word w} {tick : Word w} {b : Stacks (TeamMemoryCallback.Port r k)}
    (h : Bank hw H rs input s) (out : TeamMemoryCallback.Ready hw H pub reg tick rs' b) :
    Bank hw H rs' input (withMemory s b) := by
  refine ⟨out.short,out.scratch,out.lifted,out.buffer,out.fields,?_,h.raw,h.temp,h.tracks⟩
  intro j; have hj := h.aux j; cases j <;> exact hj


/-- The dispatcher's exit corresponding to a fixed ordinary memory operation. -/
def memoryExit (pc : Fin p) : TeamMemoryCallback.Op r → TeamOpcode.Exit p r a
  | .load dst addr => .native (.read dst addr pc)
  | .store addr src => .native (.write addr src pc)

/-- The real loop takes one ordinary memory instruction all the way to its common
resume label. It consumes the previous word's bits, emits the pair, commits the
new register file, and preserves every countdown and the probe timestamp. -/
theorem memory_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (pc : Fin p) (op : TeamMemoryCallback.Op r) (old : Word w) (suffix : List Bool)
    {s : Stacks (Port r k (m*g))} (h : Ready hw H rs s) (pub : Fin k → Word w)
    (state : TeamOpcode.State w p r) (meter : Fin 6 → Word w) (tick cap : Word w)
    (clock : s ∘ Port.clock = TeamLocalClock.banks pub state.logged meter cap (wordBits tick))
    (free : rs.length+2 ≤ 4*H) :
    ∃ t out, t ≤ 186*w+227 ∧ StackRuns (replay (Loop.code P lib)) t
      (.clock sg (.exit (.callback (memoryExit pc op))), (wordBits old).reverse ++ suffix) s
      (Loop.resume sg pc,suffix) out ∧ Ready hw H (rs ++ TeamMemoryCallback.pair op state.reg tick old) out ∧
      out ∘ Port.clock = TeamLocalClock.banks pub
        (TeamOpcode.State.logged ⟨pc,TeamMemoryCallback.registers op state.reg old⟩) meter cap (wordBits tick) := by
  have ready := h.memoryReady (pub := pub) (reg := state.reg) (tick := tick)
    (funext fun j => congrFun clock (.isa j)) (congrFun clock .stamp) (congrFun clock .copyScratch)
  obtain ⟨t,b,ht,run,out⟩ := TeamMemoryCallback.run op old suffix ready free
  let label := Loop.Label.memory (P := P) (Q := Q) (m := m) (g := g) sg pc op
  have path := TeamLink.replay_lift run (Loop.code P lib) memory memory_injective label s (by
    intro j hj; cases j <;> first | rfl | simp [TeamMemoryCallback.code] at hj)
  have first : StackRuns (replay (Loop.code P lib)) 1
      (.clock sg (.exit (.callback (memoryExit pc op))), (wordBits old).reverse ++ suffix) s
      (label (TeamMemoryCallback.entry op), (wordBits old).reverse ++ suffix) s := by
    cases op <;> exact .cons (.goto rfl) (.nil ..)
  have last : StackRuns (replay (Loop.code P lib)) 1 (label .done,suffix) (withMemory s b)
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

end TeamSite.Work

end BorderVNP
end Computability
end OAI
