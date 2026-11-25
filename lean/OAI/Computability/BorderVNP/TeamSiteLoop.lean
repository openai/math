import OAI.Computability.BorderVNP.TeamSitePrivate
import OAI.Computability.BorderVNP.TeamBurstCallback

/-! # The physical signed processor instruction loop

A successful clocked dispatch runs its typed callback, clears the previous probe
timestamp, and fetches its successor. The accumulated sign lives entirely in
finite control. Private rejects contribute zero and return to the outer loop.
A terminal block exposes its actual live or accepted state for handoff checking.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Loop

open VPVNP RAMTape BurstRAM TeamPrivateFragment TeamSiteChoices

variable {Q Γ : Type} {p r k a m g w : ℕ}

/-- The accepting sign multiplies in finite control, including absorbing zero. -/
def times : Option Bool → Option Bool → Option Bool
  | some b, some c => some (b ^^ c)
  | _, _ => none

/-- The stored sign represents the product of the signed integer path factors. -/
theorem value_times (b c : Option Bool) :
    (TeamPrivateCall.sign (times b c)).value = (TeamPrivateCall.sign b).value*(TeamPrivateCall.sign c).value := by
  rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> decide

/-- Actual port map for the private burst, using the live clock stamp and the
same record buffer as an ordinary load or store. -/
def burstPort {d : ℕ} : TeamBurstCallbackSetup.Port r → Port r k d
  | .reg i => isa (.reg i)
  | .stamp => .clock .stamp
  | .maxBurst => .clock .maxBurst
  | .step q => .burst q
  | .guard q => .guard q
  | .high => .high

/-- The installed burst fragment preserves the distinct locations of all its operands. -/
theorem burstPort_injective {d : ℕ} : Function.Injective (burstPort (r := r) (k := k) (d := d)) := by
  intro i j h; cases i <;> cases j <;> simp_all [burstPort]

/-- Fixed control of the outer instruction loop. Each callback carries the program
continuation that it will resume, independent of the RAM word size. -/
inductive Label (P : TeamOpcode.Program p r k a) (Q : Type) (m g : ℕ) where
  | clock (sign : Option Bool) (q : TeamLocalClock.Loop.Label P)
  | memory (sign : Option Bool) (pc : Fin p) (op : TeamMemoryCallback.Op r) (q : TeamMemoryCallback.Label k op)
  | burst (sign : Option Bool) (routine : Fin a) (addr len : Fin r) (pc : Fin p) (q : TeamBurstCallback.State addr len)
  | privateCall (sign : Option Bool) (routine : Fin a) (pc : Fin p) (q : TeamPrivateCompiler.Control Q m g)
  | reset (sign : Option Bool) (pc : Fin p) (q : (SliceArithmetic.CallClear.clear
      (Port.clock .stamp : Port r k (m*g))).State)
  | close (sign : Option Bool) (live : Option (Fin p))
  | reject

noncomputable instance (P : TeamOpcode.Program p r k a) [Fintype Q] : Fintype (Label P Q m g) := derive_fintype% _

private abbrev clearStamp := SliceArithmetic.CallClear.clear (Port.clock .stamp : Port r k (m*g))

/-- Resume the next instruction after clearing the temporary first-probe timestamp. -/
def resume {P : TeamOpcode.Program p r k a} (sign : Option Bool) (pc : Fin p) : Label P Q m g :=
  .reset sign pc clearStamp.body.entry

private def callback {P : TeamOpcode.Program p r k a} (sg : Option Bool) :
    TeamOpcode.Exit p r a → StackOp (Port r k (m*g)) (Label P Q m g)
  | .sign b next => .goto (resume (times sg (some b)) next)
  | .call j addr len next => .goto (.burst sg j addr len next (TeamBurstCallback.start addr len))
  | .native (.next pc) => .goto (resume sg pc)
  | .native (.choose yes no) => .choose (resume sg no) (resume sg yes)
  | .native (.read dst addr pc) => .goto (.memory sg pc (.load dst addr) (TeamMemoryCallback.entry _))
  | .native (.write addr src pc) => .goto (.memory sg pc (.store addr src) (TeamMemoryCallback.entry _))
  | .native .accept => .goto (.close sg none)
  | .native .reject | .native (.returnState _) => .goto .reject

/-- One fixed finite signed validator for arbitrary admitted opcodes and native private
subroutines. Its internal clock and memory instructions operate on the same named stacks. -/
noncomputable def code (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) :
    StackCode (Port r k (m*g)) (Label P Q m g)
  | .clock sg (.exit out) => match out with
    | .accepted => .goto (.close sg none)
    | .handoff pc => .goto (.close sg (some pc))
    | .reject => .goto .reject
    | .callback out => callback sg out
  | .clock sg q => (TeamLocalClock.Loop.rows P q).rename Port.clock (.clock sg)
  | .memory sg pc _ .done => .goto (resume sg pc)
  | .memory sg pc op q => (TeamMemoryCallback.code op q).rename TeamSite.memory (.memory sg pc op)
  | .burst sg j addr len pc q => TeamBurstCallback.rows addr len burstPort (.burst sg j addr len pc)
      (.privateCall sg j pc (.load .start)) q
  | .privateCall sg _ pc (.result out) => .goto (resume (times sg out) pc)
  | .privateCall sg j pc q => ((lib j).rows q).rename id (.privateCall sg j pc)
  | .reset sg pc q => (clearStamp.body.code q).rename id (fun next => next.elim (.clock sg (.enter pc)) (.reset sg pc))
  | .close sg _ => .halt sg.isSome
  | .reject => .halt false

/-- The terminal sign accompanies the real close label, including when the block hands
a live PC to a successor. -/
def negative {P : TeamOpcode.Program p r k a} : Label P Q m g → Bool
  | .close (some true) _ => true
  | _ => false

/-- The outer loop performs the complete guarded opcode preparation before consuming
any branch bit or modifying any record. -/
theorem clock_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (sg : Option Bool)
    (pub : Fin k → Word w) (s : TeamOpcode.State w p r) (block left elapsed max : Word w)
    (safe : elapsed.val+left.val < 2^w) (base : Stacks (Port r k (m*g)))
    (hc : base ∘ Port.clock = TeamLocalClock.bank pub s block left elapsed max) (bits : List Bool) :
    let x := TeamLocalClock.Loop.result P pub s block left elapsed max
    ∃ n ≤ 1050*(w+1)^2, StackRuns (replay (code P lib)) n (.clock sg (.enter s.pc),bits) base
      (.clock sg (.exit x.1),bits) (installStacks Port.clock base x.2) := by
  intro x
  obtain ⟨n,hn,run⟩ := TeamLocalClock.Loop.step P pub s block left elapsed max safe
  have lift := run.lift Port.clock (fun _ _ he => Port.clock.inj he) (Label.clock sg) base
    (target := code P lib) (by intro q h; cases q <;> first | rfl | simp [TeamLocalClock.Loop.rows] at h)
  have he := installStacks_eq (fun _ _ he => Port.clock.inj he) base
    (TeamLocalClock.bank pub s block left elapsed max) (congrFun hc)
  exact ⟨n,hn,by simpa only [he] using replay_segment lift bits⟩

/-- Every successful callback clears its timestamp in exactly one stack pop per
remaining bit plus the final empty pop. The continuation receives all suffix choices. -/
theorem reset_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (pc : Fin p) (s : Stacks (Port r k (m*g))) (bits : List Bool) :
    StackRuns (replay (code P lib)) ((s (.clock .stamp)).length+1) (resume sg pc,bits) s
      (.clock sg (.enter pc),bits) (Function.update s (.clock .stamp) []) :=
  replay_segment (TeamLink.routine_id (SliceArithmetic.CallClear.clear_runs _ s) (code P lib)
    (.reset sg pc) (.clock sg (.enter pc)) (fun _ => rfl)) bits

/-- Each binary RAM branch is realized by one literal binary row with the source's
false/true ordering, even when both branch PCs coincide. -/
theorem choose_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (yes no : Fin p) (b : Bool) (rest : List Bool) (s : Stacks (Port r k (m*g))) :
    StackRuns (replay (code P lib)) 1 (.clock sg (.exit (.callback (.native (.choose yes no)))),b::rest) s
      (resume sg (if b then yes else no),rest) s := by
  cases b <;> exact .cons (.goto rfl) (.nil ..)

end TeamSite.Loop

end BorderVNP
end Computability
end OAI
