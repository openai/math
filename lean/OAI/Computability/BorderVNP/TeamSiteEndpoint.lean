import OAI.Computability.BorderVNP.TeamSiteLoop
import OAI.Computability.BorderVNP.TeamLocalClockFinish
import OAI.Computability.BorderVNP.TeamLocalClockStartup

/-!
# Starting and finishing a physical processor block

The incident predecessor and successor frames occupy separate bit streams.
Startup, the signed RAM instruction loop and finish share one register bank
and one cumulative clock. A propagated halt bypasses the instruction loop,
whereas a live frame starts the loop with sign +1. Each processor returns
its own sign after checking its successor frame or the final halt.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Endpoint

open VPVNP RAMTape BurstRAM TeamLocalClock TeamPrivateFragment

variable {w p r k a d m g : ℕ} {Q Γ : Type}

/-- Shared physical stacks for a processor's incident frame and signed instruction loop. -/
inductive Port (r k d : ℕ) where
  | site (u : TeamSite.Port r k d)
  | incoming | outgoing | width | tag | pc | tmp | payload
  deriving DecidableEq, Fintype

/-- Startup consumes the incoming frame and fills the live loop's own registers. -/
def startup : Startup.Port r k → Port r k d
  | .clock u => .site (.clock u)
  | .wire => .incoming
  | .width => .width
  | .tmp => .tmp
  | .tag => .tag
  | .pc => .pc

/-- Finish reads the same physical register bank and consumes the candidate successor bits. -/
def finish : Finish.Port r k → Port r k d
  | .clock u => .site (.clock u)
  | .candidate => .outgoing
  | .tmp => .tmp
  | .payload => .payload

theorem startup_injective : Function.Injective (@startup r k d) := by
  intro i j h; cases i <;> cases j <;> simp_all [startup]

theorem finish_injective : Function.Injective (@finish r k d) := by
  intro i j h; cases i <;> cases j <;> simp_all [finish]

/-- Finite controller from public or predecessor startup to the signed block result. -/
inductive Label (P : TeamOpcode.Program p r k a) (Q : Type) (m g : ℕ) where
  | startup (last : Bool) (q : Startup.State p r)
  | loop (last : Bool) (q : TeamSite.Loop.Label P Q m g)
  | finish (sign : Option Bool) (q : Finish.Label p r k)
  | done (sign : Option Bool)
  | invalid

noncomputable instance (P : TeamOpcode.Program p r k a) [Fintype Q] : Fintype (Label P Q m g) :=
  derive_fintype% _

/-- Transition from a checked startup. Local signs begin positive at each processor. -/
def afterStartup {P : TeamOpcode.Program p r k a} (last : Bool) :
    TeamLocalClockPC.Outcome p → Label P Q m g
  | .live pc => .loop last (.clock (some false) (.enter pc))
  | .accepted => .finish (some false) (.enter .accepted last)
  | .reject => .invalid

/-- The program counter lives in finite control; halt serializes canonical zero instruction fields. -/
def closeMode : Option (Fin p) → Finish.Mode p
  | none => .accepted
  | some pc => .live pc

/-- A successful zero-weight private path has a verified frame and a distinct terminal
from a malformed incident frame. The enclosing processor sends every successful
path to its record-buffer and sorting checks. -/
def finishLabel {P : TeamOpcode.Program p r k a} (sign : Option Bool) (ok : Bool) :
    Label P Q m g := if ok then .done sign else .invalid

/-- The processor's finite signed stack machine. The controls before and after the
instruction loop never introduce path choices or multiply the path weight. -/
noncomputable def code (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) :
    StackCode (Port r k (m*g)) (Label P Q m g)
  | .startup last (.done out) => .goto (afterStartup last out)
  | .startup last q => (Startup.code p r k q).rename startup (.startup last)
  | .loop last (.close sg live) => .goto (.finish sg (.enter (closeMode live) last))
  | .loop _ .reject => .goto .invalid
  | .loop last q => (TeamSite.Loop.code P lib q).rename Port.site (.loop last)
  | .finish sg (.done ok) => .goto (finishLabel sg ok)
  | .finish sg q => (Finish.rows q).rename finish (.finish sg)
  | .done sg => .halt sg.isSome
  | .invalid => .halt false

/-- The sign of an accepted endpoint execution. Rejection and absorbed zero halt with value zero. -/
def negative {P : TeamOpcode.Program p r k a} : Label P Q m g → Bool
  | .done (some true) => true
  | _ => false

/-- The signed value visible to a caller, including rejected frames and verified private zero. -/
def weight {P : TeamOpcode.Program p r k a} : Label P Q m g → ℤ
  | .done sign => (TeamPrivateCall.sign sign).value
  | _ => 0

/-- Failed validation has zero signed contribution; successful validation exposes the
unchanged local contribution and permits downstream sorting even when it is zero. -/
theorem weight_finishLabel {P : TeamOpcode.Program p r k a} (sg : Option Bool) (ok : Bool) :
    weight (finishLabel (P := P) (Q := Q) (m := m) (g := g) sg ok) =
      if ok then (TeamPrivateCall.sign sg).value else 0 := by cases ok <;> rfl

/-- Startup uses no choice bits and passes the complete suffix to the signed loop,
the propagated halt, or the rejecting exit. -/
theorem startup_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (last : Bool) {t q s result out} (hr : StackRuns (Startup.code p r k) t q s (.done result) out)
    (base : Stacks (Port r k (m*g))) (ready : base ∘ startup = s) (bits : List Bool) :
    StackRuns (replay (code P lib)) (t+1) (.startup last q,bits) base
      (afterStartup last result,bits) (installStacks startup base out) := by
  have h := hr.lift startup startup_injective (Label.startup last) base (target := code P lib) (by
    intro q h; cases q with
    | done res => cases res <;> contradiction
    | _ => rfl)
  rw [installStacks_eq startup_injective base s (congrFun ready)] at h
  have lastStep : StackRuns (code P lib) 1 (.startup last (.done result)) (installStacks startup base out)
      (afterStartup last result) (installStacks startup base out) := .cons (.goto rfl) (.nil ..)
  exact replay_segment (h.trans lastStep) bits

/-- Install any finite signed-loop replay segment onto the shared physical site ports.
Every branch bit consumed by the installed segment is one consumed by the inner loop. -/
theorem loop_segment (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (last : Bool) {t q bits s q' rest out}
    (hr : StackRuns (replay (TeamSite.Loop.code P lib)) t (q,bits) s (q',rest) out)
    (base : Stacks (Port r k (m*g))) (ready : base ∘ Port.site = s) :
    StackRuns (replay (code P lib)) t (.loop last q,bits) base (.loop last q',rest)
      (installStacks Port.site base out) := by
  have h := TeamLink.replay_lift hr (code P lib) Port.site (fun _ _ he => Port.site.inj he)
    (Label.loop last) base (by intro q h; cases q <;> first | rfl | simp [TeamSite.Loop.code] at h)
  rw [installStacks_eq (fun _ _ he => Port.site.inj he) base s (congrFun ready)] at h
  exact h

/-- Exact prefix of path choices consumed by the inner loop, including arbitrary private branches.
The frame checker receives the same local sign and live program counter as that loop. -/
theorem loop_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (last : Bool) {t q bits s sg live rest out}
    (hr : StackRuns (replay (TeamSite.Loop.code P lib)) t (q,bits) s (.close sg live,rest) out)
    (base : Stacks (Port r k (m*g))) (ready : base ∘ Port.site = s) :
    StackRuns (replay (code P lib)) (t+1) (.loop last q,bits) base
      (.finish sg (.enter (closeMode live) last),rest) (installStacks Port.site base out) := by
  have h := loop_segment P lib last hr base ready
  have go : StackRuns (code P lib) 1 (.loop last (.close sg live)) (installStacks Port.site base out)
      (.finish sg (.enter (closeMode live) last)) (installStacks Port.site base out) := .cons (.goto rfl) (.nil ..)
  exact h.trans (replay_segment go rest)

/-- A rejecting instruction loop stops with weight zero before validating a successor frame. -/
theorem loop_reject (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (last : Bool)
    (s : Stacks (Port r k (m*g))) (bits : List Bool) :
    StackRuns (replay (code P lib)) 1 (.loop last .reject,bits) s (.invalid,bits) s :=
  replay_segment (C := code P lib) (.cons (.goto rfl) (.nil ..)) bits

/-- Finality or physical outgoing-frame comparison returns the accumulated local sign exactly
on success, with no consumption of choice bits. -/
theorem finish_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) {t q s ok out} (hr : StackRuns (Finish.rows (p := p)) t q s (.done ok) out)
    (base : Stacks (Port r k (m*g))) (ready : base ∘ finish = s) (bits : List Bool) :
    StackRuns (replay (code P lib)) (t+1) (.finish sg q,bits) base
      (finishLabel sg ok,bits) (installStacks finish base out) := by
  have h := hr.lift finish finish_injective (Label.finish sg) base (target := code P lib) (by
    intro q h; cases q <;> first | rfl | contradiction)
  rw [installStacks_eq finish_injective base s (congrFun ready)] at h
  have go : StackRuns (code P lib) 1 (.finish sg (.done ok)) (installStacks finish base out)
      (finishLabel sg ok) (installStacks finish base out) := .cons (.goto rfl) (.nil ..)
  exact replay_segment (h.trans go) bits

end TeamSite.Endpoint

end BorderVNP
end Computability
end OAI
