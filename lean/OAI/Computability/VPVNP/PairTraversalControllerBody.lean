import OAI.Computability.VPVNP.PairTraversalControllerFormula

/-!
# Replaying the existing descriptor workers inside the traversal controller

The controller reads each parameter bank from live memory. When these words
match the completed level directory, each embedded body has the exact report
of its standalone reset-entry worker. In particular the controller adds no
write to those of the actual descriptor or role pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM TraversalRows
open scoped Fin.CommRing

variable {w : ℕ}

/-- One traversal pass over a specified number of sites. A tag pass writes roles, a leaf pass
writes empty child headers, and a fiber pass translates child identifiers using its
capacity bound. -/
inductive Pass (w : ℕ) where
  | tag (params : Fin 4 → Word w) (count : ℕ)
  | leaf (params : Fin 2 → Word w) (count : ℕ)
  | fiber (params : Fin 6 → Word w) (cap count : ℕ)

/-- Number of site-worker bursts scheduled for this pass. -/
def Pass.count : Pass w → ℕ
  | .tag _ n | .leaf _ n | .fiber _ _ n => n

/-- Fuel per reference burst, fixed at 12 for tagging, 14 for leaf headers and `7 * cap + 25`
for fiber rows. -/
def Pass.clock : Pass w → ℕ
  | .tag .. => 12
  | .leaf .. => 14
  | .fiber _ c _ => 7 * c + 25

/-- Instantiate the standalone tag, leaf or fiber worker with this pass's parameter words and
package its RAM program with its configuration type. -/
def Pass.spec : Pass w → Σ C : Type, BurstRAM.Program w C
  | .tag p _ => ⟨_, ((template TraversalRoles.Native.visit 0).instantiate w p).program⟩
  | .leaf p _ => ⟨_, ((LeafWorker.program.template (some 0)).instantiate w p).program⟩
  | .fiber p _ _ => ⟨_, ((SiteWorker.program.template (some 6)).instantiate w p).program⟩

/-- A single reference burst started at site word `i` in memory `m` finishes within the pass
clock on an empty choice tape and returns `rep`. -/
def Pass.At (P : Pass w) (i : Word w) (m : Memory w) (rep : Report w) : Prop :=
  execute P.spec.2 P.clock (P.spec.2.start i) m [] = some rep

/-- Starting at site zero in `m`, the reference program produces the given reports across the
pass's scheduled bursts, each with its own empty choice tape. -/
def Pass.Run (P : Pass w) (m : Memory w) (rs : List (Report w)) : Prop :=
  runSegment P.spec.2 P.clock (some 0) m (List.replicate P.count []) = some rs

open private ops from OAI.Computability.VPVNP.PairTraversalLeafWorker
open private finishOps from OAI.Computability.VPVNP.PairTraversalSiteWorker

private theorem leaf_return {pub : Fin 2 → Word w} {site : Word w} {m m' : Memory w}
    {rs out : Regs w 4} {es : List (Event w)}
    (run : Flow.Exec pub site LeafWorker.program rs m es out m') :
    out 0 = site + 1 := by
  have h := (PrimedCounter.Admin.exec_lines_iff_trace _).mp run
  have e := congrArg (Option.map (fun v : List (Event w) × Regs w 4 × Memory w => v.2.1 0)) h
  simpa (config := { decide := true }) [ops, trace, Op.effect, BinaryOp.eval, Function.update]
    using e.symm

private theorem fiber_return {pub : Fin 6 → Word w} {site : Word w} {m m' : Memory w}
    {rs out : Regs w 7} {es : List (Event w)}
    (run : Flow.Exec pub site SiteWorker.program rs m es out m') :
    out 6 = site + 1 := by
  cases run with
  | seq _ tail =>
    cases tail with
    | seq _ final =>
      have h := (PrimedCounter.Admin.exec_lines_iff_trace _).mp final
      have e := congrArg (Option.map (fun v : List (Event w) × Regs w 7 × Memory w => v.2.1 6)) h
      simpa (config := { decide := true }) [finishOps, trace, Op.effect, BinaryOp.eval,
        Function.update] using e.symm

/-- A successful standalone reference burst always returns the successor site. -/
theorem Pass.next {P : Pass w} {site : Word w} {m : Memory w} {rep : Report w}
    (h : P.At site m rep) : rep.result = some (site + 1) := by
  cases P with
  | tag pub _ =>
    have e := Option.some.inj (h.symm.trans (TraversalRoles.Native.visit_native pub site m))
    exact congrArg Report.result e
  | leaf pub _ =>
    obtain ⟨out, _, run, hr, _, _⟩ := (Flow.template_execute_iff LeafWorker.program (some 0)
      pub site (fun _ => 0) (fun _ => 0) m _ [] rep).mp h
    exact hr.trans (congrArg some (leaf_return run))
  | fiber pub _ _ =>
    obtain ⟨out, _, run, hr, _, _⟩ := (Flow.template_execute_iff SiteWorker.program (some 6)
      pub site (fun _ => 0) (fun _ => 0) m _ [] rep).mp h
    exact hr.trans (congrArg some (fiber_return run))

open private replay_exec from OAI.Computability.VPVNP.PairTraversalRowExecution

/-- The three parameter banks are computed by the same fixed expression setup. -/
def Pass.Bank (rs : Regs w R) : Pass w → Prop
  | .tag pub _ => rs ∘ roleAlloc.words (by decide) = pub
  | .leaf pub _ => rs ∘ leafAlloc.words (by decide) = pub
  | .fiber pub _ _ => rs ∘ fiberAlloc.bank = pub

/-- Select the embedded role, leaf-header or fiber-row instruction flow that replays the
standalone worker inside the traversal controller. -/
def Pass.body : Pass w → Flow R 11
  | .tag .. => roleAlloc.role
  | .leaf .. => leafAlloc.leaf
  | .fiber .. => fiberAlloc.fiber

/-- Lift an actual standalone report, including its writes, into the common
word-width-independent controller. Every operand and output register outside
the seven worker temporaries is preserved. -/
theorem Pass.lift {P : Pass w} {i : Word w} {m : Memory w} {rep : Report w}
    (h : P.At i m rep) (pub : Fin 11 → Word w) (state : Word w) (rs : Regs w R)
    (hp : P.Bank rs) (hi : rs (value 0) = i) (zero : ∀ j, rs (scratchRegs j) = 0) :
    ∃ out, Flow.Exec pub state P.body rs m rep.events out (after m rep.events) ∧
      choiceBits rep.events = [] ∧ rep.events.length < P.clock ∧
      ∀ j, j ∉ Set.range scratchRegs → out j = rs j := by
  cases P with
  | tag p n =>
    have e := Option.some.inj (h.symm.trans (TraversalRoles.Native.visit_native p i m))
    obtain ⟨out, run, _, _, len, bits, frame⟩ := roleAlloc.role_exec pub state i rs m p hp hi
    cases e
    exact ⟨out, run, bits, by change _ < 12; rw [len]; decide, frame⟩
  | leaf p n =>
    obtain ⟨out, m', run, _, len, bits⟩ := (Flow.template_execute_iff LeafWorker.program (some 0)
      p i (fun _ => 0) (fun _ => 0) m _ [] rep).mp h
    have small : rs ∘ leafAlloc.regs (by decide : 4 ≤ 7) = fun _ => 0 := funext fun _ => zero _
    have no (j) : leafAlloc.words (by decide : 2 ≤ 6) j ∉
        Set.range (leafAlloc.regs (by decide : 4 ≤ 7)) :=
      fun ⟨b, eb⟩ => leafAlloc.bankOutside _ ⟨_, eb⟩
    have arg : leafAlloc.site ∉ Set.range (leafAlloc.regs (by decide : 4 ≤ 7)) :=
      fun ⟨b, eb⟩ => leafAlloc.siteOutside ⟨_, eb⟩
    obtain ⟨rs', body, _, frame⟩ := OnlineWorker.liftExec _ _ _ no arg pub run rs small hp hi
      (state := state)
    refine ⟨rs', (replay_exec run).symm ▸ body, bits, len, fun j hj => frame j ?_⟩
    exact fun ⟨b, eb⟩ => hj ⟨_, eb⟩
  | fiber p cap n =>
    obtain ⟨out, m', run, _, len, bits⟩ := (Flow.template_execute_iff SiteWorker.program (some 6)
      p i (fun _ => 0) (fun _ => 0) m _ [] rep).mp h
    have small : rs ∘ fiberAlloc.scratch = fun _ => 0 := funext zero
    obtain ⟨rs', body, _, frame⟩ := OnlineWorker.liftExec _ _ _ fiberAlloc.bankOutside
      fiberAlloc.siteOutside pub run rs small hp hi (state := state)
    exact ⟨rs', (replay_exec run).symm ▸ body, bits, len, frame⟩

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
