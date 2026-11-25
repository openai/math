import OAI.Computability.BorderVNP.DiagonalResidueRAMAdvice
import OAI.Computability.BorderVNP.RoutingISARuns

/-!
# Executing one row of the residue interpreter

Symbolic execution of straight-line assembly computes the exact register bank,
memory, and chronological probe trace. It uses the native `Runs` relation,
including the identity of a binary guess and the old word observed by a store.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA

/-- Result of one straight-line assembly fragment on a specified branch. -/
structure Effect (w : ℕ) where
  /-- Register bank at the next program counter. -/
  bank : Bank w
  /-- Shared memory at the next program counter. -/
  mem : Memory w
  /-- Ordinary and choice instructions in chronological order. -/
  trace : List (TeamRAM.Event w)

/-- Instructions used inside the three finite straight-line fragments. -/
def straight : Code → Bool
  | .constant .. | .copy .. | .load .. | .store .. | .nop => true
  | .binary op .. => !(op == .div || op == .mod)
  | .seq a b | .choose a b => straight a && straight b
  | _ => false

/-- Symbolic native execution of straight-line code, at a specified Boolean
branch. For a compound containing multiple guesses it chooses this bit at
each of them. The interpreter uses this only for fragments with at most one. -/
def effect {w : ℕ} (b : Bool) (s : Bank w) (m : Memory w) : Code → Effect w
  | .nop => ⟨s, m, [tick w]⟩
  | .constant d v => ⟨Function.update s d (Fin.ofNat _ v.val), m, [tick w]⟩
  | .copy d x => ⟨Function.update s d (s x), m, [tick w]⟩
  | .binary op d x y => ⟨Function.update s d (op.eval (s x) (s y)), m, [tick w]⟩
  | .load d a => ⟨Function.update s d (m (s a).val), m,
    [⟨.ordinary (some ((s a).val, none)), [m (s a).val], [], .plus⟩]⟩
  | .store a x => ⟨s, Function.update m (s a).val (s x),
    [⟨.ordinary (some ((s a).val, some (s x))), [m (s a).val], [], .plus⟩]⟩
  | .seq a c =>
    let e := effect b s m a
    let f := effect b e.bank e.mem c
    { f with trace := e.trace ++ f.trace }
  | .choose a c =>
    let e := if b then effect b s m a else effect b s m c
    { e with trace := choiceTick w b :: e.trace }
  | _ => ⟨s,m,[]⟩

/-- Every supported symbolic execution is an execution of the actual
structured ISA, with exactly the same events and final registers. -/
theorem effect_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (b : Bool) (s : Bank w) (m : Memory w) (c : Code) (hc : straight c = true) :
    let e := effect b s m c
    Runs pub macros c s m e.trace e.bank e.mem := by
  induction c generalizing s m with
  | nop | constant | copy => exact Runs.localStep _ rfl rfl
  | binary op d x y =>
    exact Runs.localStep _ rfl (by
      cases op <;> simp [straight] at hc <;> rfl)
  | load d a => exact Runs.load _ _ d a _ _
  | store a x => exact Runs.store _ _ a x _ _
  | seq a c iha ihc =>
    have hh : straight a = true ∧ straight c = true := by simpa [straight] using hc
    exact .seq (iha _ _ hh.1) (ihc _ _ hh.2)
  | choose a c iha ihc =>
    have hh : straight a = true ∧ straight c = true := by simpa [straight] using hc
    cases b with
    | false => exact .choose false (ihc _ _ hh.2)
    | true => exact .choose true (iha _ _ hh.1)
  | _ => contradiction

/-- Correctness of straight-line setup for the residue reader. -/
theorem setup_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :
    let e := effect false s m setup
    Runs pub macros setup s m e.trace e.bank e.mem :=
  effect_runs pub macros false s m setup (by decide)

/-- Correctness of the nondeterministic single-bit store. -/
theorem guessBody_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (b : Bool) (s : Bank w) (m : Memory w) :
    let e := effect b s m guessBody
    Runs pub macros guessBody s m e.trace e.bank e.mem :=
  effect_runs pub macros b s m guessBody (by decide)

/-- Correctness of the two indirect loads, two word operations and gate store. -/
theorem gateBody_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :
    let e := effect false s m gateBody
    Runs pub macros gateBody s m e.trace e.bank e.mem :=
  effect_runs pub macros false s m gateBody (by decide)

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
