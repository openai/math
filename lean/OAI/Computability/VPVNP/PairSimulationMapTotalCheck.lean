import OAI.Computability.VPVNP.PairSimulationMapWidths
import OAI.Computability.VPVNP.PrimedInputRAMFlowLinks
import OAI.Computability.VPVNP.MotifPayload

/-!
# Checking the entire supply width vector in private RAM

The fixed motif has one running total and one descriptor width for each
supply edge, including edges at other parties. A fixed sequence of guards
compares their resident word registers and branches to rejection on the
first discrepancy.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapWidths

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM PrimedStackRAM

variable {E : Type*} {w p r k : ℕ}

/-- The constant final guard is also the empty-edge exit. -/
def checkCode (lhs rhs : E → Fin r) (scratch : Fin r) : List E → Flow r k
  | [] => .line (.guardEq scratch scratch)
  | e :: es => (Flow.line (.guardEq (lhs e) (rhs e))).seq (checkCode lhs rhs scratch es)

/-- Number of comparisons executed up to the first mismatch or the final guard. -/
def checkSteps (eq : E → Bool) : List E → ℕ
  | [] => 1
  | e :: es => if eq e then 1 + checkSteps eq es else 1

theorem checkSteps_le (eq : E → Bool) (es : List E) : checkSteps eq es ≤ es.length + 1 := by
  induction es with
  | nil => exact le_rfl
  | cons e es ih =>
    cases h : eq e <;> simp [checkSteps, h]
    omega

/-- The fixed guards consume no guesses, perform no probes and preserve
all registers, private memory and the persistent word on both exits. -/
theorem checkCode_native (lhs rhs : E → Fin r) (scratch : Fin r) (es : List E)
    (M : Machine w p r k) (label : (checkCode lhs rhs scratch es : Flow r k).Label → Fin p)
    (stop bad : Fin p) (link : Flow.Linked M (checkCode lhs rhs scratch es) label stop bad)
    (c : Config w p r) (hpc : c.pc = label (checkCode lhs rhs scratch es : Flow r k).entry) :
    let same := fun e ↦ decide (c.reg (lhs e) = c.reg (rhs e))
    Prefix M c (List.replicate (checkSteps same es) .tick)
      {c with pc := if es.all same then stop else bad} := by
  dsimp only
  induction es generalizing c with
  | nil =>
    have hs : M.program.step c = .localStep {c with pc := stop} := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hpc, link.atLabel]
      change CallAction.localStep {c with pc := if c.reg scratch = c.reg scratch
        then stop else bad} = _
      simp
    exact .tick hs (.nil _)
  | cons e es ih =>
    let tail := checkCode lhs rhs scratch es (k := k)
    let enter := label (Sum.inr tail.entry)
    by_cases he : c.reg (lhs e) = c.reg (rhs e)
    · have hs : M.program.step c = .localStep {c with pc := enter} := by
        rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hpc, link.atLabel]
        change CallAction.localStep {c with pc := if c.reg (lhs e) = c.reg (rhs e)
          then enter else bad} = _
        simp [he]
      have rest := ih (label ∘ Sum.inr) link.seqRight {c with pc := enter} rfl
      simp only [checkSteps, he, decide_true, ↓reduceIte, List.all_cons, Bool.true_and]
      simpa only [Nat.add_comm 1, List.replicate_succ] using Prefix.tick hs rest
    · have hs : M.program.step c = .localStep {c with pc := bad} := by
        rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hpc, link.atLabel]
        change CallAction.localStep {c with pc := if c.reg (lhs e) = c.reg (rhs e)
          then enter else bad} = _
        simp [he]
      simpa only [checkSteps, he, decide_false, Bool.false_eq_true, ↓reduceIte, List.all_cons,
        Bool.false_and, List.replicate_one] using Prefix.tick hs (.nil _)

open scoped Classical in
/-- Compare the full totals produced by an actual inner selector list with the
descriptor widths, even for a malformed descriptor. All tested natural values
must fit the word; all other cells and registers can be arbitrary. -/
theorem totalCheck_native {Q : Type*} {u : ℕ} (width : Q → E → ℕ) (θ : Fin u → Q)
    (v : E → ℕ) (es : List E) (cover : ∀ e, e ∈ es)
    (lhs rhs : E → Fin r) (scratch : Fin r) (M : Machine w p r k)
    (label : (checkCode lhs rhs scratch es : Flow r k).Label → Fin p)
    (stop bad : Fin p) (link : Flow.Linked M (checkCode lhs rhs scratch es) label stop bad)
    (c : Config w p r) (hpc : c.pc = label (checkCode lhs rhs scratch es : Flow r k).entry)
    (hx : ∀ e, (c.reg (lhs e)).val = MotifSelector.totalWidth width θ e)
    (hy : ∀ e, (c.reg (rhs e)).val = v e) :
    ∃ steps ≤ es.length + 1, Prefix M c (List.replicate steps .tick)
      {c with pc := if ∀ e, v e = MotifSelector.totalWidth width θ e then stop else bad} := by
  classical
  let same := fun e ↦ decide (c.reg (lhs e) = c.reg (rhs e))
  have hsame : es.all same = true ↔ ∀ e, v e = MotifSelector.totalWidth width θ e := by
    simp only [List.all_eq_true, same, decide_eq_true_eq]
    constructor
    · intro h e
      exact (hy e).symm.trans ((congrArg Fin.val (h e (cover e))).symm.trans (hx e))
    · intro h e _
      exact Fin.ext ((hx e).trans ((h e).symm.trans (hy e).symm))
  refine ⟨checkSteps same es, checkSteps_le .., ?_⟩
  have run := checkCode_native lhs rhs scratch es M label stop bad link c hpc
  change Prefix M c (List.replicate (checkSteps same es) .tick)
    {c with pc := if es.all same then stop else bad} at run
  simpa only [hsame] using run

end PairSimulation.MapWidths

end VPVNP
end Computability
end OAI
