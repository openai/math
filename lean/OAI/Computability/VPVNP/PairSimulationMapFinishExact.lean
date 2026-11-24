import OAI.Computability.VPVNP.PairSimulationMapFinish

/-!
# Exact native time for the successful width check and label histogram

Each matching width consumes one guard instruction, and a final guard transfers
control to the histogram scan. That scan increments one private counter for each
emitted label, including repetitions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapWidths

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM

variable {E : Type*} {w p r k : ℕ}

/-- A successful guard sequence reads every tested pair and reaches the final guard. -/
theorem checkSteps_of_all (eq : E → Bool) (es : List E) (all : ∀ e ∈ es, eq e = true) :
    checkSteps eq es = es.length + 1 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [checkSteps, ite_eq_left (all e List.mem_cons_self), List.length_cons,
      ih (fun i hi => all i (List.mem_cons_of_mem e hi))]
    omega

/-- The complete successful guard chain leaves the counter operands intact. -/
theorem checkCode_success (lhs rhs : E → Fin r) (scratch : Fin r) (es : List E)
    (M : Machine w p r k) (label : (checkCode lhs rhs scratch es : Flow r k).Label → Fin p)
    (stop bad : Fin p) (link : Flow.Linked M (checkCode lhs rhs scratch es) label stop bad)
    (c : Config w p r) (hc : c.pc = label (checkCode lhs rhs scratch es : Flow r k).entry)
    (valid : ∀ e ∈ es, c.reg (lhs e) = c.reg (rhs e)) :
    Prefix M c (List.replicate (es.length + 1) .tick) {c with pc := stop} := by
  let same := fun e ↦ decide (c.reg (lhs e) = c.reg (rhs e))
  have all (e : E) (he : e ∈ es) : same e = true := decide_eq_true (valid e he)
  have pre := checkCode_native lhs rhs scratch es M label stop bad link c hc
  change Prefix M c (List.replicate (checkSteps same es) .tick)
    {c with pc := if es.all same then stop else bad} at pre
  rwa [checkSteps_of_all same es all, ite_eq_left (List.all_eq_true.mpr all)] at pre

end PairSimulation.MapWidths

namespace PairSimulation.MapFinish

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM MotifSelector
open scoped Fin.CommRing

variable {E Q : Type*} {w p r k t u : ℕ}

/-- Matching payload widths give the exact successful path, including the empty
width vector and an empty sequence of emitted labels. -/
theorem native_success (width : Q → E → ℕ) (θ : Fin u → Q) (v : E → ℕ) (es : List E)
    (lhs rhs : E → Fin r) (tmp : Fin r) (M : Machine w p r k)
    (guardPC : (MapWidths.checkCode lhs rhs tmp es : Flow r k).Label → Fin p)
    (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done bad : Fin p)
    (guards : Flow.Linked M (MapWidths.checkCode lhs rhs tmp es) guardPC (pc 0) bad)
    (counts : PrivateLabels.Linked M pc reg done) (src base : ℕ)
    (names : Fin u → Fin t) (c : Config w p r)
    (hc : c.pc = guardPC (MapWidths.checkCode lhs rhs tmp es : Flow r k).entry)
    (hx : ∀ e, (c.reg (lhs e)).val = totalWidth width θ e) (hy : ∀ e, (c.reg (rhs e)).val = v e)
    (ready : HistogramReady (u := u) reg src base c) (hfit : base + t ≤ 2 ^ w)
    (apart : src + u ≤ base ∨ base + t ≤ src) (endFit : src + u < 2 ^ w)
    (data : ∀ i : Fin u, c.privateMem ((src + i.val : ℕ) : BurstRAM.Word w) =
      ((names i).val : BurstRAM.Word w))
    (valid : ∀ e, v e = totalWidth width θ e) :
    ∃ out, Prefix M c (List.replicate ((es.length + 1) + (7 * u + 1)) .tick) out ∧
      out.pc = done ∧
      out.privateMem = PrivateLabels.accumulate base (List.ofFn names) c.privateMem ∧
      out.persistent = c.persistent := by
  let mid := {c with pc := pc 0}
  have pre := MapWidths.checkCode_success lhs rhs tmp es M guardPC (pc 0) bad guards c hc
    (fun e _ => Fin.ext ((hx e).trans ((valid e).symm.trans (hy e).symm)))
  let ns := List.ofFn names
  have hlen : ns.length = u := List.length_ofFn
  have stored (i : Fin ns.length) : mid.privateMem ((src + i.val : ℕ) : BurstRAM.Word w) =
      (ns[i.val].val : BurstRAM.Word w) := by
    simpa only [ns, List.getElem_ofFn] using data ⟨i.val, hlen ▸ i.isLt⟩
  obtain ⟨out, run, hpc, mem, per⟩ := PrivateLabels.run_separated counts ns src base mid rfl
    ready.cursor (hlen ▸ ready.stop) ready.base ready.one hfit (hlen ▸ apart) (hlen ▸ endFit) stored
  refine ⟨out, ?_, hpc, mem, per⟩
  rw [List.replicate_add, ← hlen]
  exact pre.append run

end PairSimulation.MapFinish

end VPVNP
end Computability
end OAI
