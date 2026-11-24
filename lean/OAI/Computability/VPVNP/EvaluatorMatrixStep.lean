import OAI.Computability.VPVNP.EvaluatorIndexChoice
import OAI.Computability.VPVNP.Evaluator
import OAI.Computability.VPVNP.StructuredStackCount

/-!
# Streaming one matrix-index path of the finite algebra evaluator

A linear step chooses its next basis index once, reads that single matrix
entry, and multiplies the running weight. The routines before and after the
choice are deterministic. The count formula allows their costs to depend on
the index and passes the exact remaining fuel to the next matrix step.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator

open RAMTape

variable {K P Q : Type*} [DecidableEq K] (bound dest : K)
    (prepare : Routine K P) (advance : Routine K Q)

/-- The first routine prepares the basis dimension. After the binary choice,
the second routine queries the chosen entry and updates both the current index
and the field product, keeping only the data for the next step. -/
def matrixStep : Routine K ((P ⊕ IndexChoice.Phase) ⊕ Q) :=
  (prepare.followedBy (IndexChoice.guessBelow bound dest)).followedBy advance

/-- Count a machine step, with arbitrary subsequent computation. The per-index
postprocessing times need only admit a common bound. -/
theorem matrixStep_count {w : ℕ} (hne : bound ≠ dest) (n : BurstRAM.Word w)
    {s ready : Stacks K} {prepTime : ℕ} (hp : prepare.Runs prepTime s ready)
    (hb : ready bound = BurstRAM.wordBits n) (next : Fin n.val → Stacks K)
    (ticks : Fin n.val → ℕ) (ha : ∀ i, advance.Runs (ticks i)
      (IndexChoice.written bound dest ready (BurstRAM.wordBits (Fin.castLE n.isLt.le i))) (next i))
    (c : ℕ → Stacks K → ℕ) (fuel : ℕ) (ht : ∀ i, ticks i ≤ fuel) :
    (matrixStep bound dest prepare advance).count c (fuel + (3*w + 2) + prepTime) s =
      ∑ i, c (fuel - ticks i) (next i) := by
  rw [matrixStep, Routine.count_followedBy, Routine.count_followedBy, hp.count_eq,
    IndexChoice.count_guessBelow_fin bound dest hne n ready hb]
  apply Finset.sum_congr rfl
  intro i _
  have h := (ha i).count_eq c (fuel - ticks i)
  rwa [Nat.sub_add_cancel (ht i)] at h

/-- A common step budget allows every branch to be charged its own actual
query time. The delays are independent of the choice of continuation. -/
theorem matrixStep_count_of_bound {w : ℕ} (hne : bound ≠ dest) (n : BurstRAM.Word w)
    {s ready : Stacks K} {prepTime : ℕ} (hp : prepare.Runs prepTime s ready)
    (hb : ready bound = BurstRAM.wordBits n) (next : Fin n.val → Stacks K)
    {stepBound : ℕ} (ha : ∀ i, ∃ t, prepTime + (3*w + 2) + t ≤ stepBound ∧
      advance.Runs t (IndexChoice.written bound dest ready
        (BurstRAM.wordBits (Fin.castLE n.isLt.le i))) (next i))
    (hprep : prepTime + (3*w + 2) ≤ stepBound) (fuel : ℕ) (hfuel : stepBound ≤ fuel) :
    ∃ delay : Fin n.val → ℕ, (∀ i, delay i ≤ stepBound) ∧ ∀ c,
      (matrixStep bound dest prepare advance).count c fuel s =
        ∑ i, c (fuel - delay i) (next i) := by
  choose ticks htime hrun using ha
  let first := prepTime + (3*w + 2)
  refine ⟨fun i ↦ first + ticks i, htime, fun c ↦ ?_⟩
  have hn : fuel - first + (3*w+2) + prepTime = fuel := by dsimp [first]; omega
  have hh := matrixStep_count bound dest prepare advance hne n hp hb next ticks hrun c (fuel - first)
    (fun i ↦ by have := htime i; dsimp [first]; omega)
  simpa only [hn, Nat.sub_sub] using hh

/-- Convert the running field product to its prime-field residue. A failed
endpoint test sets the bound to zero. A successful endpoint test uses the
residue word as the bound and each legal choice accepts immediately. -/
def residueBranches (finalize : Routine K P) : Routine K ((P ⊕ IndexChoice.Phase) ⊕ Unit) :=
  (finalize.followedBy (IndexChoice.guessBelow bound dest)).followedBy (Routine.halt true)

/-- For the terminating routine the ordinary integer leaf count equals the
encoded residue, at every clock that covers its two routines and final halt. -/
theorem residueBranches_count (finalize : Routine K P) {w : ℕ} (hne : bound ≠ dest)
    (n : BurstRAM.Word w) {s ready : Stacks K} {t : ℕ} (hp : finalize.Runs t s ready)
    (hb : ready bound = BurstRAM.wordBits n) (c : ℕ → Stacks K → ℕ) (fuel : ℕ) :
    (residueBranches bound dest finalize).count c (fuel+1 + (3*w+2) + t) s = n.val := by
  rw [residueBranches, Routine.count_followedBy, Routine.count_followedBy, hp.count_eq,
    IndexChoice.count_guessBelow_fin bound dest hne n ready hb]
  simp [Routine.count, Routine.countFrom, Routine.halt]

end Evaluator

end VPVNP
end Computability
end OAI
