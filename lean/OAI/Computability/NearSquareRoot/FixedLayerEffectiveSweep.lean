import OAI.Computability.NearSquareRoot.FixedLayerSweep
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.ScheduleRegisterLookup

/-! # The literal chronological Fourier sweep for a supplied row command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code Space FixedCandidate ProductRecovery DigitPacking
open FixedPoint FixedLayerTickets ShortFourier.BatchWord GeneratorSyntax CommonRegisters
open EffectiveBoundedTask

def sweepCmd (row : Cmd) : Cmd :=
  splitRoot 0 (fun _ => .pass) ((move 0 1 2).join (.tie (Task.sweepBody row)))

theorem effective_sweepCmd {P : Type} [Primcodable P] {c : P → Cmd} (h : Effective ltr c) :
    Effective ltr (fun p => sweepCmd (c p)) := by
  apply KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
  apply (effective_const ltr (move 0 1 2)).join
  apply Effective.tie
  apply KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
  exact (effective_const ltr (move 1 0 2)).join ((effective_const ltr (pack 0)).join
    (h.join (effective_const ltr (.again 0))))

theorem within_sweepCmd {c : Cmd} {R : ℕ} (hR : 3 ≤ R) (h : Within R c) : Within R (sweepCmd c) := by
  unfold sweepCmd
  rw [RegisterWitness.splitRoot_within]
  refine ⟨by omega,trivial,trivial,?_,(RegisterLookup.sweepBody_within hR c).mpr h⟩
  simp [move,forward,forwardBody,flood,give,pack,Within]
  omega

noncomputable section

variable {I : Type} (n : I → ℕ) (hv : ∀ i, Directory (n i)) (dir : I → Bool)

set_option maxRecDepth 4500 in
set_option maxHeartbeats 2400000 in
/-- Recover the physical program used by the chronological sweep. Both callers
supply their particular checked commands, so the inferred sweep runs that very
row instruction at every ticket and uses the corresponding header prelude. -/
theorem namedProgramAt (area : I → ℕ) (fit : ∀ i, n i ≤ area i) (hn : ∀ i, 2 ≤ n i) (hk : ∀ i, 1 ≤ addressBits (n i))
    (F : ∀ i, Program (hv i))
    (len : ∀ i, steps (hv i) (F i) = (directedPlan (rowKey n dir i)).length)
    (ok : ∀ i, ForwardOK (hv i) (F i) ∨ InverseOK (hv i) (F i))
    (out : (i : I) → Fin (directedPlan (rowKey n dir i)).length →
      Array (n i) → Array (n i))
    (agree : ∀ i (j : Fin (directedPlan (rowKey n dir i)).length) u,
      nextArray (hv i) (F i) j.val u =
        out i ⟨(directedPlan (rowKey n dir i)).length-1-j.val, by omega⟩ u)
    (clock : ℕ → ℕ) (row pre : Cmd)
    (localRun : Runs row (fun e : RowInput n hv dir => clock (n e.instanceIndex))
      (fun e => area e.instanceIndex) (fun e => .fork (send (e.ticket n hv dir)) (framed e.payload))
      (fun e => framed (out e.instanceIndex e.position e.payload)))
    (prepare : Runs pre (fun e : Admitted n hv => n e.val.1) (fun e => n e.val.1)
      (fun e => framed e.val.2)
      (fun e => .fork (send (chronological (rowKey n dir e.val.1))) (framed e.val.2)))
    (K : ℕ) (vol : ∀ i, (send (chronological (rowKey n dir i))).count ≤ K*(n i+1)) :
    Runs (pre.join (sweepCmd row))
      (fun e : Admitted n hv => 3*boxDepth (addressBits (n e.val.1))*clock (n e.val.1)+n e.val.1)
      (fun e => area e.val.1) (fun e => framed e.val.2) (fun e => framed (eval (hv e.val.1) (F e.val.1) e.val.2)) :=
  command_contract (pre.join (sweepCmd row)) from runProgramAt n hv dir area fit hn hk F len ok out agree clock
    ⟨row,localRun⟩ ⟨pre,prepare⟩ K vol

/-- The named command specializes to linear workspace when every row does. -/
theorem namedProgram (hn : ∀ i, 2 ≤ n i) (hk : ∀ i, 1 ≤ addressBits (n i))
    (F : ∀ i, Program (hv i))
    (len : ∀ i, steps (hv i) (F i) = (directedPlan (rowKey n dir i)).length)
    (ok : ∀ i, ForwardOK (hv i) (F i) ∨ InverseOK (hv i) (F i))
    (out : (i : I) → Fin (directedPlan (rowKey n dir i)).length →
      Array (n i) → Array (n i))
    (agree : ∀ i (j : Fin (directedPlan (rowKey n dir i)).length) u,
      nextArray (hv i) (F i) j.val u =
        out i ⟨(directedPlan (rowKey n dir i)).length-1-j.val, by omega⟩ u)
    (clock : ℕ → ℕ) (row pre : Cmd)
    (localRun : Runs row (fun e : RowInput n hv dir => clock (n e.instanceIndex))
      (fun e => n e.instanceIndex) (fun e => .fork (send (e.ticket n hv dir)) (framed e.payload))
      (fun e => framed (out e.instanceIndex e.position e.payload)))
    (prepare : Runs pre (fun e : Admitted n hv => n e.val.1) (fun e => n e.val.1)
      (fun e => framed e.val.2)
      (fun e => .fork (send (chronological (rowKey n dir e.val.1))) (framed e.val.2)))
    (K : ℕ) (vol : ∀ i, (send (chronological (rowKey n dir i))).count ≤ K*(n i+1)) :
    Runs (pre.join (sweepCmd row))
      (fun e : Admitted n hv => 3*boxDepth (addressBits (n e.val.1))*clock (n e.val.1)+n e.val.1)
      (fun e => n e.val.1) (fun e => framed e.val.2) (fun e => framed (eval (hv e.val.1) (F e.val.1) e.val.2)) :=
  namedProgramAt n hv dir n (fun _ => le_rfl) hn hk F len ok out agree clock row pre localRun prepare K vol

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
