import OAI.Computability.VPVNP.EvaluatorMatrixStep
import OAI.Computability.VPVNP.EvaluatorSafetyTransfer
import OAI.Computability.VPVNP.EvaluatorRadixDivision
import OAI.Computability.VPVNP.SliceArithmeticCallClear
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-!
# The basis index registers of the evaluator

Each step preserves the advised dimension and the old ordinal while it
generates the new ordinal in the little-endian format used by the query
routines. Once the entry has been used, committing the new ordinal clears
the scratch stacks and prepares the registers for another step.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.IndexRegisters

open RAMTape EvaluatorRadixDivision SliceArithmetic

/-- Stacks for the basis dimension, current ordinal, bounded guess and the scratch used to
commit the next ordinal. -/
inductive Port where
  | dimension | current | bound | reversed | next | scratch
  deriving DecidableEq

instance : Fintype Port :=
  ⟨{.dimension, .current, .bound, .reversed, .next, .scratch}, fun k ↦ by cases k <;> simp⟩

/-- The two index words available during an entry query. At a step boundary
the next index is empty. -/
def bank (dimension current next : List Bool) : Stacks Port
  | .dimension => dimension | .current => current | .next => next | _ => []

private def prepared (dim cur : List Bool) := Function.update (bank dim cur []) .bound dim

private def prepare : FiniteRoutine Port := SuccessorFields.prependCopy .dimension .bound .scratch

/-- Guess once below the dimension and restore the chosen word to the
same bit order as the old index. -/
def select : FiniteRoutine Port :=
  .ofRoutine (matrixStep .bound .reversed prepare.body (reverseOnto .reversed .next).body)

private theorem prepare_runs (dim cur : List Bool) :
    prepare.Runs (5*dim.length+2) (bank dim cur []) (prepared dim cur) := by
  simpa only [prepare, prepared, bank, List.append_nil] using
    SuccessorFields.prependCopy_runs Port.dimension .bound .scratch (by decide) (by decide)
      (by decide) (bank dim cur []) rfl

private theorem selected_runs (dim cur bits : List Bool) :
    (reverseOnto .reversed .next).Runs (2*bits.length+1)
      (IndexChoice.written .bound .reversed (prepared dim cur) bits) (bank dim cur bits) := by
  let chosen := IndexChoice.written Port.bound .reversed (prepared dim cur) bits
  have hlen : (chosen .reversed).length = bits.length := by simp [chosen, IndexChoice.written, prepared, bank]
  rw [← hlen]
  apply reverseOnto_runs (by decide : Port.reversed ≠ .next) _ _ rfl
  · simp [chosen, IndexChoice.written, prepared, bank]
  · intro k hrev hn
    cases k <;> first | contradiction | rfl

theorem select_count {v : ℕ} (n : BurstRAM.Word v) (cur : List Bool)
    (c : ℕ → Stacks Port → ℕ) (fuel : ℕ) :
    select.body.count c (fuel+(10*v+5)) (bank (BurstRAM.wordBits n) cur []) =
      ∑ j : Fin n.val, c fuel (bank (BurstRAM.wordBits n) cur
        (BurstRAM.wordBits (Fin.castLE n.isLt.le j : BurstRAM.Word v))) := by
  let dim := BurstRAM.wordBits n
  let bits (j : Fin n.val) := BurstRAM.wordBits (Fin.castLE n.isLt.le j : BurstRAM.Word v)
  have hp := prepare_runs dim cur
  simp only [dim, BurstRAM.length_wordBits] at hp
  let chosen (j : Fin n.val) := IndexChoice.written .bound .reversed (prepared dim cur) (bits j)
  have hr (j : Fin n.val) :
      (reverseOnto .reversed .next).Runs (2*v+1) (chosen j) (bank dim cur (bits j)) := by
    simpa only [bits, BurstRAM.length_wordBits] using selected_runs dim cur (bits j)
  have hc := matrixStep_count Port.bound .reversed prepare.body (reverseOnto .reversed .next).body
    (by decide) n hp rfl (fun j ↦ bank dim cur (bits j)) (fun _ ↦ 2*v+1) hr c
    (fuel+(2*v+1)) (fun _ ↦ by omega)
  rw [show fuel+(2*v+1)+(3*v+2)+(5*v+2) = fuel+(10*v+5) by omega] at hc
  simp only [Nat.add_sub_cancel] at hc
  exact hc

/-- The selection code preserves a polynomial storage bound on both branches
of every choice. All returning branches supply an in-range ordinal. -/
theorem select_safe {v : ℕ} (n : BurstRAM.Word v) (cur : List Bool)
    (safe : Stacks Port → Prop) (cont : ℕ → Stacks Port → Prop) (reserve : ℕ)
    (hroom : ∀ s, (∀ k, (s k).length ≤ (bank (BurstRAM.wordBits n) cur [] k).length + (10*v+5)) → safe s)
    (hc : ∀ j : Fin n.val, cont reserve (bank (BurstRAM.wordBits n) cur
      (BurstRAM.wordBits (Fin.castLE n.isLt.le j : BurstRAM.Word v)))) :
    select.body.Safe safe cont (reserve+(10*v+5)) (bank (BurstRAM.wordBits n) cur []) := by
  apply EvaluatorRoutineSafety.safe_of_allStops cont reserve _ hroom
  let dim := BurstRAM.wordBits n
  let c (left : ℕ) := cont (reserve+left)
  let post := (reverseOnto Port.reversed .next).body
  change ((prepare.body.followedBy (IndexChoice.guessBelow Port.bound .reversed)).followedBy post).AllStops
    c (10*v+5) (bank dim cur [])
  rw [Routine.allStops_followedBy, Routine.allStops_followedBy]
  have hp := prepare_runs dim cur
  simp only [dim, BurstRAM.length_wordBits] at hp
  rw [show 10*v+5 = (2*v+1+(3*v+2))+(5*v+2) by omega, hp.allStops_iff]
  apply IndexChoice.allStops_guessBelow Port.bound Port.reversed (by decide) n _ rfl (post.AllStops c) (2*v+1)
  intro j
  let bits := BurstRAM.wordBits (Fin.castLE n.isLt.le j : BurstRAM.Word v)
  have hh := selected_runs dim cur bits
  simp only [bits, BurstRAM.length_wordBits] at hh
  have h := (hh.allStops_iff c 0).mpr (hc j)
  simpa only [Nat.zero_add] using h

/-- Replace the old ordinal by the new one after the matrix entry query. -/
def commit : FiniteRoutine Port :=
  ((CallClear.clear .current).followedBy (reverseOnto .next .reversed)).followedBy
    (reverseOnto .reversed .current)

theorem commit_runs (dim cur next : List Bool) :
    commit.Runs (cur.length + 4*next.length + 3) (bank dim cur next) (bank dim next []) := by
  let mid := bank dim [] next
  let rev := Function.update (bank dim [] []) .reversed next.reverse
  have clear : (CallClear.clear .current).Runs (cur.length+1) (bank dim cur next) mid := by
    have hc := CallClear.clear_runs Port.current (bank dim cur next)
    have h : Function.update (bank dim cur next) .current [] = mid := by
      funext p
      cases p <;> rfl
    rwa [h] at hc
  have first : (reverseOnto .next .reversed).Runs (2*next.length+1) mid rev := by
    apply reverseOnto_runs (by decide : Port.next ≠ .reversed) mid rev rfl
    · simp [mid, rev, bank]
    · intro k hn hr
      cases k <;> first | contradiction | rfl
  have last : (reverseOnto .reversed .current).Runs (2*next.length+1) rev (bank dim next []) := by
    have hlen : (rev .reversed).length = next.length := by simp [rev]
    rw [← hlen]
    apply reverseOnto_runs (by decide : Port.reversed ≠ .current) _ _ rfl
    · simp [rev, bank]
    · intro k hrev hc
      cases k <;> first | contradiction | rfl
  have run := (clear.followedBy first).followedBy last
  rwa [show cur.length+1+(2*next.length+1)+(2*next.length+1) = cur.length+4*next.length+3 by omega] at run

end Evaluator.IndexRegisters

end VPVNP
end Computability
end OAI
