import OAI.Computability.NearSquareRoot.CRTControlledFlatSwapList
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Two fixed commands for the forward and reverse swap files

The universal input covers every width, table, and record stream satisfying the
volume and length estimates. Each direction therefore uses one command with a
constant register bound across the entire range of input parameters.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code IntegerMultiplication.Strip
open NearSquareRoot.Space NearSquareRoot.CommonRegisters NearSquareRoot.GeneratorSyntax
open NearSquareRoot.EffectiveBoundedTask Filter

noncomputable section

structure SwapCase where
  k : ℕ
  V : ℕ
  moves : List (Fin k × Fin k)
  distinct : ∀ p ∈ moves, p.1 ≠ p.2
  length_le : moves.length ≤ k
  records : Block 2 k → Tree
  fits : (stripe (line 2 k) records).count ≤ V

def SwapCase.cost (x : SwapCase) := (x.moves.length+1)*x.V

def SwapCase.input (x : SwapCase) : Tree :=
  .fork (send (flatSwapInput x.k x.moves)) (stripe (line 2 x.k) x.records)

def SwapCase.output (backwards : Bool) (x : SwapCase) : Tree :=
  stripe (line 2 x.k) (x.records ∘ swapsFlat (if backwards then x.moves.reverse else x.moves))

private theorem swapTask (backwards : Bool) :
    BoundedTask SwapCase.cost SwapCase.V SwapCase.input (SwapCase.output backwards) :=
  boundedFlatSwaps backwards SwapCase.k SwapCase.V SwapCase.moves SwapCase.distinct 1
    (fun x => by have := x.length_le; omega) SwapCase.records SwapCase.fits

def swapCmd (backwards : Bool) : Cmd := (swapTask backwards).choose

theorem swap_all_runs (backwards : Bool) :
    Runs (swapCmd backwards) SwapCase.cost SwapCase.V SwapCase.input (SwapCase.output backwards) :=
  (swapTask backwards).choose_spec

theorem swap_runs (backwards : Bool) {I : Type} (k V : I → ℕ)
    (moves : (i : I) → List (Fin (k i) × Fin (k i)))
    (distinct : ∀ i, ∀ p ∈ moves i, p.1 ≠ p.2) (length_le : ∀ i, (moves i).length ≤ k i)
    (f : (i : I) → Block 2 (k i) → Tree)
    (fits : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i) :
    Runs (swapCmd backwards) (fun i => ((moves i).length+1)*V i) V
      (fun i => .fork (send (flatSwapInput (k i) (moves i))) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ swapsFlat (if backwards then (moves i).reverse else moves i))) :=
  (swap_all_runs backwards).on (fun i => ⟨k i,V i,moves i,distinct i,length_le i,f i,fits i⟩)

/-- Both fixed commands use one common finite set of registers. -/
theorem swap_within : ∀ᶠ R : ℕ in atTop, ∀ backwards, Within R (swapCmd backwards) := by
  filter_upwards [RegisterSelect.within_eventually (swapCmd false),
    RegisterSelect.within_eventually (swapCmd true)] with R f t b
  cases b <;> assumption

theorem swap_registers : ∃ R : ℕ, 0 < R ∧ ∀ backwards, Within R (swapCmd backwards) :=
  (Filter.Eventually.and (eventually_gt_atTop 0) swap_within).exists

theorem swap_effective : Effective ltr swapCmd := by
  exact (Computable.cond Computable.id (Computable.const (file ltr (swapCmd true)))
    (Computable.const (file ltr (swapCmd false)))).of_eq (fun b => by cases b <;> rfl)

theorem swap_effective_const {J : Type} [Primcodable J] (backwards : Bool) :
    Effective ltr (fun _ : J => swapCmd backwards) := effective_const _ _

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
