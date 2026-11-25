import OAI.Optimization.LinearProgramming.PriceGame.ControlWeightFolds
import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyLoops

/-! # Concrete finite-stack updates for the weights of a suspended market trial -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Trial

abbrev rawWeightInputCode := prodCode Nat.bits (prodCode assemblyCallsCode ratCode)

private theorem prod_read {α : Type} [Inhabited α] (xs : List α) (f : α → ℚ) :
    (∏ t ∈ Finset.range xs.length, f (atD xs t)) = (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, Finset.prod_range_succ', List.map_cons, List.prod_cons]
    have h0 : atD (x::xs) 0 = x := rfl
    have hnext (i : ℕ) : atD (x::xs) (i+1) = atD xs i := by simp [atD]
    simp only [hnext, h0, ih, mul_comm]

private theorem sum_read {α : Type} [Inhabited α] (xs : List α) (f : α → ℕ) :
    (∑ t ∈ Finset.range xs.length, f (atD xs t)) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    have h0 : atD (x::xs) 0 = x := rfl
    have hnext (i : ℕ) : atD (x::xs) (i+1) = atD xs i := by simp [atD]
    simp only [hnext, h0, ih, Nat.add_comm]

private noncomputable def gainsP : Procedure rawWeightInputCode (listCode ratCode)
    (fun p => p.2.1.map (fun c => atD c.gains p.1)) := by
  let expert := first Nat.bits (prodCode assemblyCallsCode ratCode)
  let rest := second Nat.bits (prodCode assemblyCallsCode ratCode)
  let calls := (first assemblyCallsCode ratCode).comp rest
  exact (columnP ratCode completedGainsP).comp (calls.pair expert)

private noncomputable def scoresP : Procedure rawWeightInputCode (listCode Nat.bits)
    (fun p => p.2.1.map (fun c => atD c.child.scores p.1)) := by
  let expert := first Nat.bits (prodCode assemblyCallsCode ratCode)
  let rest := second Nat.bits (prodCode assemblyCallsCode ratCode)
  let calls := (first assemblyCallsCode ratCode).comp rest
  exact (columnP Nat.bits (roundScoresP.comp completedChildP)).comp (calls.pair expert)

private noncomputable def rawInitialP : Procedure rawWeightInputCode ratCode (fun p => p.2.2) :=
  (second assemblyCallsCode ratCode).comp (second Nat.bits (prodCode assemblyCallsCode ratCode))

/-- An actual bit program whose output is the raw local-expert update on the
encoded calls, expert address, and incoming weight. -/
noncomputable def localWeightRawP : Procedure rawWeightInputCode ratCode
    (fun p => localWeightRaw p.2.1 p.1 p.2.2) :=
  (gainProductP.comp (gainsP.pair rawInitialP)).congrFun (by
    rintro ⟨e,calls,w⟩
    change w * ((calls.map (fun c => atD c.gains e)).map
      (fun gain => 1 + Moment.etaQ * gain)).prod = _
    simp only [List.map_map, localWeightRaw]
    exact congrArg (fun z => w*z) (prod_read calls (fun c => 1+Moment.etaQ*atD c.gains e)).symm)

def scoreTotal (calls : List Completed) (e : ℕ) : ℕ := (calls.map fun c => atD c.child.scores e).sum

def deepCapped (budget : ℕ) (calls : List Completed) (e : ℕ) (w : ℚ) :=
  w * (2 : ℚ) ^ min budget (scoreTotal calls e)

noncomputable def deepWeightRawP : Procedure (prodCode unaryCode rawWeightInputCode) ratCode
    (fun p => deepCapped p.1 p.2.2.1 p.2.1 p.2.2.2) := by
  let k := first unaryCode rawWeightInputCode
  let input := second unaryCode rawWeightInputCode
  exact scoreProductP.comp (k.pair ((scoresP.comp input).pair (rawInitialP.comp input)))

theorem deepCapped_eq {budget : ℕ} (calls : List Completed) (e : ℕ) (w : ℚ)
    (h : scoreTotal calls e ≤ budget) : deepCapped budget calls e w = deepWeightRaw calls e w := by
  rw [deepCapped, min_eq_right h, scoreTotal, deepWeightRaw]
  exact congrArg (fun n : ℕ => w*2^n) (sum_read calls (fun c => atD c.child.scores e)).symm

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
