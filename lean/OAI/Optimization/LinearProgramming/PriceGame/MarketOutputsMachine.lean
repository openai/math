import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Computability.QuantumFactoring.BitStackListFold
import OAI.Optimization.LinearProgramming.PriceGame.MarketExecutablePrices

/-! # Finite bit-stack procedures for market output operations

The procedures below operate on explicit binary encodings of signed rationals,
natural flows, and lists of numbered options. The scan keeps the earliest
maximizer, matching the deterministic tie rule for a zero-weight expert.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace OutputMachine
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

abbrev ScoredOption := ℕ × ℚ
abbrev scoredCode : ScoredOption → List Bool := prodCode Nat.bits ratCode

/-- Destination numbering reserves zero for the dummy. -/
def optionNumber {g : ℕ} : Option (Fin g) → ℕ
  | none => 0
  | some i => i.val + 1

def chooseBetter (pair : ScoredOption × ScoredOption) : ScoredOption :=
  if pair.2.2 < pair.1.2 then pair.1 else pair.2

/-- One actual finite-machine comparison of a new entry against the incumbent. -/
noncomputable def chooseBetterP : Procedure (prodCode scoredCode scoredCode) scoredCode chooseBetter := by
  let cand := first scoredCode scoredCode
  let incumbent := second scoredCode scoredCode
  let utility := second Nat.bits ratCode
  let improve := OracleSpec.Arithmetic.ratLt.comp ((utility.comp incumbent).pair (utility.comp cand))
  exact ((choose incumbent cand).comp (improve.pair (identity (prodCode scoredCode scoredCode)))).congrFun
    (by intro p; by_cases h : p.2.2 < p.1.2 <;> simp [chooseBetter, h])

private theorem take_best_mem (xs : List ScoredOption) (b : ScoredOption) :
    xs.foldl (fun b a => chooseBetter (a,b)) b ∈ b :: xs := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih =>
    have h := ih (chooseBetter (a,b))
    simp only [List.mem_cons] at h
    simp only [List.foldl_cons, List.mem_cons]
    rcases h with he | he
    · rw [he]
      unfold chooseBetter
      split <;> simp
    · exact Or.inr (Or.inr he)

private theorem code_entry_le (xs : List ScoredOption) (a : ScoredOption) (ha : a ∈ xs) :
    (scoredCode a).length ≤ (listCode scoredCode xs).length := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [listCode_length_cons]
    rcases List.mem_cons.mp ha with rfl | hh
    · omega
    · have := ih hh; omega

/-- Folding the first-max scan has a polynomial machine bound because the
accumulator is a literal earlier record from the encoded input list. -/
noncomputable def bestRowP : Procedure (prodCode (listCode scoredCode) scoredCode) scoredCode
    (fun p => p.1.foldl (fun b a => chooseBetter (a,b)) p.2) := by
  refine foldList (0,0) chooseBetterP Polynomial.X ?_
  intro xs b i
  rw [Polynomial.eval_X]
  have hm := take_best_mem (xs.take i) b
  rcases List.mem_cons.mp hm with he | he
  · rw [he]; omega
  · have hb := code_entry_le xs _ (List.mem_of_mem_take he)
    omega

private theorem fold_aux_map {α : Type} (label : α → ℕ) (u : α → ℚ)
    (xs : List α) (base : α) :
    (xs.map (fun x => (label x, u x))).foldl (fun b a => chooseBetter (a,b)) (label base,u base) =
      ((xs.foldl (List.argAux (fun x y => u y < u x)) (some base)).map
        (fun x => (label x, u x))).getD (0,0) := by
  induction xs generalizing base with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.foldl_cons, List.argAux, chooseBetter]
    split <;> exact ih _

/-- The encoded finite maximum is exactly the good chosen by `Market.best`. -/
theorem bestRow_eq {g : ℕ} (available : Fin g → Bool) (u : Option (Fin g) → ℚ) :
    ((((List.finRange g).filter available).map fun i => (optionNumber (some i), u (some i))).foldl
      (fun b a => chooseBetter (a,b)) (optionNumber (none : Option (Fin g)), u none)) =
    (optionNumber (best available u), u (best available u)) := by
  let xs := ((List.finRange g).filter available).map some
  have hm := fold_aux_map optionNumber u xs none
  have hh : (options available).argmax u =
      xs.foldl (List.argAux (fun x y => u y < u x)) (some none) := rfl
  have har := best_mem_argmax available u
  rw [Option.mem_def] at har
  rw [← hh, har] at hm
  simpa [xs, List.map_map, Function.comp_def] using hm

abbrev quoteInputCode : (Bool × ℚ × ℚ) → List Bool :=
  prodCode boolCode (prodCode ratCode ratCode)

/-- A signed bid minus the indicated price on a real market arc. -/
noncomputable def quoteP : Procedure quoteInputCode ratCode
    (fun x => if x.1 then x.2.1 - x.2.2 else x.2.1 + x.2.2) := by
  let sign := first boolCode (prodCode ratCode ratCode)
  let values := second boolCode (prodCode ratCode ratCode)
  exact (choose ratAdd ratSub).comp (sign.pair values)

theorem quote_eq_score {e g : ℕ} (pos : Fin e → Bool) (c : Fin e → Fin g → ℚ)
    (y : Fin g → ℚ) (k : Fin e) (i : Fin g) :
    (if pos k then c k i - y i else c k i + y i) = score pos c y k (some i) := by
  cases h : pos k <;> simp [score, side, h]

/-- Divide binary integral option and row totals to obtain their reduced fraction. -/
noncomputable def fractionP : Procedure (prodCode Nat.bits Nat.bits) ratCode
    (fun pair => (pair.1 : ℚ) / (pair.2 : ℚ)) :=
  ratDiv.comp ((natToRat.comp (first Nat.bits Nat.bits)).pair (natToRat.comp (second Nat.bits Nat.bits)))

/-- Read a good and dummy potential and compute their difference in the paper's orientation. -/
noncomputable def priceP : Procedure (prodCode ratCode ratCode) ratCode
    (fun p => p.1 - p.2) := ratSub

end OutputMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
