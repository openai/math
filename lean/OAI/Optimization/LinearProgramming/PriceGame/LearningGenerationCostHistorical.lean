import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace GenerationCost

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

variable {α : Type}

/-- An unbounded initial interval, or a predecessor and its equality bit. -/
abbrev RawCell (α : Type) := Unit ⊕ (α × Bool)

def rawCellCode (ea : α → List Bool) : RawCell α → List Bool :=
  sumCode emptyCode (prodCode ea boolCode)

def rowChoices (row : List α) : List (RawCell α) :=
  Sum.inl () :: row.flatMap (fun x => [Sum.inr (x, false), Sum.inr (x, true)])

private noncomputable def taggedP (ea : α → List Bool) (b : Bool) :
    Procedure ea (rawCellCode ea) (fun x => Sum.inr (x, b)) := by
  let pair := (identity ea).pair (constant ea boolCode b)
  let tag : Procedure (prodCode ea boolCode) (rawCellCode ea) Sum.inr :=
    (prepend (prodCode ea boolCode) [true]).result (by intro x; rfl)
  exact tag.comp pair

/-- The two threshold choices are produced by a program, including the
cost of serializing the input threshold twice. -/
noncomputable def rowChoicesP (ea : α → List Bool) (da : α) :
    Procedure (listCode ea) (listCode (rawCellCode ea)) rowChoices := by
  let er := rawCellCode ea
  let last := (listCons er).comp ((taggedP ea true).pair (constant ea (listCode er) []))
  let pair := (listCons er).comp ((taggedP ea false).pair last)
  let allRows := (flattenP er (.inl ())).comp (listMap da [] pair)
  exact ((listCons er).comp ((constant (listCode ea) er (.inl ())).pair allRows)).congrFun
    (by intro row; rfl)

/-- The finite list of price-comparison codes produced on any threshold history.
The cap also bounds work on histories with extra feature rows. -/
def historicalCodes (cap : ℕ) (history : List (List α)) : List (List (RawCell α)) :=
  boundedProduct (RawCell α) cap (history.map rowChoices)

/-- A genuine finite binary-stack machine, including all its list operations
and a polynomial clock, for a fixed number of features. -/
noncomputable def historicalCodesP (ea : α → List Bool) (da : α) (cap : ℕ) :
    Procedure (listCode (listCode ea)) (listCode (listCode (rawCellCode ea)))
      (historicalCodes (α := α) cap) :=
  (boundedProductP (rawCellCode ea) (.inl ()) cap).comp (listMap [] [] (rowChoicesP ea da))

@[simp] theorem length_rowChoices (row : List α) : (rowChoices row).length = 2 * row.length + 1 := by
  induction row with
  | nil => simp [rowChoices]
  | cons x xs ih =>
    simp only [rowChoices, List.length_cons] at ih
    simp only [rowChoices, List.flatMap_cons, List.length_cons, List.cons_append, List.nil_append]
    omega

theorem length_cross (xs : List α) (tails : List (List α)) :
    (cross xs tails).length = xs.length * tails.length := by
  induction xs with
  | nil => simp [cross]
  | cons a xs ih => simp [cross, List.flatMap_cons, Nat.succ_mul, Nat.add_comm] at *

theorem length_boundedProduct (cap : ℕ) (rows : List (List α)) :
    (boundedProduct α cap rows).length = ((rows.take cap).map List.length).prod := by
  induction cap generalizing rows with
  | zero => simp [boundedProduct]
  | succ cap ih =>
    cases rows with
    | nil => simp [boundedProduct]
    | cons r rows => simp [boundedProduct, length_cross, ih]

theorem length_historicalCodes (cap : ℕ) (history : List (List α)) :
    (historicalCodes cap history).length = ((history.take cap).map (fun r => 2 * r.length + 1)).prod := by
  unfold historicalCodes
  rw [length_boundedProduct, ← List.map_take, List.map_map]
  simp only [Function.comp_def, length_rowChoices]

def wireCell {s : Finset ℚ} : Cells.Cell s → RawCell ℚ
  | none => .inl ()
  | some (θ, b) => .inr (θ.val, b)

private theorem wireCell_mem {s : Finset ℚ} (c : Cells.Cell s) :
    wireCell c ∈ rowChoices (s.sort (· ≤ ·)) := by
  cases c with
  | none => simp [wireCell, rowChoices]
  | some t =>
    obtain ⟨⟨θ,hθ⟩, b⟩ := t
    cases b <;> simp [wireCell, rowChoices, hθ]

/-- A deterministic wire ordering for the compact coordinate-pair histories. -/
def historyRows {n : ℕ} (s : Experts.Feature n → Finset ℚ) : List (List ℚ) :=
  (FinEnum.toList (Experts.Feature n)).map fun f => (s f).sort (· ≤ ·)

def serializeCell {n : ℕ} {s : Experts.Feature n → Finset ℚ} (c : Experts.Code s) :
    List (RawCell ℚ) := (FinEnum.toList (Experts.Feature n)).map (fun f => wireCell (c f))

theorem serializeCell_mem {n cap : ℕ} (s : Experts.Feature n → Finset ℚ)
    (c : Experts.Code s) (h : n*n ≤ cap) : serializeCell c ∈ historicalCodes cap (historyRows s) := by
  let features := FinEnum.toList (Experts.Feature n)
  have hl : features.length = n*n := by
    simp only [features, FinEnum.toList, List.length_map, List.length_finRange]
    rw [FinEnum.card_eq_fintypeCard]
    simp [Experts.Feature]
  unfold historicalCodes historyRows
  rw [List.map_map]
  exact mem_boundedProduct_of_select (fun f => rowChoices ((s f).sort (· ≤ ·)))
    (fun f => wireCell (c f)) features cap (by omega) fun f _ => wireCell_mem (c f)

theorem source_cap_covers {p : ℕ} (hp : p ≤ 65) (s : Experts.Feature (p+1) → Finset ℚ)
    (c : Experts.Code s) : serializeCell c ∈ historicalCodes (66*66) (historyRows s) :=
  serializeCell_mem s c ((Nat.mul_le_mul (by omega) (by omega)) : (p+1)*(p+1) ≤ 66*66)

/-- The bit measure used by the binary machine agrees with the paper's integer ceiling. -/
theorem size_eq_clog_succ (R : ℕ) : R.size = Nat.clog 2 (R+1) := by
  apply le_antisymm
  · exact Nat.size_le.mpr (Nat.le_pow_clog (by decide : 1 < 2) (R+1))
  · exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (Nat.lt_size_self R)

end GenerationCost
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
