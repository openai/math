import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomAligned
import OAI.Computability.NearSquareRoot.InterchangeROMEffectiveSeries

/-! # Computable syntax of aligned columns and record operations -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip GeneratorSyntax

variable {X : Type} [Primcodable X]

/-- A split quotes exactly the two leaf cases, the node case and the default branch. -/
theorem effective_split {i : X → ℕ} {leaf : X → Bool → Cmd} {node : X → Cmd}
    (hi : Computable i) (hl : ∀ b, Effective ltr (fun x => leaf x b)) (hn : Effective ltr node) :
    Effective ltr (fun x => splitRoot (i x) (leaf x) (node x)) := by
  unfold splitRoot
  apply effective_look ltr hi
  intro top
  apply (effective_pop ltr hi).join
  cases top with
  | none => exact effective_const ltr .pass
  | some t =>
    cases t with
    | node => exact hn
    | bit b => exact hl b
    | sep => exact effective_const ltr .pass

theorem effective_map {op : X → Cmd} (ho : Effective ltr op) :
    Effective ltr (fun x => mapCommand (op x)) :=
  (effective_split (Computable.const 0) (fun b => effective_const ltr (give 0 b))
    (ho.join (effective_const ltr ((move 0 1 2).join ((Prog.again 0).join ((move 1 0 2).join (pack 0))))))).tie

theorem effective_column {n : X → ℕ} (hn : Computable n) :
    Effective ltr (fun x => columnCommand (n x)) :=
  effective_map (InterchangeROM.effective_cell hn)

private theorem index_range {K : Type} [DecidableEq K] (cols : Series K) :
    cols.explore.map (fun a => cols.explore.idxOf a) = List.range cols.count := by
  apply List.ext_getElem (by simp [Series.count])
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, cols.nodup.idxOf_getElem]

/-- Every enumeration of the same width emits the identical rank sequence. -/
theorem transpose_eq_range {K : Type} [DecidableEq K] (cols : Series K) :
    transposeCommand cols = seriesCommand columnCommand (List.range cols.count) := by
  rw [← index_range cols, InterchangeROM.series_map]
  rfl

/-- A numeric width can replace an abstract output layout in the emitted command. -/
theorem aligned_eq_natural {L : Type} [DecidableEq L] (rank : ℕ) (cols : Series L) (op : Cmd) :
    alignedCommand rank cols op = alignedCommand rank (Series.natural cols.count) op := by
  simp only [alignedCommand, alignedCore, transpose_eq_range, Series.count_natural]

variable {K : X → Type} [∀ x, DecidableEq (K x)]

/-- Only the number of fields is needed to quote the transpose, including
when the field type and its enumeration depend on the candidate. -/
theorem effective_transpose (cols : (x : X) → Series (K x)) (h : Computable fun x => (cols x).count) :
    Effective ltr (fun x => transposeCommand (cols x)) := by
  simp only [transpose_eq_range]
  exact InterchangeROM.effective_series (effective_column (Computable.snd : Computable (@Prod.snd X ℕ)))
    (Primrec.list_range.to_comp.comp h)

open private scaffold eraseCell from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomAligned

private theorem effective_scaffold {n : X → ℕ} (hn : Computable n) :
    Effective ltr (fun x => scaffold (n x)) :=
  (effective_const ltr (clone 0 1 2)).join ((InterchangeROM.effective_cell hn).join
    (effective_const ltr ((mapCommand eraseCell).join ((move 1 0 2).join (pack 0)))))

theorem effective_alignedCore (cols : (x : X) → Series (K x))
    (hc : Computable fun x => (cols x).count) {op : X → Cmd} (ho : Effective ltr op) :
    Effective ltr (fun x => alignedCore (cols x) (op x)) :=
  (effective_const ltr blendCommand).join ((effective_map ho).join (effective_transpose cols hc))

theorem effective_aligned {rank : X → ℕ} (hr : Computable rank) (cols : (x : X) → Series (K x))
    (hc : Computable fun x => (cols x).count) {op : X → Cmd} (ho : Effective ltr op) :
    Effective ltr (fun x => alignedCommand (rank x) (cols x) (op x)) :=
  (effective_scaffold hr).join (effective_alignedCore cols hc ho)

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
