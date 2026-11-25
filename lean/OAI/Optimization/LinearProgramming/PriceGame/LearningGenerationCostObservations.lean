import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCostHistorical
import OAI.Optimization.LinearProgramming.PriceGame.LearningCutCode

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace GenerationCost

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- Compare the unknown value with an observed threshold from a wire cell.
The two returned predicates are the literal bits in a cut observation. -/
def rawDecode (c : RawCell ℚ) (θ : ℚ) : Ordering :=
  match c with
  | .inl _ => .lt
  | .inr (r,b) =>
    if θ < r then .gt else if θ = r then (if b then .eq else .gt) else .lt

theorem rawDecode_wireCell {s : Finset ℚ} (c : Cells.Cell s) (θ : ℚ) :
    rawDecode (wireCell c) θ = Cells.decode c θ := by
  cases c with
  | none => rfl
  | some t => obtain ⟨v,b⟩ := t; rfl

private def pred : RawCell ℚ → ℚ := Sum.elim (fun _ => 0) Prod.fst
private def hit : RawCell ℚ → Bool := Sum.elim (fun _ => false) Prod.snd
private def present : RawCell ℚ → Bool := Sum.elim (fun _ => false) (fun _ => true)

private noncomputable def rawLowP :
    Procedure (prodCode ratCode (rawCellCode ratCode)) boolCode
      (fun x : ℚ × RawCell ℚ => decide (rawDecode x.2 x.1 = .lt)) := by
  let e := prodCode ratCode (rawCellCode ratCode)
  let c := second ratCode (rawCellCode ratCode)
  let θ := first ratCode (rawCellCode ratCode)
  let getPred : Procedure (rawCellCode ratCode) ratCode pred :=
    casesSum (constant emptyCode ratCode 0) (first ratCode boolCode)
  let getPresent : Procedure (rawCellCode ratCode) boolCode present :=
    casesSum (constant emptyCode boolCode false) (constant (prodCode ratCode boolCode) boolCode true)
  let less := OracleSpec.Arithmetic.ratLt.comp ((getPred.comp c).pair θ)
  apply (conditional (getPresent.comp c) less (constant e boolCode true)).congrFun
  rintro ⟨x, _ | ⟨r,b⟩⟩
  · rfl
  · change decide (r < x) = decide (rawDecode (.inr (r,b)) x = .lt)
    rcases lt_trichotomy x r with h|h|h
    · simp [rawDecode,h,not_lt_of_gt h]
    · subst r; cases b <;> simp [rawDecode]
    · simp [rawDecode,h,not_lt_of_gt h,ne_of_gt h]

private noncomputable def rawHighP :
    Procedure (prodCode ratCode (rawCellCode ratCode)) boolCode
      (fun x : ℚ × RawCell ℚ => decide (rawDecode x.2 x.1 = .gt)) := by
  let e := prodCode ratCode (rawCellCode ratCode)
  let c := second ratCode (rawCellCode ratCode)
  let θ := first ratCode (rawCellCode ratCode)
  let getPred : Procedure (rawCellCode ratCode) ratCode pred :=
    casesSum (constant emptyCode ratCode 0) (first ratCode boolCode)
  let getPresent : Procedure (rawCellCode ratCode) boolCode present :=
    casesSum (constant emptyCode boolCode false) (constant (prodCode ratCode boolCode) boolCode true)
  let getHit : Procedure (rawCellCode ratCode) boolCode hit :=
    casesSum (constant emptyCode boolCode false) (second ratCode boolCode)
  let args := θ.pair (getPred.comp c)
  let high := conditional (getHit.comp c) (OracleSpec.Arithmetic.ratLt.comp args) (OracleSpec.Arithmetic.ratLe.comp args)
  apply (conditional (getPresent.comp c) high (constant e boolCode false)).congrFun
  rintro ⟨x, _ | ⟨r,b⟩⟩
  · rfl
  · change (if b then decide (x < r) else decide (x ≤ r)) =
      decide (rawDecode (.inr (r,b)) x = .gt)
    rcases lt_trichotomy x r with h|h|h
    · cases b <;> simp [rawDecode,h,h.le]
    · subst r; cases b <;> simp [rawDecode]
    · cases b <;> simp [rawDecode,not_lt_of_gt h,not_le_of_gt h,ne_of_gt h]

private def mkObs {n} (f : Experts.Feature n) (x : ℚ × RawCell ℚ) : Observation n :=
  ⟨f.1, f.2, x.1, rawDecode x.2 x.1⟩

private noncomputable def mkObsP {n : ℕ} (f : Experts.Feature n) :
    Procedure (prodCode ratCode (rawCellCode ratCode)) (BitMachine.cutObservationCode n) (mkObs f) := by
  let e := prodCode ratCode (rawCellCode ratCode)
  let proc := (constant e Nat.bits f.1.val).pair ((constant e Nat.bits f.2.val).pair
    ((first ratCode (rawCellCode ratCode)).pair (rawLowP.pair rawHighP)))
  exact proc.result (by intro x; rfl)

abbrev CandidateAndHistory := List (RawCell ℚ) × List (List ℚ)
def candidateHistoryCode := prodCode (listCode (rawCellCode ratCode)) (listCode (listCode ratCode))

/-- Entries missing from a malformed or short table are supplied with defaults.
Only actual historic thresholds generate observations. -/
def observe {n : ℕ} : List (Experts.Feature n) → CandidateAndHistory → List (Observation n)
  | [], _ => []
  | f :: fs, (cs, rs) =>
    (rs.headD []).map (fun θ => mkObs f (θ, cs.headD (.inl ()))) ++ observe fs (cs.tail, rs.tail)

/-- Program for the exact full observation list sent to the difference-constraint solver. -/
noncomputable def observeP {n : ℕ} (fs : List (Experts.Feature n)) :
    Procedure candidateHistoryCode (listCode (BitMachine.cutObservationCode n)) (observe fs) := by
  induction fs with
  | nil => exact constant _ _ []
  | cons f fs ih =>
    let ec := rawCellCode ratCode
    let es := listCode (listCode ratCode)
    let cs := first (listCode ec) es
    let rs := second (listCode ec) es
    let row := (listHead (listCode ratCode) []).comp rs
    let cell := (listHead ec (.inl ())).comp cs
    let d : Observation n := ⟨f.1,f.2,0,.eq⟩
    let block := (mapContextP 0 d (mkObsP f)).comp (row.pair cell)
    let rest := ih.comp (((listTail ec).comp cs).pair ((listTail (listCode ratCode)).comp rs))
    exact (listAppend (BitMachine.cutObservationCode n) d).comp (block.pair rest)

private theorem observe_serial {n : ℕ} (fs : List (Experts.Feature n)) (s : Experts.Feature n → Finset ℚ)
    (c : Experts.Code s) :
    observe fs (fs.map (fun f => wireCell (c f)), fs.map (fun f => (s f).sort (· ≤ ·))) =
    fs.flatMap (fun f => ((s f).sort (· ≤ ·)).map (fun θ =>
      (⟨f.1,f.2,θ,Cells.decode (c f) θ⟩ : Observation n))) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [observe,mkObs,rawDecode_wireCell,ih]

/-- The cut order, indices, exact thresholds, and comparison tags agree with
the reference `Experts.observations` on every serialized candidate. -/
theorem observe_serializeCell {n : ℕ} (s : Experts.Feature n → Finset ℚ) (c : Experts.Code s) :
    observe (FinEnum.toList (Experts.Feature n)) (serializeCell c, historyRows s) =
      Experts.observations s c := observe_serial _ _ _

end GenerationCost
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
