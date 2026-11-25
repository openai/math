import OAI.Computability.BorderVNP.DiagonalCheckedCellNative

/-! # The ordered batch of checked reports and genuine private auxiliary tapes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open CellSparse Packing.BottomReports FiniteDiagonal.CellTrace
open scoped Classical

/-- Data fixed before an owned cell guesses its counts and source uses. -/
structure AssignedCell (l : ReportLayout) where
  /-- The per-cell report whose tape is filled with the guessed bits. -/
  report : ReportCell l
  /-- The directory before the bundle-use records are appended. -/
  initial : Directory
  /-- Number of private Boolean wires assigned by this cell. -/
  privateWires : ℕ
  /-- The values on those private wires. -/
  assignment : Fin privateWires → Bool
  /-- Boundary bits following the private assignment. -/
  boundary : List Bool
  /-- The ordered bundles whose uses are recorded in the report. -/
  bundles : List Bundle
  /-- Observed guard outcomes and their optional indices, in order. -/
  observations : List (Bool × Option ℕ)

variable {l : ReportLayout}

/-- Concatenate the private assignment and the boundary bits. -/
def AssignedCell.pre (s : AssignedCell l) := List.ofFn s.assignment ++ s.boundary

/-- Append bundle-use records after the private, boundary and count fields. -/
def AssignedCell.augmented (s : AssignedCell l) := appendRows s.initial
  (supplements (s.privateWires+s.boundary.length+l.gadgets*l.countWidth) s.bundles)

/-- The canonical report tail determined by the observations and bundle uses. -/
noncomputable def AssignedCell.spelling (s : AssignedCell l) :=
  canonicalTail s.observations l.gadgets l.countWidth s.pre s.bundles

/-- Local data of a genuine passing assignment, stated entirely in terms
of the stored source, true count range, and the actual typed clock. -/
structure AssignedCell.Passing (s : AssignedCell l) (w order : ℕ) : Prop where
  positiveWord : 0 < w
  unsigned : s.initial.SignFree
  layout : s.initial.reportedCounts=countFields (s.privateWires+s.boundary.length) l.gadgets l.countWidth
  seen : ∀ t, s.initial.guardedObservations (lookup (s.pre++t))=some s.observations
  core : ∀ b ∈ s.bundles, b.CorePass s.pre
  uses : (s.report.bundles.map ReportBundle.useCount).sum=(s.bundles.map Bundle.useBits).sum
  range : ∀ i ∈ s.observations.filterMap Prod.snd, i < l.gadgets
  fit : ∀ i : Fin l.gadgets, (s.observations.filterMap Prod.snd).count i.val < 2^l.countWidth
  widths : s.initial.ProfileWidths
  clock : ∀ x : Fin s.report.tailWidth → Bool,
    Copied.FitsClock s.augmented w order s.privateWires (s.boundary++List.ofFn x)

theorem AssignedCell.spelling_length {s : AssignedCell l} {w order : ℕ} (h : s.Passing w order) :
    s.spelling.length=s.report.tailWidth := by
  simp only [spelling,canonicalTail,List.length_append,countPart_length,useTape_length,ReportCell.tailWidth,h.uses]

/-- The copied evaluator accepts this report on the augmented directory with the specified return. -/
def AssignedCell.Returns (s : AssignedCell l) (w order : ℕ) (r : ReportCell l) (ret : List Bool × Bool) : Prop :=
  Copied.Accepted s.augmented w order s.assignment (s.boundary++r.bits) ret.1 ret.2

/-- Classification at the arbitrary physical cursor of this cell in its
team's raw report choice stream. -/
theorem AssignedCell.native (s : AssignedCell l) (w order : ℕ) (h : s.Passing w order) :
    ∃ u : List Bool, ∀ (a : ℕ → Bool) (p : ℕ) (ret : List Bool × Bool),
      s.Returns w order (s.report.withTape a p) ret ↔
      (s.report.withTape a p).bits=s.spelling ∧ ret=(u,false) := by
  obtain ⟨u,hu⟩ := fixed_native_cell s.report s.initial s.assignment s.boundary s.bundles s.observations
    h.unsigned h.layout h.seen h.core h.uses h.range h.fit h.positiveWord h.widths h.clock
  refine ⟨u,fun a p ret => ?_⟩
  rw [Returns,ReportCell.withTape_bits]
  rcases ret with ⟨t,sg⟩
  exact (hu (fun i => a (p+i.val)) t sg).trans (by simp only [Prod.mk.injEq]; rfl)

/-- Per-cell native tape and sign in exactly the order of the report batch. -/
def BatchReturns (w order : ℕ) : List (AssignedCell l) → List (ReportCell l) → List (List Bool × Bool) → Prop
  | [],[],[] => True
  | s::ss,r::rs,t::ts => s.Returns w order r t ∧ BatchReturns w order ss rs ts
  | _,_,_ => False

/-- All successful native cells in a team force exactly one raw report byte
string and exactly one residual tape per cell. Conversely these prescribed
choices return, with positive sign at every cell. -/
theorem batch_native (w order : ℕ) (ss : List (AssignedCell l)) (ok : ∀ s ∈ ss, s.Passing w order) :
    ∃ aux : List (List Bool), ∀ (a : ℕ → Bool) (p : ℕ) (returns : List (List Bool × Bool)),
      let rows := tapeCells a p (ss.map AssignedCell.report)
      BatchReturns w order ss rows returns ↔
        reportBits rows = ss.flatMap AssignedCell.spelling ∧ returns=aux.map (fun u => (u,false)) := by
  induction ss with
  | nil =>
    refine ⟨[],fun a p returns => ?_⟩
    cases returns <;> simp [tapeCells,BatchReturns,reportBits]
  | cons s ss ih =>
    obtain ⟨u,hu⟩ := s.native w order (ok s List.mem_cons_self)
    obtain ⟨us,hus⟩ := ih (fun s h => ok s (.tail _ h))
    refine ⟨u::us,fun a p returns => ?_⟩
    cases returns with
    | nil => simp [tapeCells,BatchReturns]
    | cons t ts =>
      simp only [List.map_cons,tapeCells,BatchReturns,hu,hus,reportBits,List.flatMap_cons,List.cons.injEq]
      have len : (s.report.withTape a p).bits.length = s.spelling.length := by
        rw [ReportCell.bits_length,ReportCell.withTape_tailWidth,s.spelling_length (ok s List.mem_cons_self)]
      constructor
      · rintro ⟨⟨hr,ht⟩,hs,hts⟩
        exact ⟨congrArg₂ List.append hr hs,ht,hts⟩
      · rintro ⟨eqn,ht,hts⟩
        obtain ⟨hr,hs⟩ := List.append_inj eqn len
        exact ⟨⟨hr,ht⟩,hs,hts⟩

/-- The canonical batch word always has the exact length of the report
arena. This lets a real native choice tape realize it, including an empty
batch, empty gadget fields and zero-use sites. -/
theorem batch_spelling_length (w order : ℕ) (ss : List (AssignedCell l)) (ok : ∀ s ∈ ss, s.Passing w order) :
    (ss.flatMap AssignedCell.spelling).length=(reportBits (ss.map AssignedCell.report)).length := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.flatMap_cons,List.map_cons,reportBits,List.length_append,ReportCell.bits_length]
    exact congrArg₂ Nat.add (s.spelling_length (ok s List.mem_cons_self)) (ih (fun v hv => ok v (.tail _ hv)))

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
