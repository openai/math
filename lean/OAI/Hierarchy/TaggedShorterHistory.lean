import OAI.ThreeFlat.Diagonal.TraceAdjacent

namespace OAI
/-! # The deterministic timed RAM history used by shorter-call control

Each CPU row checks its successor. Memory records include the initial stores
and their instruction timestamps. Sorting and checking predecessors therefore
recovers the values seen by the native machine, with a unique padded history.
-/

noncomputable section
namespace Hierarchy.TaggedShorterHistory
open ThreeFlat Diagonal
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory
open scoped Classical BigOperators

variable {w : ℕ} {C : Type*}

def Deterministic (P : Program w C) : Prop := ∀ c k, P.step c ≠ .branch k

/-- Read instructions take their actual memory value. Program rejection and
exhaustion of the clock give no accepting history. -/
def run (P : Program w C) : ℕ → C → Memory w → Option (Report w)
  | 0, _, _ => none
  | f+1, c, memory =>
    match P.step c with
    | .localStep next => (run P f next memory).map (Report.prepend .tick)
    | .read a next => (run P f (next (memory a.val)) memory).map (Report.prepend (.read a (memory a.val)))
    | .write a v next => (run P f next (writeMemory memory a v)).map (Report.prepend (.write a v))
    | .finish result => some ⟨[],result⟩
    | .branch _ | .reject => none

theorem reports (P : Program w C) (det : Deterministic P) (fuel : ℕ) (c : C) (memory : Memory w) :
    RAM.reports P fuel c memory = (run P fuel c memory).toList := by
  induction fuel generalizing c memory with
  | zero => rfl
  | succ f ih =>
    cases hs : P.step c with
    | branch k => exact (det c k hs).elim
    | localStep next | read a next | write a v next | finish result | reject =>
      simp [RAM.reports,run,hs,ih,Option.toList_map]

/-- Control conditions used by the guessed time rows and the sorted memory
scan. There is a fixed slot per possible instruction and a unique pad row. -/
def verifies (P : Program w C) (c : C) (S d : ℕ) (header : ℕ → Word w)
    (rows : List (TraceRows.Row w C)) : Prop :=
  TraceRows.before (rows.headD .pad) = some c ∧ TraceRows.pairs P rows ∧
    PaddedCheck none (TraceRecordSort.sorted S d header (TraceRows.report rows).events)

theorem verifies_iff (P : Program w C) (c : C) (S d : ℕ) (header : ℕ → Word w)
    (rows : List (TraceRows.Row w C)) (room : S+rows.length ≤ 2^d) :
    verifies P c S d header rows ↔ TraceRows.Local P c rows ∧
      Correct (initialMemory S header) (TraceRows.report rows).events := by
  rw [verifies,←and_assoc,←TraceRows.local_iff_pairs]
  apply and_congr_right
  intro localCheck
  have short := (TraceRows.local_spec localCheck).1.length_lt
  exact TraceRecordSort.sorted_iff_correct _ _ _ _ (by omega)

/-- A fixed output report (including writes of all control words) has
precisely one accepted padded history iff the deterministic machine returns it. -/
theorem unique_history (P : Program w C) (det : Deterministic P) (c : C)
    (S d fuel : ℕ) (header : ℕ → Word w) (room : S+fuel ≤ 2^d) (r : Report w) :
    (∃! rows : List (TraceRows.Row w C), rows.length = fuel ∧
      verifies P c S d header rows ∧ TraceRows.report rows = r) ↔
      run P fuel c (initialMemory S header) = some r := by
  have pred : (fun rows : List (TraceRows.Row w C) => rows.length = fuel ∧
      verifies P c S d header rows ∧ TraceRows.report rows = r) =
    fun rows => rows.length = fuel ∧ TraceRows.Local P c rows ∧ TraceRows.report rows = r ∧
      Correct (initialMemory S header) (TraceRows.report rows).events := by
    funext rows
    apply propext
    by_cases len : rows.length=fuel
    · simp only [len,true_and,verifies_iff P c S d header rows (by omega)]
      tauto
    · simp [len]
  change ExistsUnique _ ↔ _
  rw [pred,TraceRows.existsUnique_rows_iff,reports P det]
  cases eq : run P fuel c (initialMemory S header) <;> simp [eq_comm]

/-- A rejecting execution leaves every history term zero. -/
theorem exists_history (P : Program w C) (det : Deterministic P) (c : C)
    (S d fuel : ℕ) (header : ℕ → Word w) (room : S+fuel ≤ 2^d) (r : Report w) :
    (∃ rows : List (TraceRows.Row w C), rows.length = fuel ∧
      verifies P c S d header rows ∧ TraceRows.report rows = r) ↔
      run P fuel c (initialMemory S header) = some r := by
  constructor
  · rintro ⟨xs,len,pass,rep⟩
    obtain ⟨cpu,mem⟩ := (verifies_iff P c S d header xs (by omega)).mp pass
    have member : r ∈ RAM.reports P fuel c (initialMemory S header) :=
      (RAM.mem_reports_iff ..).mpr ⟨len ▸ rep ▸ (TraceRows.local_spec cpu).1,rep ▸ mem⟩
    rw [reports P det] at member
    cases eq : run P fuel c (initialMemory S header) <;> simp_all
  · intro h
    exact ((unique_history P det c S d fuel header room r).mpr h).exists

end Hierarchy.TaggedShorterHistory

end
end OAI
