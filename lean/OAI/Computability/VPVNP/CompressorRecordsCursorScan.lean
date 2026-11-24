import OAI.Computability.VPVNP.CompressorRecordsCursorRAM
import OAI.Computability.VPVNP.RAMBuckets

/-!
# Native scan of the initial cursor graph

One burst call writes the six forward, inverse, displacement and width cells
for one numbered outgoing slot. This scan allows repeated visits to the same
base cell from different lanes. Agreement with a common specification suffices
for every visited cell to contain its specified value at the end of the scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CursorRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Six address/value pairs written by the call with natural index `j`. -/
def rowWrites (p : Fin 11 → Word w) (j : ℕ) : List (Word w × Word w) :=
  let i := Fin.ofNat (2 ^ w) j
  writes p i (wordRow p i)

/-- Addresses visited in the half-open interval of row indices `[k,k+n)`. -/
def Touches (p : Fin 11 → Word w) (k n addr : ℕ) : Prop :=
  ∃ j, k ≤ j ∧ j < k + n ∧ ∃ av ∈ rowWrites p j, av.1.val = addr

/-- The complete trace with one report per row, including the persistent
index for the next call. -/
def scanReports (p : Fin 11 → Word w) (k : ℕ) : ℕ → List (Report w)
  | 0 => []
  | n+1 => ⟨events p (Fin.ofNat _ k), some (Fin.ofNat _ (k+1))⟩ :: scanReports p (k+1) n

private theorem word_succ (k : ℕ) :
    Fin.ofNat (2 ^ w) k + 1 = Fin.ofNat (2 ^ w) (k + 1) := by
  apply Fin.ext
  simp [Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]

/-- Execution of precisely the calls whose initial indices are in the interval. -/
theorem scan_native (p : Fin 11 → Word w) (k n : ℕ) (m : Memory w) :
    let M := (template visit 0).instantiate w p
    runSegment M.program (1 + visit.length) (some (Fin.ofNat _ k)) m (List.replicate n []) =
      some (scanReports p k n) := by
  induction n generalizing k m with
  | zero => rfl
  | succ n ih =>
    dsimp only
    rw [List.replicate_succ, runSegment, visit_native, word_succ]
    simp only [ih, Option.map_some, scanReports]

/-- The returned state can be used as the starting cursor of a following segment. -/
theorem scanReports_endState (p : Fin 11 → Word w) (k n : ℕ) :
    endState (some (Fin.ofNat _ k)) (scanReports p k n) = some (Fin.ofNat _ (k+n)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [scanReports, endState, ih]
    congr 2
    omega

private theorem fold_writes_at (xs : List (Word w × Word w)) (m spec : Memory w)
    (agree : ∀ av ∈ xs, spec av.1.val = av.2) (addr : ℕ) :
    (xs.foldl (fun mem av ↦ writeMemory mem av.1 av.2) m) addr =
      if ∃ av ∈ xs, av.1.val = addr then spec addr else m addr := by
  induction xs generalizing m with
  | nil => simp
  | cons av xs ih =>
    rw [List.foldl_cons, ih _ (fun u hu ↦ agree u (List.mem_cons_of_mem _ hu))]
    by_cases ht : ∃ u ∈ xs, u.1.val = addr
    · simp [ht]
    · by_cases he : addr = av.1.val
      · subst addr
        simp [ht, writeMemory, agree av (List.mem_cons_self ..)]
      · simp [ht, he, Ne.symm he, writeMemory]

private theorem touches_succ (p : Fin 11 → Word w) (k n addr : ℕ) :
    Touches p k (n + 1) addr ↔ (∃ av ∈ rowWrites p k, av.1.val = addr) ∨
      Touches p (k+1) n addr := by
  constructor
  · rintro ⟨j, hj, hlt, h⟩
    rcases eq_or_lt_of_le hj with he | he
    · exact .inl (he ▸ h)
    · exact .inr ⟨j, by omega, by omega, h⟩
  · rintro (h | ⟨j,hj,hlt,h⟩)
    · exact ⟨k, le_rfl, by omega, h⟩
    · exact ⟨j, by omega, by omega, h⟩

private theorem scan_after (p : Fin 11 → Word w) (k n : ℕ) (m spec : Memory w)
    (agree : ∀ j, k ≤ j → j < k + n → ∀ av ∈ rowWrites p j, spec av.1.val = av.2)
    (addr : ℕ) :
    letI := Classical.propDecidable
    after m (eventLog (scanReports p k n)) addr =
      if Touches p k n addr then spec addr else m addr := by
  classical
  induction n generalizing k m with
  | zero =>
    have h : ¬ Touches p k 0 addr := by rintro ⟨j,hj,hlt,_⟩; omega
    simp [h, scanReports, eventLog, after]
  | succ n ih =>
    let es := events p (Fin.ofNat _ k)
    have hlog : after m (eventLog (scanReports p k (n+1))) =
        after (after m es) (eventLog (scanReports p (k+1) n)) := by
      simp only [scanReports, eventLog, List.flatMap_cons, after, List.foldl_append, es]
    have hrow : after m es addr =
        if ∃ av ∈ rowWrites p k, av.1.val = addr then spec addr else m addr := by
      rw [events_after]
      exact fold_writes_at (rowWrites p k) m spec (agree k le_rfl (by omega)) addr
    rw [hlog, ih (k+1) (after m es) (fun j hj hlt ↦ agree j (by omega) (by omega))]
    by_cases ht : Touches p (k+1) n addr <;>
      simp [ht, hrow, touches_succ]

theorem scanReports_length (p : Fin 11 → Word w) (k n : ℕ) :
    (scanReports p k n).length = n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [scanReports, ih]

theorem scanReports_work (p : Fin 11 → Word w) (k n : ℕ) :
    ∀ r ∈ scanReports p k n, r.events.length = visit.length ∧ countProbes r.events = 6 := by
  induction n generalizing k with
  | zero => simp [scanReports]
  | succ n ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · exact events_work p _
    · exact ih (k+1) r h

/-- One call plus six probes per slot, with six matching writes even when
multiple lanes visit the same base incidence. -/
theorem scan_cost (p : Fin 11 → Word w) (k n : ℕ) :
    RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) (scanReports p k n) = 7 * n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [scanReports, RAMBuckets.cost, (events_work p _).2, ih, Nat.mul_succ]
    omega

/-- All native calls, their exact work, the contents of each constructed
record, and preservation of every address outside the six scanned columns. -/
theorem scan_run (p : Fin 11 → Word w) (k n : ℕ) (m spec : Memory w)
    (agree : ∀ j, k ≤ j → j < k + n → ∀ av ∈ rowWrites p j, spec av.1.val = av.2) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program (1 + visit.length) (some (Fin.ofNat _ k)) m (List.replicate n []) =
      some rs ∧ rs.length = n ∧ (∀ r ∈ rs, r.events.length = visit.length ∧ countProbes r.events = 6) ∧
      (∀ addr, Touches p k n addr → after m (eventLog rs) addr = spec addr) ∧
      (∀ addr, ¬ Touches p k n addr → after m (eventLog rs) addr = m addr) := by
  classical
  refine ⟨scanReports p k n, scan_native p k n m, scanReports_length p k n,
    scanReports_work p k n, ?_, ?_⟩
  · intro addr h
    simpa only [h, ite_true] using scan_after p k n m spec agree addr
  · intro addr h
    simpa only [h, ite_false] using scan_after p k n m spec agree addr

end CompressorRecords.CursorRAM

end VPVNP
end Computability
end OAI
