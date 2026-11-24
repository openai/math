import OAI.Computability.VPVNP.CompressorRefreshPlacementRows
import OAI.Computability.VPVNP.CompressorLogAccess
import OAI.Computability.VPVNP.CompressorScanProgress

/-!
# Packed placement arrays and the native degree - refresh trace

The owner, count and singleton preimage columns occupy three consecutive arrays.
Each source report writes the three cells of its ordinal and returns the next
ordinal. Thus a complete scan writes every address in the placement arena.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshPlacement

open BurstRAM SourceTransport
open scoped Fin.CommRing

/-- Sizes and addresses of the three packed placement columns. -/
def packed (w start N : ℕ) : Fin 6 → Word w :=
  ![N, start, N, (start + N : ℕ), 1, (start + 2 * N : ℕ)]

private theorem packed_fields {w start N : ℕ} (fit : start + 3 * N < 2 ^ w) :
    (packed w start N 0).val = N ∧ (packed w start N 1).val = start ∧
    (packed w start N 2).val = N ∧ (packed w start N 3).val = start + N ∧
    (packed w start N 4).val = 1 % (2 ^ w) ∧ (packed w start N 5).val = start + 2 * N := by
  have a : start < 2 ^ w := by omega
  have b : N < 2 ^ w := by omega
  have c : start + N < 2 ^ w := by omega
  have d : start + 2 * N < 2 ^ w := by omega
  exact ⟨Nat.mod_eq_of_lt b,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b,Nat.mod_eq_of_lt c,
    rfl,Nat.mod_eq_of_lt d⟩

theorem packed_values {w start N : ℕ} (fit : start + 3 * N < 2 ^ w) (one : 1 < 2 ^ w) :
    (packed w start N 0).val = N ∧ (packed w start N 1).val = start ∧
    (packed w start N 2).val = N ∧ (packed w start N 3).val = start + N ∧
    (packed w start N 4).val = 1 ∧ (packed w start N 5).val = start + 2 * N := by
  simpa only [Nat.mod_eq_of_lt one] using packed_fields fit

theorem packed_regions {w start N : ℕ} (fit : start + 3 * N < 2 ^ w) :
    RowRegions (packed w start N) := by
  obtain ⟨h₀,h₁,h₂,h₃,h₄,h₅⟩ := packed_fields fit
  constructor
  · rw [h₀,h₁,h₃]
  · rw [h₂,h₃,h₅]; omega
  · rw [h₂,h₄,h₅]
    have h := Nat.mul_le_mul_left N (Nat.mod_le 1 (2 ^ w))
    omega

theorem packed_cell_val {w start N : ℕ} (fit : start + 3 * N < 2 ^ w)
    (c : Fin 3) {i : ℕ} (hi : i < N) :
    (cell (packed w start N) c (Fin.ofNat _ i)).val = start + c.val * N + i := by
  obtain ⟨_,h₁,_,h₃,_,h₅⟩ := packed_fields fit
  have base : (bank (packed w start N) c).val = start + c.val * N := by
    fin_cases c <;> simp [bank,h₁,h₃,h₅]
  have room : start + c.val * N + i < 2 ^ w := by
    have h := Nat.mul_le_mul_right N (show c.val ≤ 2 from by omega)
    omega
  rw [cell,Fin.val_add,base,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : i < 2 ^ w),
    Nat.mod_eq_of_lt room]

theorem log_scanned {w : ℕ} (p : Fin 6 → Word w) (k n : ℕ) :
    StageFrame.Scanned k (k + n) (log p k n) := by
  induction n generalizing k with
  | zero => exact .done k
  | succ n ih =>
    apply StageFrame.Scanned.next (by omega)
    · change some ((k : Word w) + 1) = some ((k + 1 : ℕ) : Word w)
      rw [Nat.cast_add_one]
    · rw [show k + (n + 1) = k + 1 + n by omega]
      exact ih (k + 1)

theorem log_progress {w : ℕ} (p : Fin 6 → Word w) (k n : ℕ) (fit : k + n < 2 ^ w) :
    SourceOnline.Progress ((k + n : ℕ) : Word w) (k : Word w) (log p k n) :=
  (log_scanned p k n).toProgress fit

theorem log_reads {w : ℕ} (p : Fin 6 → Word w) (k n : ℕ) :
    Reads (fun _ ↦ False) (eventLog (log p k n)) := by
  induction n generalizing k with
  | zero => intro a v h; exact List.not_mem_nil h
  | succ n ih =>
    intro a v h
    rcases List.mem_append.mp h with head | tail
    · simp [report,events] at head
    · exact ih (k + 1) a v tail

private theorem write_events_iff {w : ℕ} (p : Fin 6 → Word w) (i a v : Word w) :
    Event.write a v ∈ events p i ↔ ∃ c : Fin 3, a = cell p c i ∧ v = value c i := by
  constructor
  · intro h
    simp only [events, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      Event.write.injEq] at h
    rcases h with h | h | h
    · exact ⟨0,h.1,h.2.trans (by simp [value])⟩
    · exact ⟨1,h.1,h.2.trans (by simp [value])⟩
    · exact ⟨2,h.1,h.2.trans (by simp [value])⟩
  · rintro ⟨c,rfl,rfl⟩
    fin_cases c <;> simp [events,value]

/-- An address - value pair is written precisely when it is the cell and payload of
one of the three columns at a visited ordinal. -/
theorem log_write_iff {w : ℕ} (p : Fin 6 → Word w) (k n : ℕ) (a v : Word w) :
    Event.write a v ∈ eventLog (log p k n) ↔
      ∃ i, k ≤ i ∧ i < k + n ∧ ∃ c : Fin 3,
        a = cell p c (Fin.ofNat _ i) ∧ v = value c (Fin.ofNat _ i) := by
  induction n generalizing k with
  | zero =>
    simp only [log,eventLog,List.flatMap_nil,List.not_mem_nil,Nat.add_zero,false_iff]
    rintro ⟨i,hi,hj,_⟩
    omega
  | succ n ih =>
    change Event.write a v ∈ events p (Fin.ofNat _ k) ++ eventLog (log p (k + 1) n) ↔ _
    rw [List.mem_append,write_events_iff,ih]
    constructor
    · rintro (h | ⟨i,h₁,h₂,h⟩)
      · exact ⟨k,le_rfl,by omega,h⟩
      · exact ⟨i,by omega,by omega,h⟩
    · rintro ⟨i,h₁,h₂,h⟩
      rcases eq_or_lt_of_le h₁ with rfl | hlt
      · exact Or.inl h
      · exact Or.inr ⟨i,hlt,by omega,h⟩

theorem packed_log_access {w start N k n : ℕ} (fit : start + 3 * N < 2 ^ w) (range : k + n ≤ N) :
    LogAccess (fun _ ↦ False) (fun x ↦ start ≤ x ∧ x < start + 3 * N)
      (log (packed w start N) k n) := by
  refine ⟨log_reads _ _ _,?_⟩
  intro a v h
  obtain ⟨i,_,hi,c,rfl,_⟩ := (log_write_iff _ _ _ _ _).mp h
  rw [packed_cell_val fit c (hi.trans_le range)]
  have hc := Nat.mul_le_mul_right N (show c.val ≤ 2 from by omega)
  omega

/-- Every cell of the full arena occurs as a genuine native write. -/
theorem packed_written_iff {w start N : ℕ} (fit : start + 3 * N < 2 ^ w) (a : Word w) :
    (∃ v, Event.write a v ∈ eventLog (log (packed w start N) 0 N)) ↔
      start ≤ a.val ∧ a.val < start + 3 * N := by
  constructor
  · rintro ⟨v,h⟩
    exact (packed_log_access fit (Nat.zero_add N).le).2 a v h
  · rintro ⟨ha,hb⟩
    have hit (c : Fin 3) (i : ℕ) (hi : i < N) (addr : a.val = start + c.val * N + i) :
        ∃ v, Event.write a v ∈ eventLog (log (packed w start N) 0 N) := by
      refine ⟨value c (Fin.ofNat _ i), (log_write_iff _ _ _ _ _).mpr
        ⟨i,Nat.zero_le _,by omega,c,Fin.ext ?_,rfl⟩⟩
      exact addr.trans (packed_cell_val fit c hi).symm
    by_cases h₀ : a.val < start + N
    · exact hit 0 (a.val - start) (by omega) (by simp; omega)
    by_cases h₁ : a.val < start + 2 * N
    · exact hit 1 (a.val - (start + N)) (by omega) (by simp; omega)
    · exact hit 2 (a.val - (start + 2 * N)) (by omega) (by simp; omega)

end CompressorRecords.RefreshPlacement

end VPVNP
end Computability
end OAI
