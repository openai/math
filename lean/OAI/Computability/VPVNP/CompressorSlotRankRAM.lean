import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.RAMWork

/-!
# Native RAM ranks for ordered incidence slots

The input row lists the incident slot keys in the order in which the descriptor
builder found them. The burst call counts keys strictly below its persistent
input and writes the count to the endpoint's slot field. It reads each key once.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotRankRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Register 0 is the moving read address, 1 the pivot, 2 the unit,
3 the running count and 4 a temporary word. -/
private def visit : List (Op 5 2) :=
  [.read 4 0, .binary .add 4 4 2, .binary .div 4 1 4, .binary .div 4 4 4,
   .binary .add 3 3 4, .binary .add 0 0 2]

private def scan : ℕ → List (Op 5 2)
  | 0 => []
  | n + 1 => visit ++ scan n

/-- Public words 0 and 1 are the row address and destination address.
The rank accumulator starts at zero on entry to the burst call. -/
def rankCode (n : ℕ) : List (Op 5 2) :=
  [.publicWord 0 0, .stateWord 1, .constant 2 1] ++ scan n ++
    [.publicWord 4 1, .write 4 3]

theorem rankCode_length (n : ℕ) : (rankCode n).length = 6 * n + 5 := by
  have h : (scan n).length = 6 * n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [scan, visit, ih]; omega
  simp [rankCode, h]

/-- Unsigned division by the key's successor, followed by a nonzero test,
implements strict order on word values. -/
private theorem quotient_indicator (pivot key : Word w) (hkey : key.val + 1 < 2 ^ w) :
    let q := BinaryOp.div.eval pivot (key + 1)
    BinaryOp.div.eval q q = if key < pivot then 1 else 0 := by
  dsimp only
  have h1 : (1 : Word w).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hs : (key + 1).val = key.val + 1 := by
    rw [Fin.val_add, h1, Nat.mod_eq_of_lt hkey]
  have hq : (BinaryOp.div.eval pivot (key + 1)).val = pivot.val / (key.val + 1) := by
    change (pivot.val / (key + 1).val) % (2 ^ w) = _
    rw [hs, Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt pivot.isLt)]
  change Fin.ofNat _ ((BinaryOp.div.eval pivot (key + 1)).val /
    (BinaryOp.div.eval pivot (key + 1)).val) = _
  rw [hq]
  by_cases h : key < pivot
  · rw [ite_eq_left h, Nat.div_self (Nat.div_pos (Fin.lt_def.mp h) (Nat.zero_lt_succ _))]
    rfl
  · rw [ite_eq_right h, Nat.div_eq_of_lt (Nat.lt_succ_of_le (le_of_not_gt (show ¬key.val < pivot.val from h)))]
    rfl

private def holds (mem : Memory w) (ptr : Word w) : List (Word w) → Prop
  | [] => True
  | key :: ks => mem ptr.val = key ∧ holds mem (ptr + 1) ks

private theorem holds_of_getElem (mem : Memory w) (ptr : Word w) (row : List (Word w))
    (hmem : ∀ i : Fin row.length, mem (ptr.val + i.val) = row[i.val])
    (haddr : ptr.val + row.length ≤ 2 ^ w) : holds mem ptr row := by
  induction row generalizing ptr with
  | nil => trivial
  | cons key ks ih =>
    simp only [List.length_cons] at haddr
    have hle : (ptr + 1).val ≤ ptr.val + 1 := by
      rw [Fin.val_add, Fin.val_one']
      exact (Nat.mod_le _ _).trans (Nat.add_le_add_left (Nat.mod_le _ _) _)
    refine ⟨hmem ⟨0, by simp⟩, ih _ (fun i => ?_) (by omega)⟩
    have hi := i.isLt
    have hnext : (ptr + 1).val = ptr.val + 1 := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^w by omega),
        Nat.mod_eq_of_lt (by omega)]
    simpa [hnext, Nat.add_assoc, Nat.add_comm 1 i.val] using hmem i.succ

private def scanEvents (ptr : Word w) : List (Word w) → List (Event w)
  | [] => []
  | key :: ks => .read ptr key :: .tick :: .tick :: .tick :: .tick :: .tick ::
      scanEvents (ptr + 1) ks

private theorem scanEvents_spec (ptr : Word w) (row : List (Word w)) (mem : Memory w)
    (es : List (Event w)) :
    countProbes (scanEvents ptr row ++ es) = row.length + countProbes es ∧
    (scanEvents ptr row ++ es).length = 6 * row.length + es.length ∧
    after mem (scanEvents ptr row ++ es) = after mem es := by
  induction row generalizing ptr with
  | nil => simp [scanEvents]
  | cons key ks ih =>
    obtain ⟨hc, hl, hm⟩ := ih (ptr + 1)
    refine ⟨?_, ?_, hm⟩
    · change 1 + countProbes (scanEvents (ptr + 1) ks ++ es) = ks.length + 1 + _
      omega
    · change (scanEvents (ptr + 1) ks ++ es).length + 6 = 6 * (ks.length + 1) + es.length
      omega

private theorem visit_trace (pub : Fin 2 → Word w) (pivot key : Word w) (mem : Memory w)
    (rs : Regs w 5) (hp : rs 1 = pivot) (hu : rs 2 = 1) (hm : mem (rs 0).val = key)
    (hk : key.val + 1 < 2 ^ w) :
    ∃ mid, trace pub pivot visit rs mem =
      some ([.read (rs 0) key, .tick, .tick, .tick, .tick, .tick], mid, mem) ∧
      mid 0 = rs 0 + 1 ∧ mid 1 = pivot ∧ mid 2 = 1 ∧
      mid 3 = rs 3 + (if key < pivot then 1 else 0) := by
  have hf := quotient_indicator pivot key hk
  simp (config := { decide := true }) [visit, trace, Op.effect, BinaryOp.eval, Function.update,
    hm, hp, hu] at hf ⊢
  exact hf ▸ rfl

private theorem scan_trace (pub : Fin 2 → Word w) (pivot : Word w) (mem : Memory w)
    (row : List (Word w)) (rs : Regs w 5) (hp : rs 1 = pivot) (hu : rs 2 = 1)
    (hm : holds mem (rs 0) row) (hk : ∀ key ∈ row, key.val + 1 < 2 ^ w)
    (hsize : (rs 3).val + row.length < 2 ^ w) :
    ∃ out, trace pub pivot (scan row.length) rs mem =
      some (scanEvents (rs 0) row, out, mem) ∧
      (out 3).val = (rs 3).val + (row.filter fun key => decide (key < pivot)).length := by
  induction row generalizing rs with
  | nil => exact ⟨rs, rfl, rfl⟩
  | cons key ks ih =>
    obtain ⟨hhead, htail⟩ := hm
    have hkey := hk key (List.mem_cons_self ..)
    obtain ⟨mid, hmid, hptr, hpiv, hone, hrank⟩ := visit_trace pub pivot key mem rs hp hu hhead hkey
    simp only [List.length_cons] at hsize
    have hv : (mid 3).val = (rs 3).val + (if key < pivot then 1 else 0) := by
      rw [hrank, Fin.val_add]
      split_ifs <;> simp only [Fin.val_one', Fin.val_zero, Nat.add_zero]
      · rw [Nat.mod_eq_of_lt (show 1 < 2^w by omega), Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (rs 3).isLt]
    obtain ⟨out, htrace, hvout⟩ := ih mid hpiv hone (hptr ▸ htail)
      (fun k h => hk k (List.mem_cons_of_mem _ h)) (by rw [hv]; split <;> omega)
    refine ⟨out, ?_, ?_⟩
    · simp [scan, trace_append, hmid, htrace, hptr, scanEvents]
    · rw [hvout, hv]
      by_cases h : key < pivot <;> simp [h]
      omega

/-- The call starts with a fresh private workspace, reads the entire row in
descriptor order, writes the strict rank to the requested field, and returns it.
The destination may coincide with a source cell since the write follows all reads. -/
theorem rank_native (pub : Fin 2 → Word w) (pivot : Word w) (mem : Memory w)
    (row : List (Word w))
    (hmem : ∀ i : Fin row.length, mem ((pub 0).val + i.val) = row[i.val])
    (haddr : (pub 0).val + row.length ≤ 2 ^ w) (hsize : row.length < 2 ^ w)
    (hkeys : ∀ key ∈ row, key.val + 1 < 2 ^ w) :
    let rank := (row.filter fun key => decide (key < pivot)).length
    let M := (template (rankCode row.length) 3).instantiate w pub
    ∃ es, execute M.program (6 * row.length + 6) (M.program.start pivot) mem [] =
        some ⟨es, some (Fin.ofNat _ rank)⟩ ∧
      after mem es = writeMemory mem (pub 1) (Fin.ofNat _ rank) ∧
      countProbes es = row.length + 1 ∧ es.length + 1 = 6 * row.length + 6 := by
  dsimp only
  let rank := (row.filter fun key => decide (key < pivot)).length
  let init : Regs w 5 := Function.update (Function.update
    (Function.update (fun _ => 0) (0 : Fin 5) (pub 0)) 1 pivot) 2 1
  have hi : trace pub pivot [.publicWord 0 0, .stateWord 1, .constant 2 1]
      (fun _ : Fin 5 => 0) mem = some ([.tick, .tick, .tick], init, mem) := rfl
  obtain ⟨out, htrace, hv⟩ := scan_trace pub pivot mem row init (by simp [init]) (by simp [init])
    (by simpa [init] using holds_of_getElem mem (pub 0) row hmem haddr) hkeys (by simpa [init] using hsize)
  have hrank : out 3 = Fin.ofNat _ rank := by
    apply Fin.ext
    change (out 3).val = rank % (2^w)
    rw [Nat.mod_eq_of_lt ((List.length_filter_le ..).trans_lt hsize)]
    simpa [init, rank] using hv
  let tail : List (Event w) := [.tick, .write (pub 1) (Fin.ofNat _ rank)]
  have ht : trace pub pivot [.publicWord 4 1, .write 4 3] out mem =
      some (tail, Function.update out 4 (pub 1), writeMemory mem (pub 1) (Fin.ofNat _ rank)) := by
    simp [trace, Op.effect, tail, hrank]
  have he := scanEvents_spec (pub 0) row mem tail
  obtain ⟨hc, hl, hm⟩ := he
  refine ⟨.tick :: .tick :: .tick :: (scanEvents (pub 0) row ++ tail), ?_, hm, hc, ?_⟩
  · rw [show 6 * row.length + 6 = 1 + (rankCode row.length).length by rw [rankCode_length]; omega]
    change execute ((template (rankCode row.length) 3).instantiate w pub).program _
      ⟨_, pivot, fun _ => 0, fun _ => 0⟩ mem [] = _
    rw [execute_template, run_eq_trace, rankCode, trace_append, trace_append, hi]
    simp [htrace, ht, hrank, init, rank]
  · change (scanEvents (pub 0) row ++ tail).length + 4 = _
    change (scanEvents (pub 0) row ++ tail).length = 6 * row.length + 2 at hl
    omega

/-- The table uses only registers and external probes. In the metered opcode
interpreter each dispatch costs at most six elementary word operations, including
when a supplied read stream stops early. -/
theorem rank_opcode_work (pub : Fin 2 → Word w) (pivot : Word w) (n allowance : ℕ)
    (bits : List Bool) :
    let M := (template (rankCode n) 3).instantiate w pub
    M.loggedDispatchWork (6 * n + 6) (M.logProgram.start pivot) allowance bits ≤ 36 * n + 36 := by
  let M := (template (rankCode n) 3).instantiate w pub
  have noLog (l : LogConfig w ((rankCode n).length + 2) 5) :
      (M.code l.pc).actualLogWork l = 0 := by
    simp only [M, Template.instantiate, template]
    split
    · cases (rankCode n)[l.pc.val] <;> rfl
    · split <;> rfl
  have bound (fuel : ℕ) (l : LogConfig w ((rankCode n).length + 2) 5) (a : ℕ) (bs : List Bool) :
      M.loggedDispatchWork fuel l a bs ≤ 6 * fuel := by
    induction fuel generalizing l a bs with
    | zero => rfl
    | succ f ih =>
      rw [Machine.loggedDispatchWork, noLog, Nat.add_zero]
      have h := (M.code l.pc).wordWork_le
      split
      · omega
      · rename_i l' a' bs' _
        have := ih l' a' bs'
        omega
  have h := bound (6 * n + 6) (M.logProgram.start pivot) allowance bits
  change M.loggedDispatchWork (6 * n + 6) (M.logProgram.start pivot) allowance bits ≤ 36 * n + 36
  omega

end CompressorRecords.SlotRankRAM

end VPVNP
end Computability
end OAI
