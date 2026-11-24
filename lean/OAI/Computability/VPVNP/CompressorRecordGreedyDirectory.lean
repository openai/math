import OAI.Computability.VPVNP.CompressorRecordGreedyPrepare

/-!
# Installing the greedy directory in external memory

After the first `k` calls, the first `k` mutable labels and the first `k`
records agree with the complete directory. The remaining words still have
their original values. In particular, each call sees the original control
words and both directed mate arrays.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy.WalkLayout

open BurstRAM BurstRAM.PrivateRAM Compression Compression.SlotGraph

variable {w N width d : ℕ} {V C : Type*}
variable (L : WalkLayout w N width)

/-- Memory after installing the first `k` indexed vertices. -/
def prefixMemory (ptrs : Fin N → List (Word w)) (outside : Memory w) (k : ℕ) : Memory w :=
  fun z ↦ if (L.origin ≤ z ∧ z < L.origin + k) ∨
      (L.origin + N ≤ z ∧ z < L.origin + N + k * (2 + width))
    then L.initialMemory ptrs outside z else outside z

@[simp] theorem prefixMemory_zero (ptrs : Fin N → List (Word w)) (outside : Memory w) :
    L.prefixMemory ptrs outside 0 = outside := by
  funext z
  simp [prefixMemory]

theorem prefixMemory_full (ptrs : Fin N → List (Word w)) (outside : Memory w) :
    L.prefixMemory ptrs outside N = L.initialMemory ptrs outside := by
  funext z
  unfold prefixMemory
  split
  · rfl
  · rename_i h
    by_cases hz : z < L.origin
    · simp [initialMemory, hz]
    · exact (L.initialMemory_after ptrs outside (by unfold limit; omega)).symm

private theorem stores_iff_fields (m : Memory w) (p : Word w) (xs : List (Word w))
    (fit : p.val + xs.length ≤ 2 ^ w) :
    Stores m p xs ↔ ∀ t : Fin xs.length, m (p.val + t.val) = xs[t.val] := by
  induction xs generalizing p with
  | nil => simp [Stores]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [Stores]
    | cons y ys =>
      have hn : (p + 1).val = p.val + 1 := by
        simp only [List.length_cons] at fit
        rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w),
          Nat.mod_eq_of_lt (by omega)]
      rw [Stores, ih _ (by simp only [hn, List.length_cons] at *; omega)]
      simp [Fin.forall_fin_succ, hn, Nat.add_assoc, Nat.add_comm 1]

/-- One complete row write, including the zero label, advances the memory invariant. -/
theorem write_prefixMemory (ptrs : Fin N → List (Word w)) (outside : Memory w)
    (size : ∀ i, (ptrs i).length = width) (i : Fin N) :
    writeRow (writeMemory (L.prefixMemory ptrs outside i.val) (L.label i) 0)
      (L.base i.val) (L.record ptrs i) = L.prefixMemory ptrs outside (i.val + 1) := by
  let p := L.origin + N + i.val * (2 + width)
  have bound := Nat.mul_le_mul_right (2 + width) (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at bound
  have fit := L.fits
  have hv : (L.base i.val).val = p := Nat.mod_eq_of_lt (by omega)
  have len : (L.record ptrs i).length = 2 + width := by simp [record, size]; omega
  have hfit : (L.base i.val).val + (L.record ptrs i).length ≤ 2 ^ w := by
    rw [hv, len]; dsimp [p]; omega
  funext z
  by_cases hz : p ≤ z ∧ z < p + (2 + width)
  · let t := z - p
    have ht : t < 2 + width := by dsimp [t]; omega
    have eq : z = p + t := by dsimp [t]; omega
    let m := writeMemory (L.prefixMemory ptrs outside i.val) (L.label i) 0
    have stored := (stores_iff_fields _ _ _ hfit).mp (writeRow_stores m _ _ hfit)
      ⟨t, by simpa only [len] using ht⟩
    rw [hv, ← eq] at stored
    rw [stored, prefixMemory, ite_eq_left (Or.inr ⟨by dsimp [p] at hz; omega,
      by rw [Nat.succ_mul]; dsimp [p] at hz; omega⟩), eq]
    rw [L.initialMemory_field ptrs outside i ht, List.getElem?_eq_getElem (len ▸ ht),
      Option.getD_some]
  · rw [writeRow_outside _ _ _ _ hfit (by rw [hv, len]; omega)]
    by_cases hl : z = (L.label i).val
    · subst z
      rw [writeMemory, ite_eq_left rfl, prefixMemory, ite_eq_left (Or.inl (by rw [label_val]; omega)),
        L.initialMemory_label]
    · rw [writeMemory, ite_eq_right hl]
      unfold prefixMemory
      rw [label_val] at hl
      dsimp [p] at hz
      rw [Nat.succ_mul]
      congr 1
      apply propext
      omega

/-- Partial installation preserves every word outside the walk allocation. -/
theorem prefixMemory_outside (ptrs : Fin N → List (Word w)) (outside : Memory w)
    {k z : ℕ} (hk : k ≤ N) (hz : z < L.origin ∨ L.limit ≤ z) :
    L.prefixMemory ptrs outside k z = outside z := by
  have h := Nat.mul_le_mul_right (2 + width) hk
  unfold limit at hz
  exact ite_eq_right (by omega)

/-- The prefix writes preserve the two mate arrays supplied to the initializer. -/
theorem prefixMemory_tables (ptrs : Fin N → List (Word w)) (outside : Memory w)
    {k : ℕ} {T : PortTables w} {G : SlotGraph V d} {order : V ≃ Fin N} (hk : k ≤ N)
    (rep : T.Represents G order outside) (free : GraphOutside (d := d) L T order) :
    T.Represents G order (L.prefixMemory ptrs outside k) := by
  refine ⟨rep.degree, rep.fits, rep.vertices, fun e ↦ ?_, fun e ↦ ?_⟩
  · rw [prefixMemory_outside L ptrs outside hk (free e _ (by simp)), rep.outgoing]
  · rw [prefixMemory_outside L ptrs outside hk (free e _ (by simp)), rep.incoming]

/-- The low control words are readable throughout preparation. -/
theorem prefixMemory_controls (ptrs : Fin N → List (Word w)) (outside : Memory w)
    {k : ℕ} {xs : List (Word w)} (hk : k ≤ N) (hs : Stores outside 0 xs)
    (h : xs.length ≤ L.origin) (fit : xs.length ≤ 2 ^ w) :
    Stores (L.prefixMemory ptrs outside k) 0 xs := by
  have hf : (0 : Word w).val + xs.length ≤ 2 ^ w := by simpa using fit
  rw [stores_iff_fields _ _ _ hf] at hs ⊢
  intro t
  rw [prefixMemory_outside L ptrs outside hk (.inl (by simpa using t.isLt.trans_le h))]
  exact hs t

/-- Lift native vertex writes along the successive prefix memories. -/
theorem prepare_segment (P : Program w C) (fuel probes steps : ℕ) (mem : ℕ → Memory w)
    (call : ∀ i : Fin N, ∃ es,
      execute P fuel (P.start (Fin.ofNat _ i.val)) (mem i.val) [] =
        some ⟨es, some (Fin.ofNat _ (i.val + 1))⟩ ∧
      after (mem i.val) es = mem (i.val + 1) ∧ es.length ≤ steps ∧ countProbes es = probes)
    (k remaining : ℕ) (bound : k + remaining ≤ N) :
    ∃ rs, runSegment P fuel (some (Fin.ofNat _ k)) (mem k) (List.replicate remaining []) = some rs ∧
      endState (some (Fin.ofNat _ k)) rs = some (Fin.ofNat _ (k + remaining)) ∧
      after (mem k) (eventLog rs) = mem (k + remaining) ∧ rs.length = remaining ∧
      RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs = remaining * (1 + probes) ∧
      ∀ r ∈ rs, r.events.length ≤ steps ∧ countProbes r.events = probes := by
  induction remaining generalizing k with
  | zero => exact ⟨[], rfl, rfl, rfl, rfl, by simp [RAMBuckets.cost], by simp⟩
  | succ remaining ih =>
    obtain ⟨es, he, hm, hs, hp⟩ := call ⟨k, by omega⟩
    let r : Report w := ⟨es, some (Fin.ofNat _ (k + 1))⟩
    obtain ⟨rs, run, hend, hfinal, hlen, hcost, hwork⟩ := ih (k + 1) (by omega)
    refine ⟨r :: rs, ?_, ?_, ?_, by simp [hlen], ?_, ?_⟩
    · simp only [List.replicate_succ, runSegment, he, hm, run, Option.map_some, r]
    · simpa only [endState, r, Nat.add_right_comm k 1, Nat.add_assoc] using hend
    · change List.foldl update (mem k) (es ++ eventLog rs) = _
      rw [List.foldl_append]
      change after (after (mem k) es) (eventLog rs) = _
      rw [hm, hfinal]
      congr 1
      omega
    · simp only [RAMBuckets.cost, r, hp, hcost, Nat.succ_mul, Nat.add_comm]
    · intro s h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨hs, hp⟩
      · exact hwork _ h

/-- The native initializer visits every vertex, returns its final cursor and installs the
complete directory. Calls include the control reads, the label and header writes,
and the probes used to obtain and store the operand pointers. -/
theorem prepare_directory (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows : OperandRows d) (outside : Memory w)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order outside)
    (control : Stores outside 0 (controlWords L T)) (low : 8 ≤ L.origin)
    (space : L.limit < 2 ^ w) (free : GraphOutside (d := d) L T order)
    (size : ∀ i : Fin N, (rowWords T G order (order.symm i) rows).length = width) :
    let P := (prepareMachine w rows).program
    let ptrs := fun i : Fin N ↦ rowWords T G order (order.symm i) rows
    ∃ rs, runSegment P (1 + (prepareCode rows).length) (some 0) outside
          (List.replicate N []) = some rs ∧
      endState (some 0) rs = some (Fin.ofNat _ N) ∧
      after outside (eventLog rs) = L.initialMemory ptrs outside ∧ rs.length = N ∧
      RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs =
        N * (12 + rows.length + width) ∧
      ∀ r ∈ rs, r.events.length ≤ 32 + 8 * rows.length + 6 * width ∧
        countProbes r.events = 11 + rows.length + width := by
  let ptrs := fun i : Fin N ↦ rowWords T G order (order.symm i) rows
  have lowFit : (controlWords L T).length ≤ 2 ^ w := by
    change 8 ≤ 2 ^ w
    unfold limit at space
    omega
  have call (i : Fin N) :=
    prepare_one L T G order rows (L.prefixMemory ptrs outside i.val) i labels
      (L.prefixMemory_tables ptrs outside i.isLt.le rep free)
      (L.prefixMemory_controls ptrs outside i.isLt.le control low lowFit)
      space free (size i)
  have whole := prepare_segment (N := N) (prepareMachine w rows).program
    (1 + (prepareCode rows).length) (11 + rows.length + width) (32 + 8 * rows.length + 6 * width)
    (L.prefixMemory ptrs outside) (fun i ↦ by
      obtain ⟨es, he, hm, hs, hp⟩ := call i
      exact ⟨es, he, hm.trans (L.write_prefixMemory ptrs outside size i), hs, hp⟩)
    0 N (by omega)
  have zero : Fin.ofNat _ 0 = (0 : Word w) := Fin.ext (Nat.zero_mod _)
  have cost : 1 + (11 + rows.length + width) = 12 + rows.length + width := by omega
  simpa only [prefixMemory_zero, Nat.zero_add, prefixMemory_full, zero, cost] using whole

end CompressorRecords.Greedy.WalkLayout

end VPVNP
end Computability
end OAI
