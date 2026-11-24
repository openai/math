import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMRecords

/-!
# Inverting a rectangular endpoint table in external RAM

The input is indexed by ordered incidence and gives the absolute endpoint field of
that incidence. One burst call reads this field and stores the incidence index at
that field in the inverse table. An injective input can leave holes in the inverse
table. The pass preserves every hole as well as all memory outside the table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotScatter

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w n capacity : ℕ}

/-- Public words give the base of the field table and the base of the inverse table.
Register 0 is the incidence index and becomes the next call's persistent cursor. -/
def visit : List (Op 4 2) :=
  [.stateWord 0, .publicWord 1 0, .binary .add 1 1 0, .read 2 1,
   .publicWord 3 1, .binary .add 3 3 2, .write 3 0, .constant 1 1, .binary .add 0 0 1]

/-- The read and the write in program order, including the intervening arithmetic. -/
def events (pub : Fin 2 → Word w) (i field : Word w) : List (Event w) :=
  [.tick, .tick, .tick, .read (pub 0 + i) field, .tick, .tick, .write (pub 1 + field) i,
   .tick, .tick]

theorem visit_native (pub : Fin 2 → Word w) (mem : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w pub
    execute M.program 10 (M.program.start i) mem [] =
      some ⟨events pub i (mem (pub 0 + i).val), some (i + 1)⟩ := by
  change execute ((template visit 0).instantiate w pub).program (1 + visit.length)
    ⟨_, i, fun _ => 0, fun _ => 0⟩ mem [] = _
  rw [execute_template, run_eq_trace]
  rfl

/-- Both address intervals fit in a word and are disjoint. Either order is allowed. -/
structure Regions (pub : Fin 2 → Word w) (n capacity : ℕ) : Prop where
  fieldsFit : (pub 0).val + n ≤ 2 ^ w
  inverseFit : (pub 1).val + capacity ≤ 2 ^ w
  disjoint : (pub 0).val + n ≤ (pub 1).val ∨ (pub 1).val + capacity ≤ (pub 0).val

private theorem address_val (base : Word w) {limit : ℕ} (fit : base.val + limit ≤ 2^w)
    (i : Fin limit) : (base + Fin.ofNat (2^w) i.val).val = base.val + i.val := by
  have hi := i.isLt
  rw [Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt (show i.val < 2^w by omega), Nat.mod_eq_of_lt (by omega)]

private theorem word_succ (k : ℕ) : Fin.ofNat (2^w) k + 1 = Fin.ofNat (2^w) (k+1) := by
  apply Fin.ext
  simp [Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]

/-- At cursor `k` precisely the fields of incidences below `k` have been written. -/
private structure Prefix (base : ℕ) (field : Fin n ↪ Fin capacity)
    (initial mem : Memory w) (k : ℕ) : Prop where
  inverse : ∀ i : Fin n, i.val < k → mem (base + (field i).val) = Fin.ofNat _ i.val
  frame : ∀ addr, (∀ i : Fin n, i.val < k → addr ≠ base + (field i).val) → mem addr = initial addr

private theorem prefix_step {pub : Fin 2 → Word w} (regions : Regions pub n capacity)
    (field : Fin n ↪ Fin capacity) {initial mem : Memory w} (i : Fin n)
    (stored : ∀ j : Fin n, initial ((pub 0).val + j.val) = Fin.ofNat _ (field j).val)
    (prior : Prefix (pub 1).val field initial mem i.val) :
    let idx := Fin.ofNat (2^w) i.val
    let v := Fin.ofNat (2^w) (field i).val
    mem (pub 0 + idx).val = v ∧
      Prefix (pub 1).val field initial (after mem (events pub idx v)) (i.val+1) := by
  intro idx v
  have ha := address_val (pub 0) regions.fieldsFit i
  have hd : (pub 1 + v).val = (pub 1).val + (field i).val :=
    address_val (pub 1) regions.inverseFit (field i)
  have hm : after mem (events pub idx v) = writeMemory mem (pub 1 + v) idx := rfl
  refine ⟨?_, ?_⟩
  · rw [ha, prior.frame, stored]
    intro j _
    have hi := i.isLt
    have hj := (field j).isLt
    rcases regions.disjoint with h | h <;> omega
  · rw [hm]
    constructor
    · intro j hj
      by_cases he : j = i
      · subst j; rw [writeMemory, hd, ite_eq_left rfl]
      · have hne : (field j).val ≠ (field i).val := fun h => he (field.injective (Fin.ext h))
        have hv : j.val ≠ i.val := fun h => he (Fin.ext h)
        simpa only [writeMemory, hd, Nat.add_left_cancel_iff, ite_eq_right hne] using prior.inverse j (by omega)
    · intro addr h
      have hhead := h i (Nat.lt_succ_self _)
      simpa only [writeMemory, hd, ite_eq_right hhead] using prior.frame addr (fun j hj => h j (by omega))

private theorem run_from {pub : Fin 2 → Word w} (regions : Regions pub n capacity)
    (field : Fin n ↪ Fin capacity) {initial : Memory w}
    (stored : ∀ i : Fin n, initial ((pub 0).val + i.val) = Fin.ofNat _ (field i).val)
    (k steps : ℕ) (mem : Memory w) (prior : Prefix (pub 1).val field initial mem k)
    (bound : k + steps ≤ n) :
    let M := (template visit 0).instantiate w pub
    let state := some (Fin.ofNat (2^w) k)
    ∃ rs, runSegment M.program 10 state mem (List.replicate steps []) = some rs ∧
      endState state rs = some (Fin.ofNat _ (k+steps)) ∧
      Prefix (pub 1).val field initial (after mem (eventLog rs)) (k+steps) ∧
      rs.length = steps ∧ (∀ r ∈ rs, r.events.length = 9 ∧ r.probes = 2) ∧
      RAMBuckets.cost Report.probes rs = 3 * steps := by
  induction steps generalizing k mem with
  | zero => exact ⟨[], rfl, rfl, prior, rfl, by simp, rfl⟩
  | succ steps ih =>
    let i : Fin n := ⟨k, by omega⟩
    let idx := Fin.ofNat (2^w) k
    let v := Fin.ofNat (2^w) (field i).val
    let es := events pub idx v
    let r : Report w := ⟨es, some (idx+1)⟩
    obtain ⟨hread, hnext⟩ := prefix_step regions field i stored prior
    obtain ⟨rs, hrun, hstate, hmem, hlen, hwork, hcost⟩ :=
      ih (k+1) (after mem es) hnext (by omega)
    have hstart : idx + 1 = Fin.ofNat _ (k+1) := word_succ k
    have harr : k + 1 + steps = k + (steps + 1) := by omega
    refine ⟨r :: rs, ?_, ?_, ?_, by simp [hlen], ?_, ?_⟩
    · rw [List.replicate_succ, runSegment, visit_native, hread]
      simpa only [hstart, Option.map_some, idx, v, r, es] using
        congrArg (Option.map (r :: ·)) hrun
    · change endState (some (idx+1)) rs = _
      rwa [hstart, ← harr]
    · change Prefix _ field initial ((es ++ eventLog rs).foldl update mem) _
      rw [List.foldl_append, ← harr]
      exact hmem
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | h
      · exact ⟨rfl, rfl⟩
      · exact hwork t h
    · rw [RAMBuckets.cost, show r.probes = 2 from rfl, hcost, Nat.mul_succ]
      omega

/-- The complete scatter pass constructs the inverse at every occupied endpoint
field, returns the end cursor, and preserves all other cells. It spends exactly
three calls-plus-probes units per incidence, with ten instructions of fuel per call. -/
theorem run {pub : Fin 2 → Word w} (regions : Regions pub n capacity)
    (field : Fin n ↪ Fin capacity) (mem : Memory w)
    (stored : ∀ i : Fin n, mem ((pub 0).val + i.val) = Fin.ofNat _ (field i).val) :
    let M := (template visit 0).instantiate w pub
    ∃ rs, runSegment M.program 10 (some 0) mem (List.replicate n []) = some rs ∧
      endState (some 0) rs = some (Fin.ofNat (2^w) n) ∧
      (∀ i : Fin n, after mem (eventLog rs) ((pub 1).val + (field i).val) = Fin.ofNat _ i.val) ∧
      (∀ addr, (∀ i : Fin n, addr ≠ (pub 1).val + (field i).val) →
        after mem (eventLog rs) addr = mem addr) ∧
      rs.length = n ∧ (∀ r ∈ rs, r.events.length = 9 ∧ r.probes = 2) ∧
      RAMBuckets.cost Report.probes rs = 3 * n := by
  have h0 : Prefix (pub 1).val field mem mem 0 := ⟨by simp, fun _ _ => rfl⟩
  obtain ⟨rs, hrun, hstate, hmem, hlen, hwork, hcost⟩ := run_from regions field stored 0 n mem h0 (by simp)
  rw [Nat.zero_add] at hstate hmem
  exact ⟨rs, hrun, hstate, fun i => hmem.inverse i i.isLt,
    fun addr h => hmem.frame addr (fun i _ => h i), hlen, hwork, hcost⟩

end CompressorRecords.SlotScatter

end VPVNP
end Computability
end OAI
