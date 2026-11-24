import OAI.Computability.VPVNP.CompressorSliceRAM
import OAI.Computability.VPVNP.RAMChain

/-!
# Native prefix scans for Appendix E

A fixed table visits the external width array in increasing index order.
Its persistent word carries the index across calls. An external cell holds the
running total, so the next call can start with fresh private registers. Each
visit records the start of one field and adds its width to the total.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SliceRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Public words name the width-array base, start-array base and accumulator cell.
Register zero carries the persistent field index. -/
def prefixOps : List (Op 7 3) :=
  [.stateWord 0, .publicWord 1 0, .binary .add 1 1 0, .read 2 1,
   .publicWord 3 2, .read 4 3, .publicWord 5 1, .binary .add 5 5 0,
   .write 5 4, .binary .add 4 4 2, .write 3 4, .constant 6 1, .binary .add 0 0 6]

/-- The two read answers are obtained before either of the two writes. -/
def prefixEvents (pub : Fin 3 → Word w) (i : Word w) (mem : Memory w) : List (Event w) :=
  let a := pub 0 + i
  let total := mem (pub 2).val
  let width := mem a.val
  [.tick, .tick, .tick, .read a width, .tick, .read (pub 2) total, .tick, .tick,
   .write (pub 1 + i) total, .tick, .write (pub 2) (total + width), .tick, .tick]

/-- Replay stores the old total at the field's start and the new total in the accumulator. -/
theorem after_prefixEvents (pub : Fin 3 → Word w) (i : Word w) (mem : Memory w) :
    after mem (prefixEvents pub i mem) =
      writeMemory (writeMemory mem (pub 1 + i) (mem (pub 2).val))
        (pub 2) (mem (pub 2).val + mem (pub 0 + i).val) := rfl

/-- The actual opcode table executes one field visit in fourteen instructions. -/
theorem prefixVisit_native (pub : Fin 3 → Word w) (i : Word w) (mem : Memory w) :
    let M := (template prefixOps 0).instantiate w pub
    execute M.program 14 (M.program.start i) mem [] =
      some ⟨prefixEvents pub i mem, some (i + 1)⟩ := by
  let M := (template prefixOps 0).instantiate w pub
  change execute M.program (1 + prefixOps.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ mem [] = _
  rw [execute_template, run_eq_trace]
  simp (config := { decide := true }) [prefixOps, trace, Op.effect, BinaryOp.eval,
    Function.update, prefixEvents]
  rfl

/-- The input and output arrays fit and are disjoint. The accumulator can be
any other word address. -/
structure PrefixRegions (pub : Fin 3 → Word w) (n : ℕ) : Prop where
  widthsFit : (pub 0).val + n ≤ 2^w
  startsFit : (pub 1).val + n ≤ 2^w
  arraysApart : (pub 0).val + n ≤ (pub 1).val ∨ (pub 1).val + n ≤ (pub 0).val
  totalOutsideWidths : (pub 2).val < (pub 0).val ∨ (pub 0).val + n ≤ (pub 2).val
  totalOutsideStarts : (pub 2).val < (pub 1).val ∨ (pub 1).val + n ≤ (pub 2).val

/-- The first `k` start cells have been filled. Every other cell apart from the
accumulator retains its initial contents. -/
structure PrefixAt (pub : Fin 3 → Word w) (ws : List ℕ) (initial mem : Memory w) (k : ℕ) : Prop where
  widths : ∀ i (hi : i < ws.length), (mem ((pub 0).val + i)).val = ws[i]
  starts : ∀ i, i < k → (mem ((pub 1).val + i)).val = (ws.take i).sum
  total : (mem (pub 2).val).val = (ws.take k).sum
  outside : ∀ x, x ≠ (pub 2).val → (x < (pub 1).val ∨ (pub 1).val + k ≤ x) → mem x = initial x

private theorem prefixAt_step {pub : Fin 3 → Word w} {ws : List ℕ}
    (bounds : PrefixRegions pub ws.length) (hs : ws.sum < 2^w) {initial mem : Memory w}
    {i : Word w} (hi : i.val < ws.length) (h : PrefixAt pub ws initial mem i.val) :
    PrefixAt pub ws initial (after mem (prefixEvents pub i mem)) (i.val + 1) := by
  have hwa : (pub 0 + i).val = (pub 0).val + i.val := by
    have := bounds.widthsFit
    exact Nat.mod_eq_of_lt (by omega)
  have hsa : (pub 1 + i).val = (pub 1).val + i.val := by
    have := bounds.startsFit
    exact Nat.mod_eq_of_lt (by omega)
  rw [after_prefixEvents]
  constructor
  · intro j hj
    have := bounds.arraysApart
    have := bounds.totalOutsideWidths
    simpa [writeMemory, hsa, show (pub 0).val + j ≠ (pub 2).val by omega,
      show (pub 0).val + j ≠ (pub 1).val + i.val by omega] using h.widths j hj
  · intro j hj
    have := bounds.totalOutsideStarts
    have ht : (pub 1).val + j ≠ (pub 2).val := by omega
    by_cases he : j = i.val
    · subst j
      simpa [writeMemory, ht, hsa] using h.total
    · simpa [writeMemory, hsa, ht, he]
        using h.starts j (by omega)
  · have hsum := congrArg List.sum (List.take_append_drop (i.val + 1) ws)
    simp only [List.sum_append] at hsum
    have hval := h.widths i.val hi
    simp only [writeMemory, ↓reduceIte, Fin.val_add, h.total, hwa, hval]
    rw [← List.sum_take_succ _ _ hi, Nat.mod_eq_of_lt (by omega)]
  · intro x hne hx
    simpa [writeMemory, hne, hsa, show x ≠ (pub 1).val + i.val by omega]
      using h.outside x hne (by omega)

/-- An uninterrupted segment may start at any completed prefix. All probes
read or write exactly the two cells specified for their current visit. -/
theorem prefixSegment_run {pub : Fin 3 → Word w} {ws : List ℕ} (bounds : PrefixRegions pub ws.length)
    (hl : ws.length < 2^w) (hs : ws.sum < 2^w) {initial mem : Memory w} {k : ℕ}
    (h : PrefixAt pub ws initial mem k) (steps : ℕ) (hb : k + steps ≤ ws.length) :
    let M := (template prefixOps 0).instantiate w pub
    let idx := fun n => Fin.ofNat (2^w) n
    ∃ rs, runSegment M.program 14 (some (idx k)) mem (List.replicate steps []) = some rs ∧
      PrefixAt pub ws initial (after mem (eventLog rs)) (k + steps) ∧
      endState (some (idx k)) rs = some (idx (k + steps)) ∧ rs.length = steps ∧
      ∀ r ∈ rs, r.probes = 4 ∧ r.events.length + 1 = 14 := by
  let idx := fun n => Fin.ofNat (2^w) n
  let M := (template prefixOps 0).instantiate w pub
  induction steps generalizing k mem with
  | zero => exact ⟨[], rfl, h, rfl, rfl, by simp⟩
  | succ steps ih =>
    have hi : (idx k).val = k := Nat.mod_eq_of_lt (by omega)
    have hnext : idx k + 1 = idx (k + 1) := by
      apply Fin.ext
      rw [Fin.val_add, hi, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^w by omega)]
      rfl
    let r : Report w := ⟨prefixEvents pub (idx k) mem, some (idx k + 1)⟩
    have hp := prefixAt_step bounds hs (i := idx k) (by omega) (hi ▸ h)
    rw [hi] at hp
    obtain ⟨rs,hr,hp',he,hℓ,hcost⟩ := ih hp (by omega)
    refine ⟨r :: rs, ?_, ?_, ?_, by simp [hℓ], ?_⟩
    · change runSegment M.program 14 (some (idx k)) mem (List.replicate (steps + 1) []) = _
      rw [List.replicate_succ, runSegment, prefixVisit_native]
      simp only [hnext, r]
      rw [show runSegment M.program 14 (some (idx (k+1))) (after mem (prefixEvents pub (idx k) mem))
        (List.replicate steps []) = some rs from hr]
      rfl
    · have hm : after mem (eventLog (r :: rs)) = after (after mem r.events) (eventLog rs) := by
        change List.foldl update mem (r.events ++ eventLog rs) = _
        rw [List.foldl_append]
        rfl
      rw [hm, show k + (steps + 1) = k + 1 + steps by omega]
      exact hp'
    · change endState (some (idx k + 1)) rs = _
      rw [hnext, he, show k + (steps + 1) = k + 1 + steps by omega]
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨rfl,rfl⟩
      · exact hcost _ ht

/-- Starting from a zero accumulator, the native pass computes all field
starts, preserves the widths and returns the field count. Its final accumulator
contains the full width sum, including when the list is empty. -/
theorem prefixPass_run {pub : Fin 3 → Word w} {ws : List ℕ} (bounds : PrefixRegions pub ws.length)
    (hl : ws.length < 2^w) (hs : ws.sum < 2^w) {mem : Memory w}
    (hw : ∀ i (hi : i < ws.length), (mem ((pub 0).val + i)).val = ws[i])
    (hz : (mem (pub 2).val).val = 0) :
    let M := (template prefixOps 0).instantiate w pub
    ∃ rs, runSegment M.program 14 (some 0) mem (List.replicate ws.length []) = some rs ∧
      PrefixAt pub ws mem (after mem (eventLog rs)) ws.length ∧
      endState (some 0) rs = some (Fin.ofNat (2^w) ws.length) ∧ rs.length = ws.length ∧
      ∀ r ∈ rs, r.probes = 4 ∧ r.events.length + 1 = 14 := by
  have h : PrefixAt pub ws mem mem 0 :=
    ⟨hw, fun i hi => by omega, by simpa using hz, fun _ _ _ => rfl⟩
  simpa using prefixSegment_run bounds hl hs h ws.length (by omega)

end CompressorRecords.SliceRAM

end VPVNP
end Computability
end OAI
