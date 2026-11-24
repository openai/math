import OAI.Computability.VPVNP.CompressorSliceRAM

/-!
# Indexed RAM visits for the interval scan

The persistent word enumerates the Cartesian product in source-major order.
One call reads both fields from the external start and width arrays. It stores
the two offsets and length of a nonempty copy in the pair's three-word slot.
For an empty copy it writes zero in the length cell, even when the slot
initially contains arbitrary words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SliceRAM.IndexedPair

open BurstRAM BurstRAM.PrivateRAM Compression.PackingData

variable {w : ℕ}

/-- Public words contain the new field count, four array bases in source/target
and start/width order, and the base of the three-word output slots. -/
def table : Template 41 15 6 where
  literalWidth := 2
  entry := 17
  code pc := match pc.val with
    | 0 => .binary .add 4 0 1 1
    | 1 => .binary .add 5 2 3 2
    | 2 => .jumpLt 0 2 3 4
    | 3 => .copy 6 2 5
    | 4 => .copy 6 0 5
    | 5 => .jumpLt 4 5 6 7
    | 6 => .copy 7 4 8
    | 7 => .copy 7 5 8
    | 8 => .jumpLt 6 7 9 16
    | 9 => .binary .sub 8 6 0 10
    | 10 => .binary .sub 9 6 2 11
    | 11 => .binary .sub 10 7 6 12
    | 12 => .writeExternal 11 8 13
    | 13 => .writeExternal 12 9 14
    | 14 => .writeExternal 13 10 15
    | 15 => .returnState 14
    | 16 => .constant 10 0 14
    | 17 => .stateWord 14 18
    | 18 => .publicWord 4 0 19
    | 19 => .binary .div 5 14 4 20
    | 20 => .binary .mod 6 14 4 21
    | 21 => .publicWord 7 1 22
    | 22 => .binary .add 7 7 5 23
    | 23 => .readExternal 0 7 24
    | 24 => .publicWord 7 2 25
    | 25 => .binary .add 7 7 5 26
    | 26 => .readExternal 1 7 27
    | 27 => .publicWord 7 3 28
    | 28 => .binary .add 7 7 6 29
    | 29 => .readExternal 2 7 30
    | 30 => .publicWord 7 4 31
    | 31 => .binary .add 7 7 6 32
    | 32 => .readExternal 3 7 33
    | 33 => .constant 8 3 34
    | 34 => .binary .mul 8 8 14 35
    | 35 => .publicWord 11 5 36
    | 36 => .binary .add 11 11 8 37
    | 37 => .constant 8 1 38
    | 38 => .binary .add 12 11 8 39
    | 39 => .binary .add 13 12 8 40
    | _ => .binary .add 14 14 8 0

/-- Source field of a pair ordinal, obtained by division by the number of target fields. -/
def oldIndex (p : Fin 6 → Word w) (k : Word w) : Word w := BinaryOp.div.eval k (p 0)

/-- Target field of a pair ordinal, obtained by reduction modulo the number of target fields. -/
def newIndex (p : Fin 6 → Word w) (k : Word w) : Word w := BinaryOp.mod.eval k (p 0)

/-- First word of the slot assigned to this ordered pair. -/
def base (p : Fin 6 → Word w) (k : Word w) : Word w := p 5 + 3 * k

theorem oldIndex_val (p : Fin 6 → Word w) (k : Word w) :
    (oldIndex p k).val = k.val / (p 0).val :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self ..) k.isLt)

theorem newIndex_val (p : Fin 6 → Word w) (k : Word w) :
    (newIndex p k).val = k.val % (p 0).val :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le ..) k.isLt)

theorem base_val (p : Fin 6 → Word w) (k : Word w) (ha : (p 5).val + 3*k.val < 2^w) :
    (base p k).val = (p 5).val + 3*k.val := by
  have hmul : ((3 : Word w) * k).val = 3*k.val := by
    change ((3 % (2^w)) * k.val) % (2^w) = _
    rw [Nat.mod_mul_mod, Nat.mod_eq_of_lt (by omega)]
  rw [base, Fin.val_add, hmul, Nat.mod_eq_of_lt ha]

/-- Compute the interval copy for the selected pair using both start and width arrays in
memory. -/
def slice (p : Fin 6 → Word w) (k : Word w) (m : Memory w) : CopySlice :=
  let i := oldIndex p k
  let j := newIndex p k
  copySlice (m (p 1 + i).val).val (m (p 2 + i).val).val
    (m (p 3 + j).val).val (m (p 4 + j).val).val

private def reads (p : Fin 6 → Word w) (k : Word w) (m : Memory w) : List (Event w) :=
  let a := p 1 + oldIndex p k
  let b := p 2 + oldIndex p k
  let c := p 3 + newIndex p k
  let d := p 4 + newIndex p k
  [.tick, .tick, .tick, .tick, .tick, .tick, .read a (m a.val), .tick, .tick,
    .read b (m b.val), .tick, .tick, .read c (m c.val), .tick, .tick,
    .read d (m d.val)] ++ List.replicate 8 .tick

private def stores (a : Word w) (s : CopySlice) : List (Event w) :=
  if s.length = 0 then List.replicate 8 .tick ++ [.write (a+1+1) 0] else
    List.replicate 10 .tick ++ [.write a (Fin.ofNat _ s.sourceOffset),
      .write (a+1) (Fin.ofNat _ s.targetOffset), .write (a+1+1) (Fin.ofNat _ s.length)]

/-- Full trace of an indexed visit, including the four array reads. -/
def report (p : Fin 6 → Word w) (k : Word w) (m : Memory w) (s : CopySlice) : Report w :=
  ⟨reads p k m ++ stores (base p k) s, some (k+1)⟩

theorem report_result (p : Fin 6 → Word w) (k : Word w) (m : Memory w) (s : CopySlice) :
    (report p k m s).result = some (k+1) := rfl

theorem report_cost (p : Fin 6 → Word w) (k : Word w) (m : Memory w) (s : CopySlice) :
    (report p k m s).probes = (if s.length = 0 then 5 else 7) ∧
      (report p k m s).events.length + 1 = (if s.length = 0 then 34 else 38) := by
  by_cases h : s.length = 0 <;> simp only [report, stores, h, ↓reduceIte] <;> exact ⟨rfl, rfl⟩

theorem report_after (p : Fin 6 → Word w) (k : Word w) (m : Memory w) (s : CopySlice) :
    let a := base p k
    after m (report p k m s).events = if s.length = 0 then writeMemory m (a+1+1) 0 else
      writeMemory (writeMemory (writeMemory m a (Fin.ofNat _ s.sourceOffset))
        (a+1) (Fin.ofNat _ s.targetOffset)) (a+1+1) (Fin.ofNat _ s.length) := by
  by_cases h : s.length = 0 <;> simp only [report, stores, h, ↓reduceIte] <;> rfl

private def registers (p : Fin 6 → Word w) (k : Word w) (m : Memory w) : Fin 15 → Word w :=
  let i := oldIndex p k
  let j := newIndex p k
  let a := base p k
  ![m (p 1+i).val, m (p 2+i).val, m (p 3+j).val, m (p 4+j).val, p 0, i, j, p 4+j,
    1, 0, 0, a, a+1, a+1+1, k+1]

set_option maxRecDepth 4096 in
private theorem execute_reads (p : Fin 6 → Word w) (k : Word w) (m : Memory w) (fuel : ℕ) :
    let M := table.instantiate w p
    execute M.program (fuel + 24) (M.program.start k) m [] =
      (execute M.program fuel ⟨0, k, registers p k m, fun _ => 0⟩ m []).map
        (fun r => ⟨reads p k m ++ r.events, r.result⟩) := by
  simp (config := { decide := true }) [execute, Machine.program, table, Template.instantiate,
    Instr.run, Instr.resize, Config.put, BinaryOp.eval, Report.prepend, Function.comp_def,
    reads, oldIndex, newIndex]
  congr 4
  funext i
  fin_cases i <;> rfl

private def wordStores (a s t lo hi : Word w) : List (Event w) :=
  if lo < hi then List.replicate 10 .tick ++
    [.write a (lo-s), .write (a+1) (lo-t), .write (a+1+1) (hi-lo)]
  else List.replicate 8 .tick ++ [.write (a+1+1) 0]

set_option maxHeartbeats 600000 in
private theorem execute_stores (p : Fin 6 → Word w) (k : Word w) (m : Memory w)
    (rs : Fin 15 → Word w) (h₁ : rs 12 = rs 11 + 1) (h₂ : rs 13 = rs 11 + 1 + 1) :
    let M := table.instantiate w p
    let lo := if rs 0 < rs 2 then rs 2 else rs 0
    let e₁ := rs 0 + rs 1
    let e₂ := rs 2 + rs 3
    execute M.program 14 ⟨0, k, rs, fun _ => 0⟩ m [] =
      some ⟨wordStores (rs 11) (rs 0) (rs 2) lo (if e₁ < e₂ then e₁ else e₂), some (rs 14)⟩ := by
  dsimp only
  by_cases hl : rs 0 < rs 2 <;> by_cases hh : rs 0 + rs 1 < rs 2 + rs 3 <;>
    simp only [wordStores, hl, hh, ↓reduceIte]
  all_goals
    split <;> rename_i hc <;>
    simp (config := { decide := true }) [table, Template.instantiate, Machine.program,
      execute, Instr.resize, Instr.run, Config.put, BinaryOp.eval, Function.update,
      hl, hh, hc, h₁, h₂, Report.prepend]

private theorem stores_exact (a s ns t nt : Word w)
    (hs : s.val + ns.val < 2^w) (ht : t.val + nt.val < 2^w) :
    let lo := if s < t then t else s
    let hi := if s + ns < t + nt then s + ns else t + nt
    wordStores a s t lo hi = stores a (copySlice s.val ns.val t.val nt.val) := by
  intro lo hi
  have hlo : lo.val = max s.val t.val := by
    by_cases h : s < t
    · simp [lo, h, max_eq_right (Fin.le_iff_val_le_val.mp h.le)]
    · simp [lo, h, max_eq_left (Fin.le_iff_val_le_val.mp (le_of_not_gt h))]
  have hsum₁ : (s + ns).val = s.val + ns.val := Nat.mod_eq_of_lt hs
  have hsum₂ : (t + nt).val = t.val + nt.val := Nat.mod_eq_of_lt ht
  have hhi : hi.val = min (s.val + ns.val) (t.val + nt.val) := by
    rw [← hsum₁, ← hsum₂]
    by_cases h : s + ns < t + nt
    · simp [hi, h, min_eq_left (Fin.le_iff_val_le_val.mp h.le)]
    · simp [hi, h, min_eq_right (Fin.le_iff_val_le_val.mp (le_of_not_gt h))]
  have hlen : (copySlice s.val ns.val t.val nt.val).length = hi.val - lo.val := by
    simp [copySlice, hhi, hlo]
  by_cases h : lo < hi
  · have hsle : s ≤ lo := Fin.le_iff_val_le_val.mpr (hlo ▸ le_max_left ..)
    have htle : t ≤ lo := Fin.le_iff_val_le_val.mpr (hlo ▸ le_max_right ..)
    have offset (x : Word w) (hle : x ≤ lo) :
        lo - x = Fin.ofNat _ (lo.val - x.val) := by
      apply Fin.ext
      rw [Fin.sub_val_of_le hle, Fin.val_ofNat, Nat.mod_eq_of_lt (by have := lo.isLt; omega)]
    have len : hi - lo = Fin.ofNat _ (hi.val - lo.val) := by
      apply Fin.ext
      rw [Fin.sub_val_of_le h.le, Fin.val_ofNat, Nat.mod_eq_of_lt (by have := hi.isLt; omega)]
    have hn : (copySlice s.val ns.val t.val nt.val).length ≠ 0 :=
      hlen ▸ Nat.sub_ne_zero_of_lt (Fin.lt_def.mp h)
    simp only [wordStores, stores, h, hn, ↓reduceIte, offset s hsle, offset t htle, len]
    rw [hhi, hlo]
    rfl
  · simp [wordStores, stores, h, hlen, Nat.sub_eq_zero_of_le (le_of_not_gt h)]

/-- A reset call computes the interval intersection and returns the next
pair identifier. The two endpoint bounds suffice for correct word arithmetic. -/
theorem visit_native (p : Fin 6 → Word w) (k : Word w) (m : Memory w)
    (hs : (m (p 1 + oldIndex p k).val).val + (m (p 2 + oldIndex p k).val).val < 2^w)
    (ht : (m (p 3 + newIndex p k).val).val + (m (p 4 + newIndex p k).val).val < 2^w) :
    let M := table.instantiate w p
    execute M.program 38 (M.program.start k) m [] = some (report p k m (slice p k m)) := by
  dsimp only
  let r := registers p k m
  rw [execute_reads p k m 14, execute_stores p k m _ rfl rfl,
    stores_exact (r 11) (r 0) (r 1) (r 2) (r 3) hs ht]
  rfl

end CompressorRecords.SliceRAM.IndexedPair

end VPVNP
end Computability
end OAI
