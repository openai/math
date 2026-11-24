import OAI.Computability.VPVNP.LiveHeaderWidths
import OAI.Computability.VPVNP.PrimedStackRAMNodeTable
import OAI.Computability.VPVNP.PrimedInputRAMOnce
import OAI.Computability.VPVNP.RAMRecords

/-!
# Native word code for the five first-half cut widths

Each output word uses two reads from the index-scan scratch and one
write. Word division computes the two indicator bits: `1 / count` for
a power of two and `high / high` for a group other than the first.
The RAM uses natural division with zero quotient on a zero divisor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderWidths

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM

/-- Public words containing the two geometric parameters and three addresses. -/
structure Parameters where
  /-- The public operand index supplying the cut-schedule height. -/
  height : Fin 16
  /-- The public operand index supplying the basic block width that scales the computed cut
  length. -/
  delta : Fin 16
  /-- The public operand index for the cell containing the highest set position in the group
  index. -/
  highestAddress : Fin 16
  /-- The public operand index for the group index's population-count cell. -/
  populationAddress : Fin 16
  /-- The public operand index for the destination of the computed cut width. -/
  outputAddress : Fin 16

namespace WidthCode

variable {w : ℕ}

private abbrev Pub := Fin 16
private abbrev Code := Flow 48 16
private abbrev Reg := Fin 48

/-- Load the two small summary words and compute the two unshifted block
counts. The live group index itself is distributed over header bits. -/
def setup (p : Parameters) : Code :=
  straight (.constant 1 1) [
    .publicWord 2 p.height, .publicWord 3 p.delta, .publicWord 4 p.highestAddress,
    .publicWord 5 p.populationAddress, .publicWord 6 p.outputAddress, .read 7 4, .read 8 5,
    .binary .div 9 1 8, .binary .sub 10 2 7, .binary .sub 11 10 1, .binary .div 12 7 7]

/-- Place the appropriate block count in register 13. -/
def select : Slot → Code
  | .liveLeft => straight (.binary .add 13 10 9) [.binary .mul 13 13 12]
  | .liveRight => .line (.copy 13 10)
  | .primedLeft => straight (.binary .add 13 11 9) [.binary .mul 13 13 12]
  | .primedMiddle => .line (.binary .add 13 11 9)
  | .primedRight => .line (.copy 13 11)

/-- Multiply the selected block count by the basic block width and write the resulting cut
length. -/
def commit : Code := straight (.binary .mul 14 13 3) [.write 6 14]

/-- Load the scanned index summary, compute the requested live or primed block count, and
publish its width. -/
def block (p : Parameters) (s : Slot) : Code := .seq (setup p) (.seq (select s) commit)

/-- The physical instruction and public-field table is independent of word width. -/
def table (p : Parameters) (s : Slot) := (block p s).template none

private def setupEvents (pub : Pub → Word w) (p : Parameters) (m : Memory w) : List (Event w) :=
  List.replicate 6 .tick ++ [.read (pub p.highestAddress) (m (pub p.highestAddress).val),
    .read (pub p.populationAddress) (m (pub p.populationAddress).val)] ++ List.replicate 4 .tick

/-- Exact external probes and arithmetic ticks, including the final write. -/
def events (pub : Pub → Word w) (p : Parameters) (m : Memory w) (s : Slot) (v : Word w) :
    List (Event w) :=
  setupEvents pub p m ++ (List.replicate (select s).length .tick ++ [.tick,.write (pub p.outputAddress) v])

theorem event_cost (pub : Pub → Word w) (p : Parameters) (m : Memory w) (s : Slot) (v : Word w) :
    countProbes (events pub p m s v) = 3 ∧ choiceBits (events pub p m s v) = [] ∧
    (events pub p m s v).length ≤ 16 := by
  cases s <;> exact ⟨rfl,rfl,by first | exact Nat.le_refl 16 | exact Nat.le_succ 15⟩

private def wordOne (w : ℕ) : Word w := Fin.ofNat _ 1

private def loaded (pub : Pub → Word w) (p : Parameters) (m : Memory w) (rs : Regs w 48) : Regs w 48 :=
  let k := m (pub p.highestAddress).val
  let c := m (pub p.populationAddress).val
  let b := BinaryOp.sub.eval (pub p.height) k
  let vals : List (Reg × Word w) :=
    [(1,wordOne w),(2,pub p.height),(3,pub p.delta),(4,pub p.highestAddress),
      (5,pub p.populationAddress),(6,pub p.outputAddress),(7,k),(8,c),
      (9,BinaryOp.div.eval (wordOne w) c),(10,b),(11,BinaryOp.sub.eval b (wordOne w)),
      (12,BinaryOp.div.eval k k)]
  vals.foldl (fun a j => Function.update a j.1 j.2) rs

private theorem setup_exec (pub : Pub → Word w) (p : Parameters) (state : Word w) (m : Memory w)
    (rs : Regs w 48) : Flow.Exec pub state (setup p) rs m (setupEvents pub p m) (loaded pub p m rs) m :=
  (Flow.once_sound pub state false (setup p) rs m rfl).1

private def chosen (rs : Regs w 48) : Slot → Word w
  | .liveLeft => (rs 10 + rs 9) * rs 12
  | .liveRight => rs 10
  | .primedLeft => (rs 11 + rs 9) * rs 12
  | .primedMiddle => rs 11 + rs 9
  | .primedRight => rs 11

private theorem select_exec (pub : Pub → Word w) (state : Word w) (m : Memory w)
    (rs : Regs w 48) (s : Slot) : ∃ out,
    Flow.Exec pub state (select s) rs m (List.replicate (select s).length .tick) out m ∧
    out 13 = chosen rs s ∧ out 3 = rs 3 ∧ out 6 = rs 6 := by
  let initial : Regs w 48 := match s with
    | .liveLeft => Function.update rs 13 (rs 10 + rs 9)
    | .primedLeft => Function.update rs 13 (rs 11 + rs 9)
    | _ => rs
  let out := Function.update initial (13 : Reg) (chosen rs s)
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · apply (Flow.once_sound pub state false _ rs m ?_).1
    cases s <;> rfl
  all_goals cases s <;> rfl

private theorem commit_exec (pub : Pub → Word w) (state : Word w) (m : Memory w)
    (rs : Regs w 48) :
    let v := rs 13 * rs 3
    Flow.Exec pub state commit rs m [.tick,.write (rs 6) v] (Function.update rs 14 v)
      (writeMemory m (rs 6) v) :=
  (Flow.once_sound pub state false commit rs m rfl).1

/-- On groups outside the first half, unused primed lengths are still
computed by the same straight-line table. Its only write is its output. -/
theorem unconditional_exec (pub : Pub → Word w) (p : Parameters) (state : Word w)
    (m : Memory w) (rs : Regs w 48) (s : Slot) :
    ∃ v out, Flow.Exec pub state (block p s) rs m (events pub p m s v) out
      (writeMemory m (pub p.outputAddress) v) := by
  let a := loaded pub p m rs
  obtain ⟨b,hs,_,_,h₆⟩ := select_exec pub state m a s
  have hb : b 6 = pub p.outputAddress := h₆
  have commitRun := commit_exec pub state m b
  dsimp only at commitRun
  rw [hb] at commitRun
  exact ⟨_,_,(setup_exec pub p state m rs).seq (hs.seq commitRun)⟩

private theorem div_val (x y : Word w) : (BinaryOp.div.eval x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)

private theorem chosen_val (pub : Pub → Word w) (p : Parameters) (m : Memory w) (rs : Regs w 48)
    (s : Slot) (H k c : ℕ) (hH : 0 < H) (hk : k ≤ H)
    (hs : s = .liveLeft ∨ s = .liveRight ∨ k < H)
    (hh : (pub p.height).val = H) (hk' : (m (pub p.highestAddress).val).val = k)
    (hc' : (m (pub p.populationAddress).val).val = c) :
    (chosen (loaded pub p m rs) s).val = blocks H k c s := by
  let a := loaded pub p m rs
  have ht := (pub p.height).isLt
  rw [hh] at ht
  have ho : (wordOne w).val = 1 := Nat.mod_eq_of_lt (by omega)
  have hk7 : (a 7).val = k := hk'
  have hc8 : (a 8).val = c := hc'
  have he : (a 9).val = (if c = 1 then 1 else 0) := by
    change (BinaryOp.div.eval (wordOne w) (a 8)).val = _
    rw [div_val, ho, hc8]
    split_ifs with he
    · simp [he]
    · rcases Nat.eq_zero_or_pos c with hz | hp
      · simp [hz]
      · exact Nat.div_eq_of_lt (by omega)
  have hb : (a 10).val = H-k := by
    change (pub p.height - a 7).val = _
    rw [Fin.sub_val_of_le (by change (a 7).val ≤ _; omega), hh, hk7]
  have hd (hshift : k < H) : (a 11).val = H-k-1 := by
    change (a 10 - wordOne w).val = _
    rw [Fin.sub_val_of_le (by change (wordOne w).val ≤ _; omega), hb, ho]
  have hm : (a 12).val = if k = 0 then 0 else 1 := by
    change (BinaryOp.div.eval (a 7) (a 7)).val = _
    rw [div_val, hk7]
    split_ifs with hz
    · simp [hz]
    · exact Nat.div_self (by omega)
  have he1 : (a 9).val ≤ 1 := by rw [he]; split_ifs <;> omega
  have hdadd (hshift : k < H) : (a 11 + a 9).val = (a 11).val + (a 9).val :=
    Fin.val_add_eq_of_add_lt (by have := hd hshift; omega)
  have hzero (x : Word w) (hz : k = 0) : (x * a 12).val = 0 := by
    rw [Fin.val_mul, hm, ite_eq_left hz, Nat.mul_zero, Nat.zero_mod]
  have hkeep (x : Word w) (hz : k ≠ 0) : (x * a 12).val = x.val := by
    rw [Fin.val_mul, hm, ite_eq_right hz, Nat.mul_one, Nat.mod_eq_of_lt x.isLt]
  change (chosen a s).val = _
  cases s with
  | liveLeft =>
    by_cases hz : k = 0
    · exact (hzero _ hz).trans (by simp [blocks,hz])
    · rw [chosen, hkeep _ hz, Fin.val_add_eq_of_add_lt (by omega), hb, he, blocks, ite_eq_right hz]
  | liveRight => exact hb
  | primedLeft =>
    have hs' : k < H := by simpa using hs
    by_cases hz : k = 0
    · exact (hzero _ hz).trans (by simp [blocks,hz])
    · rw [chosen, hkeep _ hz, hdadd hs', hd hs', he, blocks, ite_eq_right hz]
  | primedMiddle =>
    have hs' : k < H := by simpa using hs
    exact (hdadd hs').trans (by rw [hd hs', he, blocks])
  | primedRight => exact hd (by simpa using hs)

/-- Execution from arbitrary registers computes the true paper width. The
height, block size, highest set bit and population count are read at runtime.
The bound on the output word follows from the largest possible cut length. -/
theorem needed_exec (pub : Pub → Word w) (p : Parameters) (state : Word w) (m : Memory w)
    (rs : Regs w 48) (s : Slot) (h Δ i c : ℕ) (hi : 0 < i) (hend : i ≤ 2^(h+1)) (hneed : Needed h i s)
    (hc : c = 1 ↔ i = 2 ^ Nat.log 2 i)
    (hh : (pub p.height).val = h+1) (hΔ : (pub p.delta).val = Δ)
    (hk' : (m (pub p.highestAddress).val).val = Nat.log 2 i)
    (hc' : (m (pub p.populationAddress).val).val = c) (hfit : (h+1)*Δ < 2^w) :
    let width := CutSchedule.width (h+1) Δ (index i s)
    let v : Word w := Fin.ofNat _ width
    ∃ out, Flow.Exec pub state (block p s) rs m (events pub p m s v) out
      (writeMemory m (pub p.outputAddress) v) ∧ v.val = width := by
  let a := loaded pub p m rs
  obtain ⟨b,hs,h13,h3,h6⟩ := select_exec pub state m a s
  have hk : Nat.log 2 i ≤ h+1 := by
    simpa [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hend
  have hs' : s = .liveLeft ∨ s = .liveRight ∨ Nat.log 2 i < h+1 := by
    rcases hneed with hf | he | he
    · have hlog : Nat.log 2 i ≤ h := by
        simpa [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hf
      exact Or.inr (Or.inr (by omega))
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  have hb := chosen_val pub p m rs s (h+1) (Nat.log 2 i) c (by omega) hk hs' hh hk' hc'
  have hw := needed_width h Δ i c s hi hend hc hneed
  have hf := (Nat.mul_le_mul_right Δ (blocks_le (h+1) (Nat.log 2 i) c s (by omega))).trans_lt hfit
  have h3' : b 3 = pub p.delta := h3
  have h6' : b 6 = pub p.outputAddress := h6
  have hv : (b 13 * b 3).val = CutSchedule.width (h+1) Δ (index i s) := by
    rw [Fin.val_mul, h13, h3', hΔ, hb, Nat.mod_eq_of_lt hf, hw]
  let v : Word w := Fin.ofNat _ (CutSchedule.width (h+1) Δ (index i s))
  have hv' : v.val = CutSchedule.width (h+1) Δ (index i s) :=
    Nat.mod_eq_of_lt (hw ▸ hf)
  have he : b 13 * b 3 = v := Fin.ext (hv.trans hv'.symm)
  have hwrites := commit_exec pub state m b
  dsimp only at hwrites
  rw [he, h6'] at hwrites
  exact ⟨_,(setup_exec pub p state m rs).seq (hs.seq hwrites),hv'⟩

/-- First-half groups may request any of the five lengths. -/
theorem block_exec (pub : Pub → Word w) (p : Parameters) (state : Word w) (m : Memory w)
    (rs : Regs w 48) (s : Slot) (h Δ i c : ℕ) (hi : 0 < i) (hle : i ≤ 2^h)
    (hc : c = 1 ↔ i = 2 ^ Nat.log 2 i)
    (hh : (pub p.height).val = h+1) (hΔ : (pub p.delta).val = Δ)
    (hk' : (m (pub p.highestAddress).val).val = Nat.log 2 i)
    (hc' : (m (pub p.populationAddress).val).val = c) (hfit : (h+1)*Δ < 2^w) :
    let width := CutSchedule.width (h+1) Δ (index i s)
    let v : Word w := Fin.ofNat _ width
    ∃ out, Flow.Exec pub state (block p s) rs m (events pub p m s v) out
      (writeMemory m (pub p.outputAddress) v) ∧ v.val = width :=
  needed_exec pub p state m rs s h Δ i c hi (hle.trans (Nat.pow_le_pow_right (by decide) (by omega)))
    (Or.inl hle) hc hh hΔ hk' hc' hfit

end WidthCode
end LiveHeaderWidths

end VPVNP
end Computability
end OAI
