import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PrimedInputRAMOnce
import OAI.Computability.VPVNP.RAMTapeWord
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-!
# Gathering a live configuration word from contiguous bit cells

One burst call reads the `w` bits of one cut word, least significant first.
Each source cell must be zero or one. The running sum and binary place are
machine words; doubling the place at the final bit may wrap. The completed
word is written once, then the next call processes the next word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveConfigGather

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

/-- A native configuration-gather code block with 32 registers and four public operands. -/
abbrev Block := Flow 32 4
/-- The four public operand indices of the configuration-gather worker. -/
abbrev Pub := Fin 4
/-- The 32 register indices available to the configuration-gather worker. -/
abbrev Reg := Fin 32
variable {w : ℕ}

private def block (first : Op 32 4) (rest : List (Op 32 4)) : Block := straight first rest

/-- The public parameters are source bit base, destination word base, word
width and word count. A call's persistent word is its destination index. -/
def load : Block := block (.constant 0 0)
  [.constant 1 1, .constant 2 2, .publicWord 3 0, .publicWord 4 1, .publicWord 5 2,
   .publicWord 30 3, .stateWord 7, .guardLt 7 30, .binary .mul 8 7 5, .binary .add 8 3 8,
   .binary .add 9 4 7, .constant 10 0, .constant 11 0, .constant 12 1]

/-- Read one source cell, verify that it holds a bit, add its place value to the word, and
advance the bit index and place. -/
def readBit : Block := block (.binary .add 13 8 10)
  [.read 14 13, .guardLt 14 2, .binary .mul 15 14 12, .binary .add 11 11 15,
   .binary .add 12 12 12, .binary .add 10 10 1]

/-- Repeat the bit-reading block until the current word's specified width has been processed. -/
def scan : Block := .whileLt 10 5 readBit

/-- Write the gathered word at the destination and prepare the next word's cursor. -/
def save : Block := block (.write 9 11) [.binary .add 29 7 1]

/-- The complete word-gathering flow, from loading operands through the bit scan to the
destination write. -/
def body : Block := .seq load (.seq scan save)

/-- The native burst-call template for gathering one word, using the next cursor and word-count
registers to control its return. -/
def table := PrimedCounter.Call.template body 29 30

private def put (r : Regs w 32) (l : List (Reg × Word w)) : Regs w 32 :=
  l.foldl (fun s x => Function.update s x.1 x.2) r

/-- The register bank at scan entry, with source and destination addresses for the current
word, a zero accumulator, and unit place. -/
def loaded (pub : Pub → Word w) (state : Word w) (r : Regs w 32) : Regs w 32 :=
  put r [(0,0), (1,1), (2,2), (3,pub 0), (4,pub 1), (5,pub 2), (30,pub 3),
    (7,state), (8,pub 0 + state * pub 2), (9,pub 1 + state),
    (10,0), (11,0), (12,1)]

private theorem load_exec (pub : Pub → Word w) (state : Word w) (r : Regs w 32) (m : Memory w)
    (h : state < pub 3) : Flow.Exec pub state load r m (List.replicate 15 .tick) (loaded pub state r) m := by
  apply (Flow.once_sound pub state false load r m ?_).1
  simp (config := { decide := true }) [load, block, straight, Flow.once, Op.effect, BinaryOp.eval, pure, bind, h]
  rfl

/-- The register bank after consuming one source bit, including the updated sum, doubled place,
and incremented bit index. -/
def advanced (r : Regs w 32) (v : Word w) : Regs w 32 :=
  put r [(13,r 8 + r 10), (14,v), (15,v * r 12), (11,r 11 + v * r 12),
    (12,r 12 + r 12), (10,r 10 + r 1)]

private def bitEvents (addr v : Word w) : List (Event w) :=
  [.tick, .read addr v, .tick, .tick, .tick, .tick, .tick]

private theorem bit_exec (pub : Pub → Word w) (state : Word w) (r : Regs w 32) (m : Memory w)
    (v : Word w) (hread : m (r 8 + r 10).val = v) (hval : v < r 2) :
    Flow.Exec pub state readBit r m (bitEvents (r 8 + r 10) v) (advanced r v) m := by
  apply (Flow.once_sound pub state false readBit r m ?_).1
  simp (config := { decide := true }) [readBit, block, straight, Flow.once, Op.effect, BinaryOp.eval, pure, bind, hread, hval]
  constructor <;> rfl

/-- The register bank after incorporating the supplied bits in little-endian order. -/
def folded (r : Regs w 32) (bs : List Bool) : Regs w 32 :=
  bs.foldl (fun s b => advanced s (b.toNat : Word w)) r

/-- The loop-test, source-read, and arithmetic events for scanning the given sequence of
configuration bits. -/
def scanEvents (r : Regs w 32) : List Bool → List (Event w)
  | [] => [.tick]
  | b :: bs => .tick :: (bitEvents (r 8 + r 10) (b.toNat : Word w) ++
      scanEvents (advanced r (b.toNat : Word w)) bs)

theorem folded_acc (r : Regs w 32) (bs : List Bool) :
    folded r bs 11 = r 11 + r 12 * (TapeWord.value bs : Word w) := by
  induction bs generalizing r with
  | nil => simp [folded, TapeWord.value]
  | cons b bs ih =>
    change folded (advanced r _) bs 11 = _
    rw [ih]
    change r 11 + (b.toNat : Word w) * r 12 + (r 12 + r 12) * (TapeWord.value bs : Word w) = _
    simp only [TapeWord.value, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring

private theorem folded_keep (r : Regs w 32) (bs : List Bool) (i : Reg) (hi : i.val < 10 ∨ 15 < i.val) :
    folded r bs i = r i := by
  induction bs generalizing r with
  | nil => rfl
  | cons b bs ih =>
    change folded (advanced r _) bs i = _
    rw [ih]
    simp only [advanced, put, List.foldl_cons, List.foldl_nil]
    repeat rw [Function.update_of_ne (by intro he; subst i; exact (by decide : ¬ _) hi)]

private theorem scan_exec (pub : Pub → Word w) (state : Word w) (r : Regs w 32) (m : Memory w)
    (bs : List Bool) (h1 : r 1 = 1) (h2 : r 2 = 2) (hw : 2 ≤ w)
    (hlen : (r 10).val + bs.length = (r 5).val)
    (hr : ∀ (j : ℕ) (hj : j < bs.length), m (r 8 + r 10 + (j : Word w)).val = (bs[j].toNat : Word w)) :
    Flow.Exec pub state scan r m (scanEvents r bs) (folded r bs) m := by
  induction bs generalizing r with
  | nil =>
    apply Flow.Exec.whileDone
    change ¬(r 10).val < (r 5).val
    simp only [List.length_nil, Nat.add_zero] at hlen
    omega
  | cons b bs ih =>
    let v : Word w := b.toNat
    let s := advanced r v
    have ht : r 10 < r 5 := by rw [Fin.lt_def]; simp only [List.length_cons] at hlen; omega
    have hv : m (r 8 + r 10).val = v := by
      have h := hr 0 (by simp)
      change m (r 8 + r 10 + 0).val = v at h
      simpa using h
    have cap : 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    have hb : v < r 2 := by
      rw [h2, Fin.lt_def]
      have ht : (2 : Word w).val = 2 := Nat.mod_eq_of_lt (by omega : 2 < 2 ^ w)
      rw [ht]
      cases b <;> simp [v, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
    have hs : (s 10).val = (r 10).val + 1 := by
      change (r 10 + r 1).val = _
      rw [h1, Fin.val_add_eq_of_add_lt]
      · rw [show (1 : Word w).val = 1 from Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
      · rw [show (1 : Word w).val = 1 from Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
        exact (Nat.succ_le_of_lt ht).trans_lt (r 5).isLt
    refine .whileStep ht (bit_exec pub state r m v hv hb) (ih s h1 h2 ?_ ?_)
    · change (s 10).val + bs.length = (r 5).val
      rw [hs]; simp only [List.length_cons] at hlen; omega
    · intro j hj
      have h := hr (j + 1) (by simpa using hj)
      change m (r 8 + (r 10 + r 1) + (j : Word w)).val = _
      rw [h1, show r 8 + (r 10 + 1) + (j : Word w) = r 8 + r 10 + ((j+1 : ℕ) : Word w) by
        push_cast; ring]
      exact h

private theorem save_exec (pub : Pub → Word w) (state : Word w) (r : Regs w 32) (m : Memory w) :
    Flow.Exec pub state save r m [.write (r 9) (r 11), .tick]
      (Function.update r 29 (r 7 + r 1)) (writeMemory m (r 9) (r 11)) :=
  .seq (.line rfl) (.line rfl)

/-- The full event sequence for a successful word-gather call, ending with the reconstructed
word's destination write. -/
def events (pub : Pub → Word w) (state : Word w) (r : Regs w 32) (v : Word w) :=
  List.replicate 15 .tick ++ (scanEvents (loaded pub state r) (wordBits v) ++
    [.write (pub 1 + state) v, .tick])

/-- A complete word's little-endian bit image at its source address. -/
def BitImage (m : Memory w) (addr : Word w) (v : Word w) : Prop :=
  ∀ i : Fin w, m (addr + (i.val : Word w)).val = ((RAMSerialization.wordBits w v i).toNat : Word w)

/-- The genuine scheduled call executes the bit loop and writes the entire
decoded word. Surplus branch bits are rejected at its terminal instruction. -/
theorem gather_call (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (m : Memory w)
    (hw : 2 ≤ w) (hp : (pub 2).val = w) (hi : state < pub 3) (v : Word w)
    (hv : BitImage m (pub 0 + state * pub 2) v)
    (priv : Word w → Word w) (bits : List Bool) (fuel : ℕ) :
    let machine := table.instantiate w pub
    let es := events pub state rs v
    execute machine.program (es.length + (fuel + 2)) ⟨machine.entry, state, rs, priv⟩ m bits =
      if bits.isEmpty then some ⟨es ++ [.tick], if state + 1 = pub 3 then none else some (state + 1)⟩
      else none := by
  let pre := loaded pub state rs
  let post := folded pre (wordBits v)
  have hscan : Flow.Exec pub state scan pre m (scanEvents pre (wordBits v)) post m := by
    apply scan_exec pub state pre m (wordBits v) rfl rfl hw
    · change (0 : Word w).val + (wordBits v).length = (pub 2).val
      simp [hp]
    · intro j hj
      have h : j < w := by simpa using hj
      change m ((pub 0 + state * pub 2) + 0 + (j : Word w)).val = _
      simpa [wordBits] using hv ⟨j,h⟩
  have hacc : post 11 = v := by
    rw [show post 11 = _ from folded_acc pre (wordBits v), TapeWord.value_wordBits]
    change 0 + 1 * (v.val : Word w) = _
    simp
  have hdest : post 9 = pub 1 + state := folded_keep pre _ 9 (by decide)
  have hstate : post 7 = state := folded_keep pre _ 7 (by decide)
  have hone : post 1 = 1 := folded_keep pre _ 1 (by decide)
  have htotal : post 30 = pub 3 := folded_keep pre _ 30 (by decide)
  let out := Function.update post (29 : Reg) (post 7 + post 1)
  have hbody : Flow.Exec pub state body rs m (events pub state rs v) out
      (writeMemory m (pub 1 + state) v) := by
    have h := Flow.Exec.seq (load_exec pub state rs m hi) (Flow.Exec.seq hscan (save_exec pub state post m))
    simpa only [body, events, pre, hdest, hacc] using h
  have noBits (r : Regs w 32) (b : List Bool) : choiceBits (scanEvents r b) = [] := by
    induction b generalizing r with
    | nil => rfl
    | cons b bs ih => simp [scanEvents, bitEvents, choiceBits, ih]
  have hb : choiceBits (events pub state rs v) = [] := by
    simp [events, Flow.choiceBits_append, noBits, List.replicate_succ, choiceBits]
  have h29 : out 29 = state + 1 := by simp [out, hstate, hone]
  have h30 : out 30 = pub 3 := by change post 30 = _; exact htotal
  simpa only [table, hb, List.nil_append, h29, h30] using
    PrimedCounter.Call.execute_body body 29 30 pub state rs priv m hbody bits fuel

/-- The complete native report, including the final cursor comparison. -/
def report (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (v : Word w) : Report w :=
  ⟨events pub state rs v ++ [.tick], if state + 1 = pub 3 then none else some (state + 1)⟩

private theorem scan_length (r : Regs w 32) (bs : List Bool) :
    (scanEvents r bs).length = 8 * bs.length + 1 := by
  induction bs generalizing r with
  | nil => rfl
  | cons b bs ih => simp [scanEvents, bitEvents, ih]; omega

theorem events_length (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (v : Word w) :
    (events pub state rs v).length = 8 * w + 18 := by simp [events, scan_length]

private theorem probes_append (xs ys : List (Event w)) :
    countProbes (xs ++ ys) = countProbes xs + countProbes ys := by
  induction xs with
  | nil => simp [countProbes]
  | cons e xs ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

private theorem scan_probes (r : Regs w 32) (bs : List Bool) :
    countProbes (scanEvents r bs) = bs.length := by
  induction bs generalizing r with
  | nil => rfl
  | cons b bs ih => simp [scanEvents, bitEvents, countProbes, ih]; omega

theorem report_probes (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (v : Word w) :
    (report pub state rs v).probes = w + 1 := by
  simp [report, events, Report.probes, probes_append, scan_probes, List.replicate_succ, countProbes]

private theorem after_scan (m : Memory w) (r : Regs w 32) (bs : List Bool) :
    after m (scanEvents r bs) = m := by
  induction bs generalizing r with
  | nil => rfl
  | cons b bs ih =>
    change after m (scanEvents (advanced r _) bs) = m
    exact ih _

theorem report_memory (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (m : Memory w) (v : Word w) :
    after m (report pub state rs v).events = writeMemory m (pub 1 + state) v := by
  change after m ((List.replicate 15 .tick ++ (scanEvents _ _ ++ _)) ++ [.tick]) = _
  simp only [after, List.foldl_append]
  change writeMemory (after m (scanEvents (loaded pub state rs) (wordBits v))) (pub 1 + state) v = _
  rw [after_scan]

/-- Uniform fuel bound at every cursor, with the exact report for a normal
call and rejection of every nonempty choice stream. -/
theorem gather_call_at_fuel (pub : Pub → Word w) (state : Word w) (rs : Regs w 32) (m : Memory w)
    (hw : 2 ≤ w) (hp : (pub 2).val = w) (hi : state < pub 3) (v : Word w)
    (hv : BitImage m (pub 0 + state * pub 2) v) (priv : Word w → Word w) (bits : List Bool)
    {fuel : ℕ} (hf : 8 * w + 20 ≤ fuel) :
    let machine := table.instantiate w pub
    execute machine.program fuel ⟨machine.entry, state, rs, priv⟩ m bits =
      if bits.isEmpty then some (report pub state rs v) else none := by
  have h := gather_call pub state rs m hw hp hi v hv priv bits (fuel - (8 * w + 20))
  dsimp only at h
  rw [events_length, show 8*w + 18 + (fuel - (8*w+20) + 2) = fuel by omega] at h
  exact h

end LiveConfigGather

end VPVNP
end Computability
end OAI
