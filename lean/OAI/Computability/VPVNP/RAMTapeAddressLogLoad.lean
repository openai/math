import OAI.Computability.VPVNP.RAMTapeAddressLogRestore
import OAI.Computability.VPVNP.RAMTapeAddressLogValues

/-!
# Private log lookup on a fixed finite bit-stack machine

The scan compares each full address against the query, starting at the newest
write. The first hit supplies the output. Exhaustion supplies a width-matched
zero. Rewinding the consumed prefixes restores every occupied entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AddressLog

open BurstRAM BurstRAM.PrivateRAM

variable {w : ℕ}

/-- Split after the first matching entry, or after the entire log on a miss. -/
def scanSplit (a : Word w) : WriteLog w → WriteLog w × WriteLog w
  | [] => ([], [])
  | (k, v) :: tail =>
    if a = k then ([(k, v)], tail)
    else let cut := scanSplit a tail; ((k, v) :: cut.1, cut.2)

theorem scanSplit_append (a : Word w) (log : WriteLog w) :
    (scanSplit a log).1 ++ (scanSplit a log).2 = log := by
  induction log with
  | nil => rfl
  | cons e tail ih =>
    obtain ⟨k, v⟩ := e
    by_cases h : a = k <;> simp [scanSplit, h, ih]

/-- Cost up to the rewind of the key stream. An unsuccessful final empty
test includes making the zero result and restoring the query. -/
def seekCost (a : Word w) : WriteLog w → ℕ
  | [] => 5 * w + 3
  | (k, _) :: tail => if a = k then 9 * w + 4 else 8 * w + 4 + seekCost a tail

private def start (a : Word w) (log : WriteLog w) (s : Bank) : Bank :=
  {s with
    q := wordBits a, ks := keys log, vs := values log, marks := List.replicate log.length true,
    sq := [], so := []}

private def finish (a : Word w) (log : WriteLog w) (s : Bank) : Bank :=
  let cut := scanSplit a log
  {s with
    q := wordBits a, ks := keys cut.2, vs := values cut.2, marks := List.replicate cut.2.length true,
    sq := [], so := (wordBits (WriteLog.memory log a)).reverse,
    sk := (keys cut.1).reverse ++ s.sk, sv := (values cut.1).reverse ++ s.sv,
    sm := List.replicate cut.1.length true ++ s.sm}

private theorem bit_comparison (a k : Word w) :
    (wordBits a == wordBits k) = decide (a = k) := by
  by_cases h : a = k
  · simp [h]
  · have hn : wordBits a ≠ wordBits k := fun eq => h ((RAMSerialization.wordBits w).injective
      (List.ofFn_injective eq))
    simp [h, hn]

private theorem zero_bits : wordBits (0 : Word w) = List.replicate w false := by
  rw [wordBits, ← List.ofFn_const]
  exact congrArg List.ofFn (funext RAMSerialization.wordBits_zero)

private def advanced (s : Bank) (k v : Word w) : Bank :=
  {s with sk := (wordBits k).reverse ++ s.sk, sv := (wordBits v).reverse ++ s.sv, sm := true :: s.sm}

private def afterEntry (a k v : Word w) (tail : WriteLog w) (s : Bank) : Bank :=
  {start a tail (advanced s k v) with so := if a = k then (wordBits v).reverse else []}

/-- One occupancy pop and push, one width-driven comparison, and one value scan. -/
private theorem entryRun (a k v : Word w) (tail : WriteLog w) (s : Bank) :
    StackRuns loadCode (if a = k then 9 * w + 4 else 8 * w + 4)
      .record (start a ((k,v) :: tail) s).stacks
      (if a = k then .rewind .keys else .record) (afterEntry a k v tail s).stacks := by
  let st : Bank := {start a tail s with sm := true :: s.sm, vs := wordBits v ++ values tail}
  have key := keyRuns true (wordBits a) (wordBits k) (keys tail) st (by simp)
  simp only [length_wordBits, Bool.true_and, bit_comparison, st, start, List.append_nil] at key
  let mid : Bank := {st with q := [], ks := keys tail, sk := (wordBits k).reverse ++ s.sk}
  have val := valueRuns (decide (a = k)) (wordBits a).reverse (wordBits v) (values tail) mid (by simp)
  simp only [List.length_reverse, length_wordBits, List.reverse_reverse, mid, st, start, List.append_nil,
    decide_eq_true_eq] at val
  have pair := key.trans val
  have full : StackRuns loadCode ((4 * w + 1 + ((if a = k then 5 else 4) * w + 1)) + 1 + 1)
      .record (start a ((k,v) :: tail) s).stacks
      (if a = k then .rewind .keys else .record) (afterEntry a k v tail s).stacks :=
    .cons (stepPop _ (show loadCode .record = _ from rfl))
      (.cons (stepPush _ (show loadCode .saveMark = _ from rfl)) pair)
  convert full using 1
  split <;> omega

private theorem seekRun (a : Word w) (log : WriteLog w) (s : Bank) :
    StackRuns loadCode (seekCost a log) .record (start a log s).stacks
      (.rewind .keys) (finish a log s).stacks := by
  induction log generalizing s with
  | nil =>
    let st := start a [] s
    have z := zeroRuns (wordBits a) st
    simp only [st, start, length_wordBits, List.append_nil] at z
    let mid : Bank := {st with q := [], sq := (wordBits a).reverse, so := List.replicate w false}
    have restore := rewindRuns .query mid
    change StackRuns loadCode (2 * (wordBits a).reverse.length + 1) (.rewind .query) mid.stacks
      (.rewind .keys) ({mid with sq := [], q := (wordBits a).reverse.reverse ++ []} : Bank).stacks at restore
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse, length_wordBits] at restore
    have run : StackRuns loadCode ((3 * w + 1 + (2 * w + 1)) + 1) .record st.stacks
        (.rewind .keys) ({mid with sq := [], q := wordBits a} : Bank).stacks :=
      .cons (stepPop _ (show loadCode .record = _ from rfl)) (z.trans restore)
    rw [show 3 * w + 1 + (2 * w + 1) + 1 = 5 * w + 3 by omega] at run
    simpa [st, mid, start, finish, scanSplit, keys, values, zero_bits, seekCost] using run
  | cons e tail ih =>
    obtain ⟨k,v⟩ := e
    have one := entryRun a k v tail s
    by_cases hit : a = k
    · simp only [hit, ↓reduceIte] at one
      simpa [hit, finish, scanSplit, seekCost, afterEntry, start, advanced, keys, values,
        WriteLog.memory_cons] using one
    · simp only [hit, ↓reduceIte, afterEntry] at one
      have run := one.trans (ih (advanced s k v))
      simp only [finish, scanSplit, hit, ↓reduceIte, WriteLog.memory_cons,
        Function.update_of_ne hit, keys, values, List.flatMap_cons, List.reverse_append,
        List.append_assoc, advanced, List.length_cons, List.replicate_succ', List.singleton_append,
        seekCost] at run ⊢
      exact run

/-- The load includes rewinding the visited keys, values, occupancy marks and output. -/
def loadCost (a : Word w) (log : WriteLog w) : ℕ :=
  let n := (scanSplit a log).1.length
  seekCost a log + (2 * (n * w + n * w + n + w) + 4)

private theorem length_keys (log : WriteLog w) : (keys log).length = log.length * w := by
  induction log with
  | nil => simp [keys]
  | cons e log ih => simp [keys, List.length_flatMap, Nat.succ_mul] at ih ⊢; omega

private theorem length_values (log : WriteLog w) : (values log).length = log.length * w := by
  induction log with
  | nil => simp [values]
  | cons e log ih => simp [values, List.length_flatMap, Nat.succ_mul] at ih ⊢; omega

/-- A lookup preserves the query and the full log, clears its work stacks,
and prepends the encoded result to the output port. -/
theorem load_run (a : Word w) (out : List Bool) (log : WriteLog w) :
    StackRuns loadCode (loadCost a log) .record (bank a out log).stacks
      .done (bank a (wordBits (WriteLog.memory log a) ++ out) log).stacks := by
  let s := bank a out log
  have seek := seekRun a log s
  have restore := restoreRuns (finish a log s)
  have hkeys := congrArg keys (scanSplit_append a log)
  have hvalues := congrArg values (scanSplit_append a log)
  have hlen := congrArg List.length (scanSplit_append a log)
  simp only [keys, List.flatMap_append] at hkeys
  simp only [values, List.flatMap_append] at hvalues
  simp only [List.length_append] at hlen
  have run := seek.trans restore
  simp only [s, bank, start, finish, loadCost, List.append_nil, List.length_reverse,
    List.length_replicate, length_wordBits, length_keys, length_values, List.reverse_reverse,
    List.reverse_replicate, ← List.replicate_add, hlen] at run ⊢
  simpa only [keys, values, hkeys, hvalues] using run

private theorem seekCost_le (a : Word w) (log : WriteLog w) :
    seekCost a log ≤ (9 * w + 4) * log.length + (5 * w + 3) := by
  induction log with
  | nil => simp [seekCost]
  | cons e log ih =>
    obtain ⟨k,v⟩ := e
    by_cases hit : a = k <;> simp [hit, seekCost, Nat.mul_succ] <;> omega

/-- The time bound is linear in the length of the encoded log. -/
theorem loadCost_le (a : Word w) (log : WriteLog w) :
    loadCost a log ≤ (13 * w + 6) * log.length + (7 * w + 7) := by
  have hs := seekCost_le a log
  have he := congrArg List.length (scanSplit_append a log)
  simp only [List.length_append] at he
  have hn : (scanSplit a log).1.length ≤ log.length := by omega
  have hw := Nat.mul_le_mul_right w hn
  dsimp [loadCost]
  rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm w log.length] at hs ⊢
  omega

end RAMTape.AddressLog

end VPVNP
end Computability
end OAI
