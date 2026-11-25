import OAI.Computability.BorderVNP.RoutingISACompactWriteLoop
import OAI.Computability.BorderVNP.PackedDirectoryWriter

/-!
# Native compact descriptor writer

The counted loop packs the payload into consecutive little-endian words. One
final store supplies the zero terminator and padding, including the case where
the payload ends exactly on a word boundary.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactWrite

open VPVNP.BurstRAM Packing.Directory.ISA

variable {w src dst : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem setup_run (s : Bank w) (m : Memory w) (N : ℕ) (words : ℕ → ℕ)
    (hw : 0 < w) (width : readings s 2 = w) (source : readings s 3 = src)
    (length : readings s 4 = N) (destination : readings s 5 = dst) :
    BoundedRun pub macros setup s m setup.slots (fun z =>
      Ready w src N dst 0 z ∧ At w dst words (readings m) 0 z) := by
  have one : 1 < 2^w := Nat.one_lt_two_pow hw.ne'
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [setup, Code.block, Code.fixedSafe, Code.safeReadOnly, one]
  apply (setup.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  constructor <;> constructor <;>
    simp (config := {decide := true}) [setup, Code.block, Code.fixedEval, Code.evalNat,
      NatState.ofWords, width, source, length, destination]
  · omega
  · funext a
    simp [image]

private theorem image_eq_putWords (m : Memory w) (xs : List (Word w)) (dst : ℕ) :
    image (fun i => (xs[i]?.getD 0).val) (readings m) dst xs.length =
      readings (putWords m dst xs) := by
  funext a
  by_cases ha : dst ≤ a ∧ a-dst < xs.length
  · let i : Fin xs.length := ⟨a-dst, ha.2⟩
    have eq : dst + i.val = a := Nat.add_sub_of_le ha.1
    have hv := putWords_read m dst xs i
    rw [eq] at hv
    simp [image, readings, ha, hv, i]
  · simp [image, ha, readings, putWords_outside m dst a xs (by omega)]

private theorem finish_run (xs : List Bool) (original : Memory w) (hw : 0 < w)
    (s : Bank w) (m : Memory w)
    (h : At w dst (targetWords w xs) (readings original) (2*xs.length) (.ofWords s m)) :
    BoundedRun pub macros (.store 7 9) s m 1
      (fun z => z.mem = readings (putWords original dst (CompactFrame.pack w xs)) ∧
        z.reg 7 = dst + (2*xs.length)/w) := by
  let j := 2*xs.length
  have full : targetWords w xs (j/w) % 2^(j%w) = targetWords w xs (j/w) :=
    CompactFrame.last_partial hw xs
  have len : j/w+1 = (CompactFrame.pack w xs).length := by
    rw [CompactFrame.length_pack, ← CompactFrame.wordCount, CompactFrame.wordCount_terminator hw]
  apply ((Code.store 7 9).runFixed pub macros s m trivial).mono le_rfl
  rintro _ rfl
  refine ⟨?_,h.address⟩
  change Function.update (NatState.ofWords s m).mem ((NatState.ofWords s m).reg 7)
    ((NatState.ofWords s m).reg 9) = _
  rw [h.memory, h.address, h.value, full, image_succ, len]
  exact image_eq_putWords ..

/-- Starting from the four caller registers, the complete physical program writes
the exact packed descriptor and preserves every other address. -/
theorem writer_run_cursor (s : Bank w) (m : Memory w) (xs : List Bool) (hw : 0 < w)
    (width : readings s 2 = w) (base : readings s 3 = src) (length : readings s 4 = xs.length)
    (destination : readings s 5 = dst) (source : Source m src xs)
    (separate : Disjoint src xs.length dst (CompactFrame.pack w xs).length)
    (srcFit : src+xs.length ≤ 2^w) (dstFit : dst+(CompactFrame.pack w xs).length ≤ 2^w) :
    BoundedRun pub macros writer s m (setup.slots + (step.slots+1)*xs.length + 2)
      (fun z => z.mem = readings (putWords m dst (CompactFrame.pack w xs)) ∧
        z.reg 7 = dst + (2*xs.length)/w) := by
  let I (i : ℕ) (z : NatState) :=
    Ready w src xs.length dst i z ∧ At w dst (targetWords w xs) (readings m) (2*i) z
  have start : BoundedRun pub macros setup s m setup.slots (I 0) := by
    simpa only [I, Nat.mul_zero] using
      setup_run (pub := pub) (macros := macros) s m xs.length (targetWords w xs) hw width base length destination
  have each (i : ℕ) (hi : i < xs.length) (u : Bank w) (mu : Memory w) (h : I i (.ofWords u mu)) :=
    step_run (pub := pub) (macros := macros) xs m hw hi source separate srcFit dstFit h.1 h.2
  have loop (u : Bank w) (mu : Memory w) (h : I 0 (.ofWords u mu)) :=
    run_counted_loop pub macros 6 4 step xs.length step.slots I
      (fun _ _ h => ⟨h.1.index,h.1.length⟩) each 0 (Nat.zero_le _) u mu h
  have run := start.seq fun u mu h => (loop u mu h).seq fun t mt ht =>
    finish_run xs m hw t mt ht.2
  exact run.mono (by rw [Nat.sub_zero, Nat.mul_comm xs.length]; omega) (fun _ h => h)

/-- The packed-word memory after running the complete physical writer. -/
theorem writer_run (s : Bank w) (m : Memory w) (xs : List Bool) (hw : 0 < w)
    (width : readings s 2 = w) (base : readings s 3 = src) (length : readings s 4 = xs.length)
    (destination : readings s 5 = dst) (source : Source m src xs)
    (separate : Disjoint src xs.length dst (CompactFrame.pack w xs).length)
    (srcFit : src+xs.length ≤ 2^w) (dstFit : dst+(CompactFrame.pack w xs).length ≤ 2^w) :
    BoundedRun pub macros writer s m (setup.slots + (step.slots+1)*xs.length + 2)
      (fun z => z.mem = readings (putWords m dst (CompactFrame.pack w xs))) := by
  exact (writer_run_cursor s m xs hw width base length destination source separate srcFit dstFit).mono le_rfl
    (fun _ h => h.1)

/-- The actual returned word memory is the chronological store of the packed array. -/
theorem writer_runs (s : Bank w) (m : Memory w) (xs : List Bool) (hw : 0 < w)
    (width : readings s 2 = w) (base : readings s 3 = src) (length : readings s 4 = xs.length)
    (destination : readings s 5 = dst) (source : Source m src xs)
    (separate : Disjoint src xs.length dst (CompactFrame.pack w xs).length)
    (srcFit : src+xs.length ≤ 2^w) (dstFit : dst+(CompactFrame.pack w xs).length ≤ 2^w) :
    ∃ es t, Runs pub macros writer s m es t (putWords m dst (CompactFrame.pack w xs)) ∧
      traceCost es ≤ setup.slots + (step.slots+1)*xs.length + 2 := by
  obtain ⟨es,t,mt,run,cost,mem⟩ :=
    writer_run (pub := pub) (macros := macros) s m xs hw width base length destination source separate srcFit dstFit
  have exactMemory : mt = putWords m dst (CompactFrame.pack w xs) :=
    funext fun i => Fin.ext (congrFun mem i)
  exact ⟨es,t,exactMemory ▸ run,cost⟩

end RoutingISA.CompactWrite

end BorderVNP
end Computability
end OAI
