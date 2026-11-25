import OAI.Computability.BorderVNP.RoutingISACompactWriteBits
import OAI.Computability.BorderVNP.RoutingISACompactWriteStep
import OAI.Computability.BorderVNP.RoutingISABlockAppend

/-!
# Reading a payload word and writing its two framed bits

The native iteration checks that the word read from shared memory is a Boolean
digit, emits a tag and that digit, and advances its source index. Disjoint
source and output intervals keep earlier stores from changing the next read.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactWrite

open VPVNP.BurstRAM

/-- Natural values of the target packed words, extended by zero. -/
def targetWords (w : ℕ) (xs : List Bool) (k : ℕ) : ℕ := (((CompactFrame.pack w xs)[k]?).getD 0).val

/-- One Boolean-valued source word for each payload digit, in input order. -/
def Source {w : ℕ} (original : Memory w) (src : ℕ) (xs : List Bool) : Prop :=
  ∀ i (hi : i < xs.length), (original (src+i)).val = xs[i].toNat

/-- The half-open source and destination intervals are separated in either order. -/
def Disjoint (src n dst count : ℕ) : Prop := src+n ≤ dst ∨ dst+count ≤ src

private def readDigit : List Code :=
  [.binary .add 12 3 6, .load 11 12, .ifEq 11 0 .nop (requireEq 11 1)]

private def writeDigit : List Code := [emit 1, emit 11, .binary .add 6 6 1]

private theorem read_run {w src dst i : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} (xs : List Bool) (original : Memory w) (hw : 0 < w)
    (hi : i < xs.length) (source : Source original src xs)
    (separate : Disjoint src xs.length dst (CompactFrame.pack w xs).length)
    (srcFit : src+xs.length ≤ 2^w) (h : Ready w src xs.length dst i (.ofWords s m))
    (a : At w dst (targetWords w xs) (readings original) (2*i) (.ofWords s m)) :
    BoundedRun pub macros (.block readDigit) s m (Code.block readDigit).slots (fun z =>
      Ready w src xs.length dst i z ∧ At w dst (targetWords w xs) (readings original) (2*i) z ∧
        z.reg 11 = xs[i].toNat) := by
  let z := NatState.ofWords s m
  let env := readings pub
  have fit : src+i < 2^w := by omega
  have outside : ¬ (dst ≤ src+i ∧ src+i-dst < (2*i)/w) := by
    have bound := CompactFrame.word_in_range hw xs (2*i) (by omega)
    rcases separate with left | right <;> omega
  have bit : z.mem (src+i) = xs[i].toNat := by
    change (NatState.ofWords s m).mem (src+i) = _
    rw [a.memory, image, ite_eq_right outside]
    exact source i hi
  have hz : z.reg 0 = 0 := h.zero
  have ho : z.reg 1 = 1 := h.one
  have hs : z.reg 3 = src := h.source
  have hi' : z.reg 6 = i := h.index
  let result : NatState := ⟨Function.update (Function.update z.reg 12 (src+i)) 11 xs[i].toNat, z.mem⟩
  have spec : (Code.block readDigit).fixedSafe w env z ∧ (Code.block readDigit).fixedEval env z = result := by
    cases hb : xs[i] <;> simp (config := {decide := true}) [readDigit, Code.block, requireEq,
      Code.fixedSafe, Code.fixedEval, Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp,
      hz, ho, hs, hi', fit, bit, hb, result]
  apply (Code.runFixed (.block readDigit) pub macros s m spec.1).mono le_rfl
  rintro _ rfl
  change Ready w src xs.length dst i ((Code.block readDigit).fixedEval env z) ∧ _
  rw [spec.2]
  constructor
  · constructor <;> simp (config := {decide := true}) [result, h.zero, h.one, h.width, h.source,
      h.length, h.destination, h.index, z]
  · constructor
    · constructor <;> simp (config := {decide := true}) [result, z, a.address, a.used, a.value, a.place, a.memory]
    · simp [result]

private theorem increment_run {w src n dst i j : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} (words original : ℕ → ℕ) (more : i < n)
    (h : Ready w src n dst i (.ofWords s m)) (a : At w dst words original j (.ofWords s m)) :
    BoundedRun pub macros (.binary .add 6 6 1) s m (Code.binary .add 6 6 1).slots
      (fun z => Ready w src n dst (i+1) z ∧ At w dst words original j z) := by
  have fit := h.length.symm.trans_lt (s 4).isLt
  have safe : (Code.binary .add 6 6 1).fixedSafe w (readings pub) (.ofWords s m) := by
    change (NatState.ofWords s m).reg 6 + (NatState.ofWords s m).reg 1 < 2^w
    rw [h.index, h.one]
    omega
  apply (Code.runFixed _ pub macros s m safe).mono le_rfl
  rintro _ rfl
  constructor
  · constructor <;> simp (config := {decide := true}) [Code.fixedEval, Code.evalNat, addressOp,
      h.zero, h.one, h.width, h.source, h.length, h.destination, h.index]
  · constructor <;> simp (config := {decide := true}) [Code.fixedEval, Code.evalNat,
      a.address, a.used, a.value, a.place, a.memory]

/-- One physical loop iteration reads a genuine source digit and emits its
presence tag followed by its value. The exact packed-word prefix and register
invariants advance by two bits and one input word. -/
theorem step_run {w src dst i : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} (xs : List Bool) (original : Memory w)
    (hw : 0 < w) (hi : i < xs.length) (source : Source original src xs)
    (separate : Disjoint src xs.length dst (CompactFrame.pack w xs).length)
    (srcFit : src+xs.length ≤ 2^w) (dstFit : dst+(CompactFrame.pack w xs).length ≤ 2^w)
    (h : Ready w src xs.length dst i (.ofWords s m))
    (a : At w dst (targetWords w xs) (readings original) (2*i) (.ofWords s m)) :
    BoundedRun pub macros step s m step.slots (fun z =>
      Ready w src xs.length dst (i+1) z ∧ At w dst (targetWords w xs) (readings original) (2*(i+1)) z) := by
  let words := targetWords w xs
  have fits (k : ℕ) : words k < 2^w := (((CompactFrame.pack w xs)[k]?).getD 0).isLt
  have room (j : ℕ) (hj : j ≤ 2*xs.length) : dst+j/w < 2^w := by
    have bound := CompactFrame.word_in_range hw xs j hj
    omega
  have bits (j : ℕ) : (words (j/w)).testBit (j%w) = CompactFrame.letter xs j :=
    CompactFrame.atWord_bit hw xs j
  let read := read_run (pub := pub) (macros := macros) xs original hw hi source separate srcFit h a
  have next (u : Bank w) (mu : Memory w) (hu : Ready w src xs.length dst i (.ofWords u mu))
      (au : At w dst words (readings original) (2*i) (.ofWords u mu)) (data : (u 11).val = xs[i].toNat) :
      BoundedRun pub macros (.block writeDigit) u mu (Code.block writeDigit).slots (fun z =>
        Ready w src xs.length dst (i+1) z ∧ At w dst words (readings original) (2*(i+1)) z) := by
    have tag : (u 1).val = ((words ((2*i)/w)).testBit ((2*i)%w)).toNat := by
      rw [bits, CompactFrame.letter_tag xs hi]
      exact hu.one
    apply (emit_run (pub := pub) (macros := macros) 1 words _ hw (fits _) (room _ (by omega)) hu au tag).seq
    rintro v mv ⟨hv, av, saved⟩
    have digit : (v 11).val = ((words ((2*i+1)/w)).testBit ((2*i+1)%w)).toNat := by
      rw [bits, CompactFrame.letter_data xs hi]
      exact saved.trans data
    apply (emit_run (pub := pub) (macros := macros) 11 words _ hw (fits _) (room _ (by omega)) hv av digit).seq
    rintro b mb ⟨hb, ab, _⟩
    rw [show 2*(i+1) = 2*i+1+1 by omega]
    exact increment_run words _ hi hb ab
  obtain ⟨es, t, mt, run, bound, post⟩ := read.seq (fun u mu hr => next u mu hr.1 hr.2.1 hr.2.2)
  exact ⟨es, t, mt, (Runs.block_append_iff (a := readDigit) (b := writeDigit) (by decide) (by decide)).2 run,
    bound, post⟩

end RoutingISA.CompactWrite

end BorderVNP
end Computability
end OAI
