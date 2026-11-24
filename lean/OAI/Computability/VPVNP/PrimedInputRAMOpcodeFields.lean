import OAI.Computability.VPVNP.PrimedInputRAMOnce
import OAI.Computability.VPVNP.PrimedInputRAMOpcodes
import OAI.Computability.VPVNP.PrimedInputRAMDispatch
import Mathlib.Data.ZMod.Defs

/-!
# Native word instructions for literals and header fields

The four header fields choose between a literal zero and an address derived from the
loaded parameters. A middle-cut bit is owned only by the outgoing endpoint of group
zero. All paths in these blocks update only the payload, fetch flag, and owner flag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Register output common to all field decisions. -/
def fieldResult (rs : Regs w 48) (d : RawCopy × Bool) : Regs w 48 :=
  let (value, fetch) := match d.1 with
    | .literal b => (encodeBit w b, (0 : Word w))
    | .fetch addr => ((addr : Word w), 1)
  Function.update (Function.update (Function.update rs (26 : Reg) value) 27 fetch) 28 (encodeBit w d.2)

@[simp] theorem fieldResult_payload (rs : Regs w 48) (d : RawCopy × Bool) :
    fieldResult rs d 26 = match d.1 with
      | .literal b => encodeBit w b
      | .fetch addr => (addr : Word w) := by
  rcases d with ⟨src, own⟩
  cases src <;> rfl

@[simp] theorem fieldResult_fetch (rs : Regs w 48) (d : RawCopy × Bool) :
    fieldResult rs d 27 = match d.1 with
      | .literal _ => 0
      | .fetch _ => 1 := by
  rcases d with ⟨src, own⟩
  cases src <;> rfl

@[simp] theorem fieldResult_owner (rs : Regs w 48) (d : RawCopy × Bool) :
    fieldResult rs d 28 = encodeBit w d.2 := by
  rcases d with ⟨src, own⟩
  cases src <;> rfl

theorem fieldResult_other (rs : Regs w 48) (d : RawCopy × Bool) (i : Reg)
    (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) : fieldResult rs d i = rs i := by
  rcases d with ⟨src, own⟩
  cases src <;> simp [fieldResult, Function.update_of_ne, h26, h27, h28]

/-- The shift-and-mask implements the mathematical bit, including shifts beyond
the end of the word. -/
theorem readBit_word (hw : 0 < w) (x j : Word w) :
    BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval x j) 1 = encodeBit w (x.val.testBit j.val) := by
  have hone := Nat.one_lt_two_pow hw.ne'
  by_cases hj : j.val < w
  · have hshift : x.val / 2^j.val < 2^w := (Nat.div_le_self ..).trans_lt x.isLt
    rcases Nat.mod_two_eq_zero_or_one (x.val / 2^j.val) with hb | hb <;>
      simp [BinaryOp.eval, hj, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hshift,
        Nat.mod_eq_of_lt hone, Nat.testBit_eq_decide_div_mod_eq, hb, encodeBit]
  · have ht := Nat.testBit_lt_two_pow (x := x.val) (i := j.val)
        (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hj)))
    simp [BinaryOp.eval, hj, ht, encodeBit]

theorem exec_literalZero (pub : Pub → Word w) (state : Word w) (rs : Regs w 48) (m : Memory w) :
    Flow.Exec pub state literalZero rs m (List.replicate 3 .tick)
      (fieldResult rs (.literal false, false)) m :=
  (Flow.once_sound pub state false literalZero rs m rfl).1

theorem exec_literalBit (pub : Pub → Word w) (state : Word w) (rs : Regs w 48) (m : Memory w)
    (hw : 0 < w) (hone : rs 1 = 1) (src amount : Reg) :
    Flow.Exec pub state (literalBit src amount) rs m (List.replicate 4 .tick)
      (fieldResult rs (.literal ((rs src).val.testBit (rs amount).val), false)) m := by
  apply (Flow.once_sound pub state false _ rs m ?_).1
  change some (_, Function.update (Function.update (Function.update (Function.update rs (26 : Reg) _)
    26 (BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval (rs src) (rs amount)) (rs 1))) 27 0) 28 0, m) = _
  rw [Function.update_idem, hone, readBit_word hw]
  rfl

/-- Register values after loading the public dimensions and cut lengths and
decoding the current row's group, site, and header offset. -/
structure HeaderRegisters (rs : Regs w 48) (L : Lengths) (base n r P g v j : ℕ) : Prop where
  zero : (rs 0).val = 0
  one : (rs 1).val = 1
  two : (rs 2).val = 2
  three : (rs 3).val = 3
  rowWidth : (rs 6).val = n
  siteBits : (rs 8).val = r
  baseAddr : (rs 11).val = base
  prefixWidth : (rs 12).val = P
  indexWidth : (rs 14).val = L.index
  adviceWidth : (rs 15).val = L.advice
  cutCapacity : (rs 16).val = L.cutCapacity
  leftCut : (rs 18).val = L.leftCut
  middleCut : (rs 19).val = L.middleCut
  rightCut : (rs 20).val = L.rightCut
  group : (rs 22).val = g
  site : (rs 23).val = v
  offset : (rs 25).val = j

private theorem regCast {x : Word w} {v : ℕ} (h : x.val = v) : x = (v : Word w) := by
  rw [← h, Fin.cast_val_eq_self]

theorem once_headerFields (pub : Pub → Word w) (state : Word w) (bit : Bool)
    (rs : Regs w 48) (m : Memory w) {L : Lengths} {base n r P g v j : ℕ}
    (h : HeaderRegisters rs L base n r P g v j) (hj : j < 4) :
    ∃ t, Flow.once pub state bit headerFields rs m = some (List.replicate t .tick,
      fieldResult rs (dispatchHeader L base n r P g v j), m) := by
  have ej₀ : rs 25 = rs 0 ↔ j = 0 := by rw [Fin.ext_iff, h.offset, h.zero]
  have ej₁ : rs 25 = rs 1 ↔ j = 1 := by rw [Fin.ext_iff, h.offset, h.one]
  have ej₂ : rs 25 = rs 2 ↔ j = 2 := by rw [Fin.ext_iff, h.offset, h.two]
  have eg : rs 22 = rs 0 ↔ g = 0 := by rw [Fin.ext_iff, h.group, h.zero]
  have vi : rs 23 < rs 14 ↔ v < L.index := by rw [Fin.lt_def, h.site, h.indexWidth]
  have va : rs 23 < rs 15 ↔ v < L.advice := by rw [Fin.lt_def, h.site, h.adviceWidth]
  have vl : rs 23 < rs 18 ↔ v < L.leftCut := by rw [Fin.lt_def, h.site, h.leftCut]
  have vm : rs 23 < rs 19 ↔ v < L.middleCut := by rw [Fin.lt_def, h.site, h.middleCut]
  have vr : rs 23 < rs 20 ↔ v < L.rightCut := by rw [Fin.lt_def, h.site, h.rightCut]
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  case' inl =>
    by_cases hv : v < L.index <;> refine ⟨if v < L.index then 7 else 5, ?_⟩
  case' inr.inl =>
    by_cases hv : v < L.advice <;> refine ⟨if v < L.advice then 8 else 6, ?_⟩
  case' inr.inr.inl =>
    refine ⟨if g = 0 then (if v < L.leftCut then 11 else 8)
      else (if v < L.middleCut then 12 else 8), ?_⟩
    by_cases hg : g = 0 <;> by_cases hv : v < (if g = 0 then L.leftCut else L.middleCut)
    all_goals simp only [hg, ↓reduceIte] at hv
  case' inr.inr.inr =>
    refine ⟨if g = 0 then (if v < L.middleCut then 12 else 8)
      else (if v < L.rightCut then 12 else 8), ?_⟩
    by_cases hg : g = 0 <;> by_cases hv : v < (if g = 0 then L.middleCut else L.rightCut)
    all_goals simp only [hg, ↓reduceIte] at hv
  all_goals
    simp (config := { decide := true }) only [headerFields, Flow.once, indexField, adviceField, leftField, middleField,
      rightField, dispatchHeader, ↓reduceIte, *]
  all_goals first | rfl |
    (simp [fetched, adviceBase, sequence, bin, set, line, Flow.once, Op.effect, BinaryOp.eval,
      fieldResult, rectangleAddress, encodeBit, Function.update_idem, regCast h.group,
      regCast h.indexWidth, regCast h.adviceWidth, regCast h.cutCapacity, regCast h.site,
      regCast h.baseAddr, regCast h.rowWidth, regCast h.prefixWidth, regCast h.siteBits,
      regCast h.two, regCast h.three, add_assoc, add_comm, add_left_comm]; rfl)

/-- Bounded, probe-free execution of all four supplied header fields. -/
theorem exec_headerFields (pub : Pub → Word w) (state : Word w) (rs : Regs w 48) (m : Memory w)
    {L : Lengths} {base n r P g v j : ℕ} (h : HeaderRegisters rs L base n r P g v j) (hj : j < 4) :
    ∃ t ≤ headerFields.length, Flow.Exec pub state headerFields rs m (List.replicate t .tick)
      (fieldResult rs (dispatchHeader L base n r P g v j)) m := by
  obtain ⟨t, ht⟩ := once_headerFields pub state false rs m h hj
  have hs := Flow.once_sound pub state false headerFields rs m ht
  exact ⟨t, by simpa only [List.length_replicate] using hs.2, hs.1⟩

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
