import OAI.Computability.BorderVNP.CellPacketEncodeDigit
import OAI.Computability.BorderVNP.PackedDirectoryWriter

/-! # Native copies of bit slices into the private-call packet

The opaque-field mode writes a zero tag before every bit. The external-input mode
writes the bits themselves. The enclosing encoder appends the opaque-field terminator
using the same destination cursor. Source and output may occur in either address order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacketCopy

open VPVNP.BurstRAM CellPacketEncode

/-- Load and advance the input cursor, then write one raw or zero-prefixed bit. -/
def step (framed : Bool) : Code :=
  .seq (.block [.load 16 14, .binary .add 14 14 1]) (emit framed 16)

/-- Scan the half-open interval in registers 14 and 15. -/
def copy (framed : Bool) : Code := .whileLt 14 15 (step framed)

/-- End marker for an opaque field, emitted at the same cursor as its data. -/
def appendOne : Code := emit false 1

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Append the one-bit terminator in two ordinary instructions. -/
theorem appendOne_run (s : Bank w) (m : Memory w) (c : Constants (readings s))
    (fit : readings s 20 + 1 < 2^w) :
    BoundedRun pub macros appendOne s m 2 (Written (.ofWords s m) [true]) := by
  have safe : appendOne.fixedSafe w (readings pub) (.ofWords s m) := by
    simpa [appendOne, emit, Code.fixedSafe, Code.fixedEval, Code.safeReadOnly, addressOpFits,
      NatState.ofWords, c.2.1] using fit
  apply (appendOne.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  refine ⟨fun j hj => ?_, ?_, ?_⟩ <;>
    simp_all [appendOne, emit, Code.fixedEval, Code.evalNat, addressOp, NatState.ofWords, putDigits, c.2.1]

private theorem step_run (e : Bool) (s : Bank w) (m : Memory w) (b : Bool)
    (c : Constants (readings s)) (value : readings m (readings s 14) = b.toNat)
    (srcFit : readings s 14 + 1 < 2^w) (dstFit : readings s 20 + (tags e [b]).length < 2^w) :
    BoundedRun pub macros (step e) s m 6 (fun z => Fixed (readings s) z.reg ∧
      z.reg 14 = readings s 14 + 1 ∧ z.reg 20 = readings s 20 + (tags e [b]).length ∧
      z.mem = putDigits (readings m) (readings s 20) (tags e [b])) := by
  let fetch := Code.block [.load 16 14, .binary .add 14 14 1]
  have safe : fetch.fixedSafe w (readings pub) (.ofWords s m) := by
    simpa (config := {decide := true}) [fetch, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, NatState.ofWords, c.2.1] using srcFit
  apply (fetch.runFixed pub macros s m safe).seq (t := 4)
  intro t mt he
  have ht := congrArg NatState.reg he
  have hmem := congrArg NatState.mem he
  change readings mt = readings m at hmem
  have regs (j : Reg) (ha : j ≠ 14) (hb : j ≠ 16) : readings t j = readings s j := by
    simpa [fetch, Code.block, Code.fixedEval, Code.evalNat, ha, hb, NatState.ofWords] using congrFun ht j
  have hs : readings t 14 = readings s 14 + 1 := by
    simpa (config := {decide := true}) [fetch, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, NatState.ofWords, c.2.1] using congrFun ht 14
  have hb : readings t 16 = b.toNat := by
    simpa (config := {decide := true}) [fetch, Code.block, Code.fixedEval, Code.evalNat,
      NatState.ofWords, value] using congrFun ht 16
  have hd := regs 20 (by decide) (by decide)
  have hfixed : Fixed (readings s) (readings t) := fun j a b _ _ => regs j a b
  apply (emit_run (pub := pub) (macros := macros) e t mt 16 (by decide) b hb
    (hfixed.constants c) (by rwa [hd])).mono le_rfl
  intro z hz
  exact ⟨fun j a b _ d => (hz.regs j d).trans (regs j a b),
    (hz.regs 14 (by decide)).trans hs, hz.cursor.trans (congrArg (· + _) hd),
    hz.mem.trans (by change putDigits (readings mt) (readings t 20) _ = _; rw [hd,hmem])⟩

/-- The actual copy fills its entire output interval with the requested digits, advances both
cursors to their exclusive ends, and preserves the protected register bank. -/
theorem copy_run (e : Bool) (s : Bank w) (m : Memory w) (xs : List Bool)
    (c : Constants (readings s)) (stop : readings s 15 = readings s 14 + xs.length)
    (source : ∀ i : Fin xs.length, readings m (readings s 14 + i.val) = xs[i].toNat)
    (apart : readings s 14 + xs.length ≤ readings s 20 ∨ readings s 20 + (tags e xs).length ≤ readings s 14)
    (fit : readings s 20 + (tags e xs).length < 2^w) :
    BoundedRun pub macros (copy e) s m (7*xs.length+1) (fun z => Fixed (readings s) z.reg ∧
      z.reg 14 = readings s 15 ∧ z.reg 20 = readings s 20 + (tags e xs).length ∧
      z.mem = putDigits (readings m) (readings s 20) (tags e xs)) := by
  induction xs generalizing s m with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at stop
    refine ⟨_,s,m,.whileDone (show ¬ (s 14).val < (s 15).val from not_lt_of_ge stop.le),le_rfl,
      fun _ _ _ _ _ => rfl, stop.symm, ?_, ?_⟩ <;> simp [NatState.ofWords, putDigits]
  | cons b xs ih =>
    have splitTags : tags e (b::xs) = tags e [b] ++ tags e xs := tags_append e [b] xs
    simp only [splitTags, List.length_append] at fit apart ⊢
    simp only [List.length_cons] at stop apart
    have srcBound : readings s 15 < 2^w := (s 15).isLt
    have head : readings m (readings s 14) = b.toNat := by simpa using source ⟨0,by simp⟩
    obtain ⟨es,t,mt,first,hcost,fixed,hs,hd,hm⟩ :=
      step_run (pub := pub) (macros := macros) e s m b c head (by omega) (by omega)
    change readings t 14 = readings s 14 + 1 at hs
    change readings t 20 = readings s 20 + (tags e [b]).length at hd
    change readings mt = putDigits (readings m) (readings s 20) (tags e [b]) at hm
    have he : readings t 15 = readings s 15 := fixed 15 (by decide) (by decide) (by decide) (by decide)
    have tail (i : Fin xs.length) : readings mt (readings t 14 + i.val) = xs[i].toNat := by
      have hi := i.isLt
      rw [hm, putDigits_outside _ _ _ _ (by rcases apart with h|h <;> omega), hs,
        Nat.add_assoc, Nat.add_comm 1 i.val]
      exact source i.succ
    obtain ⟨fs,z,mz,last,hcost',fixed',hs',hd',hm'⟩ := ih t mt (fixed.constants c)
      (by omega) tail (by rcases apart with h|h <;> omega) (by omega)
    refine ⟨_,z,mz,.whileStep (show (s 14).val < (s 15).val from (show readings s 14 < readings s 15 by omega))
      first last, ?_, fixed.trans fixed', hs'.trans he, ?_, ?_⟩
    · change 1 + traceCost (es ++ fs) ≤ 7*(xs.length+1)+1
      rw [show traceCost (es ++ fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
      omega
    · change readings z 20 = readings t 20 + (tags e xs).length at hd'
      change readings z 20 = _
      omega
    · rw [putDigits_append, ← hd, ← hm]; exact hm'

/-- The natural-state postcondition is also an exact equality of physical word memories. -/
theorem putWords_of_putDigits {m m' : Memory w} (dst : ℕ) (bs : List Bool) (positive : 1 < 2^w)
    (h : readings m' = putDigits (readings m) dst bs) :
    m' = Packing.Directory.ISA.putWords m dst (bs.map fun b => DiagonalResidueRAM.word w b.toNat) := by
  suffices aux : ∀ (m : Memory w) (dst : ℕ),
      readings (Packing.Directory.ISA.putWords m dst (bs.map fun b => DiagonalResidueRAM.word w b.toNat)) =
      putDigits (readings m) dst bs by
    funext j; exact Fin.ext (congrFun (h.trans (aux m dst).symm) j)
  clear h m m' dst
  induction bs with
  | nil => exact fun _ _ => rfl
  | cons b bs ih =>
    intro m dst
    simp only [List.map_cons, Packing.Directory.ISA.putWords, putDigits, ih]
    congr 1
    funext j
    by_cases hj : j = dst
    · subst j; simp only [readings, Function.update_self]
      exact DiagonalResidueRAM.word_val _ _ (by cases b <;> simp_all)
    · simp [readings, hj]

end RoutingISA.CellPacketCopy

end BorderVNP
end Computability
end OAI
