import OAI.Computability.BorderVNP.CellPacketEncodeModel

/-! # Physical execution of the sparse integer digit writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacketEncode

open VPVNP.BurstRAM RationalHitting.StackLanguage

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- The digit writer changes only register 20 and fills consecutive scratch addresses. -/
structure Written (start : NatState) (bs : List Bool) (finish : NatState) : Prop where
  /-- Every other register is preserved. -/
  regs : ∀ j, j ≠ 20 → finish.reg j = start.reg j
  /-- Cursor immediately past the encoded digits. -/
  cursor : finish.reg 20 = start.reg 20 + bs.length
  /-- Chronological writes of the digits. -/
  mem : finish.mem = putDigits start.mem (start.reg 20) bs

/-- Consecutive digit writes preserve all other registers and concatenate their outputs. -/
theorem Written.append {s t z : NatState} {xs ys : List Bool}
    (a : Written s xs t) (b : Written t ys z) : Written s (xs++ys) z :=
  ⟨fun j hj => (b.regs j hj).trans (a.regs j hj),
    by rw [b.cursor,a.cursor,List.length_append,Nat.add_assoc],
    by rw [putDigits_append, ← a.mem, ← a.cursor, b.mem]⟩

private theorem single_run (s : Bank w) (m : Memory w) (r : Reg) (b : Bool)
    (value : readings s r = b.toNat) (one : readings s 1 = 1)
    (fit : readings s 20 + 1 < 2^w) :
    BoundedRun pub macros (emit false r) s m 2 (Written (.ofWords s m) [b]) := by
  let z := NatState.ofWords s m
  have safe : (emit false r).fixedSafe w (readings pub) z := by
    simpa [emit, Code.fixedSafe, Code.fixedEval, Code.safeReadOnly, addressOpFits, z, NatState.ofWords,
      one] using fit
  apply ((emit false r).runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  refine ⟨fun j hj => ?_,?_,?_⟩ <;>
    simp_all [emit, Code.fixedEval, Code.evalNat, addressOp, NatState.ofWords, putDigits]

/-- Each emitted logical digit has either one or two actual stores. -/
theorem emit_run (e : Bool) (s : Bank w) (m : Memory w) (r : Reg) (hr : r ≠ 20) (b : Bool)
    (value : readings s r = b.toNat) (c : Constants (readings s))
    (fit : readings s 20 + (tags e [b]).length < 2^w) :
    BoundedRun pub macros (emit e r) s m 4 (Written (.ofWords s m) (tags e [b])) := by
  cases e with
  | false =>
    exact (single_run s m r b value c.2.1 fit).mono (by decide) fun _ h => h
  | true =>
    change readings s 20 + 2 < 2^w at fit
    have first := single_run (pub := pub) (macros := macros) s m 0 false c.1 c.2.1 (by omega)
    apply first.seq (b := emit false r) (t := 2)
    intro t mt h
    have cursor : readings t 20 = readings s 20+1 := h.cursor
    have next := single_run (pub := pub) (macros := macros) t mt r b
      ((h.regs r hr).trans value) ((h.regs 1 (by decide)).trans c.2.1) (by omega)
    exact next.mono le_rfl fun _ h' => h.append h'

private theorem divide_run (s : Bank w) (m : Memory w) (a : ℕ) (hv : readings s 16 = a)
    (two : readings s 18 = 2) :
    BoundedRun pub macros (.block [.binary .mod 17 16 18, .binary .div 16 16 18]) s m 2
      (fun z => z.reg 16 = a/2 ∧ z.reg 17 = a.bodd.toNat ∧
        (∀ j, j ≠ 16 → j ≠ 17 → z.reg j = readings s j) ∧ z.mem = readings m) := by
  let block := Code.block [.binary .mod 17 16 18, .binary .div 16 16 18]
  have safe : block.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [block, Code.block, Code.fixedSafe, Code.safeReadOnly,
      Code.fixedEval, Code.evalNat, addressOpFits, NatState.ofWords, two]
  apply (block.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  simp (config := {decide := true}) [block, Code.block, Code.fixedEval, Code.evalNat, addressOp,
    NatState.ofWords, hv, two, Nat.mod_two_of_bodd]
  intro j h16 h17
  simp [h16,h17]

/-- One native division step emits a zero tag and the least significant bit. -/
theorem digit_run (e : Bool) (s : Bank w) (m : Memory w) (a : ℕ)
    (c : Constants (readings s)) (hv : readings s 16 = a)
    (fit : readings s 20 + (tags e [false,a.bodd]).length < 2^w) :
    BoundedRun pub macros (digit e) s m 10 (fun z =>
      z.reg 16 = a/2 ∧ (∀ j, j ≠ 16 → j ≠ 17 → j ≠ 20 → z.reg j = readings s j) ∧
      z.reg 20 = readings s 20 + (tags e [false,a.bodd]).length ∧
      z.mem = putDigits (readings m) (readings s 20) (tags e [false,a.bodd])) := by
  rw [show [false,a.bodd] = [false] ++ [a.bodd] by rfl, tags_append, List.length_append] at fit
  apply (divide_run (pub := pub) (macros := macros) s m a hv c.2.2).seq (b := .seq (emit e 0) (emit e 17)) (t := 8)
  rintro t mt ⟨quotient,remainder,regs,mem⟩
  have ct : Constants (readings t) :=
    ⟨(regs 0 (by decide) (by decide)).trans c.1, (regs 1 (by decide) (by decide)).trans c.2.1,
      (regs 18 (by decide) (by decide)).trans c.2.2⟩
  have cursor : readings t 20 = readings s 20 := regs 20 (by decide) (by decide)
  apply (emit_run (pub := pub) (macros := macros) e t mt 0 (by decide) false ct.1 ct (by omega)).seq (b := emit e 17) (t := 4)
  intro u mu h
  have cu := Fixed.constants (fun j _ _ _ hj => h.regs j hj) ct
  have curu : readings u 20 = readings t 20 + (tags e [false]).length := h.cursor
  apply (emit_run (pub := pub) (macros := macros) e u mu 17 (by decide) a.bodd
    ((h.regs 17 (by decide)).trans remainder) cu (by omega)).mono le_rfl
  intro z g
  have total := h.append g
  rw [← tags_append] at total
  exact ⟨(total.regs 16 (by decide)).trans quotient,
    fun j ha hb hc => (total.regs j hc).trans (regs j ha hb),
    total.cursor.trans (congrArg (· + _) cursor),
    total.mem.trans (by change putDigits (readings mt) (readings t 20) _ = _; rw [cursor]; exact congrArg (fun f => putDigits f _ _) mem)⟩

end RoutingISA.CellPacketEncode

end BorderVNP
end Computability
end OAI
