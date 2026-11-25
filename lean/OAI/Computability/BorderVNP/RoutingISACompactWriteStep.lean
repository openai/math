import OAI.Computability.BorderVNP.RoutingISACompactWriteModel

/-! # Safe native emission of a single packed bit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactWrite

open VPVNP.BurstRAM

/-- Storing the next completed word extends the exact output prefix by one. -/
theorem image_succ (words original : ℕ → ℕ) (dst k : ℕ) :
    Function.update (image words original dst k) (dst+k) (words k) = image words original dst (k+1) := by
  funext a
  by_cases h : a = dst+k
  · subst a
    simp [image]
  · rw [Function.update_of_ne h]
    unfold image
    split_ifs <;> first | rfl | omega

private theorem low_succ (x p : ℕ) : x % 2^(p+1) =
    if x.testBit p then x % 2^p + 2^p else x % 2^p := by
  rw [pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : x / 2^p % 2 = 1
  · simp [h]
  · have h0 : x / 2^p % 2 = 0 := by omega
    simp [h0]

private def put (d : Reg) : Code := .ifEq d 0 .nop (.binary .add 9 9 10)
private def next : Code := .seq (.binary .add 8 8 1) (.ifEq 8 2 flush (.binary .add 10 10 10))

/-- Append a bit read from the declared register. The register bank and memory agree with
the next bit position of the true target word; a full word is stored and the place resets. -/
theorem emit_run {w src n dst i j : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} (d : Reg) (words original : ℕ → ℕ)
    (hw : 0 < w) (wordFit : words (j/w) < 2^w) (room : dst + (j+1)/w < 2^w)
    (h : Ready w src n dst i (.ofWords s m)) (before : At w dst words original j (.ofWords s m))
    (digit : (s d).val = ((words (j/w)).testBit (j%w)).toNat) :
    BoundedRun pub macros (emit d) s m (emit d).slots (fun z =>
      Ready w src n dst i z ∧ At w dst words original (j+1) z ∧ z.reg 11 = (s 11).val) := by
  let z := NatState.ofWords s m
  let env := readings pub
  let p := j%w
  let q := j/w
  let x := words q
  let u : NatState := ⟨Function.update z.reg 9 (x % 2^(p+1)), z.mem⟩
  have hbit : z.reg d = (x.testBit p).toNat := digit
  have hwidth : w < 2^w := h.width.symm.trans_lt (s 2).isLt
  have hp : p < w := Nat.mod_lt j hw
  have hlo : x % 2^p + 2^p < 2^w := by
    have hm := Nat.mod_lt x (Nat.two_pow_pos p)
    have he := Nat.pow_le_pow_right (by decide : 0 < 2) (show p+1 ≤ w by omega)
    rw [pow_succ] at he
    omega
  have v : z.reg 9 = x % 2^p := before.value
  have pl : z.reg 10 = 2^p := before.place
  have hz : z.reg 0 = 0 := h.zero
  have prep : (put d).fixedSafe w env z ∧ (put d).fixedEval env z = u := by
    cases hb : x.testBit p with
    | false =>
      have low : x % 2^(p+1) = x % 2^p := by rw [low_succ, hb]; rfl
      simp [put, Code.fixedSafe, Code.fixedEval, Code.safeReadOnly, Code.evalNat,
        hbit, hb, hz, u, low, ← v, Function.update_eq_self]
    | true =>
      have low : x % 2^(p+1) = x % 2^p + 2^p := by rw [low_succ, hb]; rfl
      simp [put, Code.fixedSafe, Code.fixedEval, Code.safeReadOnly, Code.evalNat,
        hbit, hb, hz, u, low, v, pl, addressOp, addressOpFits, hlo]
  have ur (k : Reg) (hk : k ≠ 9) : u.reg k = z.reg k := Function.update_of_ne hk ..
  have up : u.reg 8 = p := (ur 8 (by decide)).trans before.used
  have uq : u.reg 7 = dst+q := (ur 7 (by decide)).trans before.address
  have u1 : u.reg 1 = 1 := (ur 1 (by decide)).trans h.one
  have u0 : u.reg 0 = 0 := (ur 0 (by decide)).trans h.zero
  have uw : u.reg 2 = w := (ur 2 (by decide)).trans h.width
  have upow : u.reg 10 = 2^p := (ur 10 (by decide)).trans pl
  have uv : u.reg 9 = x % 2^(p+1) := by simp [u]
  have um : u.mem = image words original dst q := before.memory
  have hinc : p+1 < 2^w := by omega
  let y := next.fixedEval env u
  have finish : next.fixedSafe w env u ∧ At w dst words original (j+1) y := by
    by_cases last : p+1 = w
    · have mr : (j+1)%w = 0 := by rw [← Nat.mod_add_mod j w 1, show j%w+1 = w from last, Nat.mod_self]
      have qr : (j+1)/w = q+1 := Nat.succ_div_of_mod_eq_zero mr
      have full : words q % 2^w = words q := Nat.mod_eq_of_lt wordFit
      have addrFit : dst+q+1 < 2^w := by rw [qr] at room; omega
      constructor
      · simp (config := {decide := true}) [next, flush, Code.block, Code.fixedSafe, Code.fixedEval,
          Code.safeReadOnly, Code.evalNat, addressOp, addressOpFits, up, u1, uw, uq, last, addrFit, hwidth]
      · constructor <;> simp (config := {decide := true}) [y, next, flush, Code.block, Code.fixedEval,
          Code.evalNat, addressOp, up, u1, u0, uw, uq, uv, um, mr, qr, last, full, Nat.add_assoc, x, image_succ, Nat.mod_one]
    · have hp' : p+1 < w := by omega
      have mr : (j+1)%w = p+1 := by
        rw [← Nat.mod_add_mod j w 1, Nat.mod_eq_of_lt hp']
      have qr : (j+1)/w = q := Nat.succ_div_of_mod_ne_zero (by rw [mr]; omega)
      have grow : 2^p+2^p < 2^w := by
        have hh := Nat.pow_lt_pow_right (by decide : 1 < 2) hp'
        rw [pow_succ] at hh
        omega
      constructor
      · simp (config := {decide := true}) [next, Code.fixedSafe, Code.fixedEval,
          Code.safeReadOnly, Code.evalNat, addressOp, addressOpFits, up, u1, uw, upow, last, hinc, grow]
      · constructor <;> simp (config := {decide := true}) [y, next, Code.fixedEval, Code.evalNat,
          addressOp, up, u1, uw, uq, uv, um, mr, qr, upow, last, pow_succ, Nat.mul_two, x]
  have safe : (emit d).fixedSafe w env z := by
    change (put d).fixedSafe w env z ∧ next.fixedSafe w env ((put d).fixedEval env z)
    exact ⟨prep.1,prep.2 ▸ finish.1⟩
  apply (Code.runFixed (emit d) pub macros s m safe).mono le_rfl
  rintro _ rfl
  have protect (k : Reg) (hk : k.val < 7) :
      ((emit d).fixedEval env z).reg k = z.reg k :=
    (emit d).fixedEval_protected env z (lo := 7) (by rfl) k hk
  refine ⟨⟨(protect 0 (by decide)).trans h.zero, (protect 1 (by decide)).trans h.one,
    (protect 2 (by decide)).trans h.width, (protect 3 (by decide)).trans h.source,
    (protect 4 (by decide)).trans h.length, (protect 5 (by decide)).trans h.destination,
    (protect 6 (by decide)).trans h.index⟩,?_,?_⟩
  · change At w dst words original (j+1) (next.fixedEval env ((put d).fixedEval env z))
    rw [prep.2]
    exact finish.2
  · change (next.fixedEval env ((put d).fixedEval env z)).reg 11 = (s 11).val
    rw [prep.2]
    have keep : u.reg 11 = (s 11).val := ur 11 (by decide)
    by_cases last : p+1=w <;>
      simp (config := {decide := true}) [next, flush, Code.block, Code.fixedEval, Code.evalNat,
        addressOp, up, u1, uw, last, keep]

end RoutingISA.CompactWrite

end BorderVNP
end Computability
end OAI
