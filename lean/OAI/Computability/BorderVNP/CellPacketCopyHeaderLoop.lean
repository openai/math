import OAI.Computability.BorderVNP.CellPacketEncodeInner

/-! # Reading a little-endian length field on the physical team machine

The descending source cursor addresses the most significant unread digit. The
accumulator at that cursor is the length divided by the corresponding power of two.
Thus every intermediate integer is at most the final payload length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacketCopy

open VPVNP.BurstRAM CellPacketEncode

/-- One backwards step reads the next bit and appends it to the accumulator. -/
def headerStep : Code := .block [.binary .sub 21 21 1, .load 16 21,
  .binary .add 22 22 22, .binary .add 22 22 16]

/-- A length scan writes only the data temporary, backwards cursor and accumulator. -/
def HeaderFixed (s t : Reg → ℕ) : Prop := ∀ j, j ≠ 16 → j ≠ 21 → j ≠ 22 → t j = s j

private theorem next_digit (n k : ℕ) :
    n / 2^(k+1) + n / 2^(k+1) + (n.testBit k).toNat = n / 2^k := by
  have bit : (n.testBit k).toNat = n / 2^k % 2 := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases h : n / 2^k % 2 = 1 <;> simp [h]
    omega
  rw [bit, pow_succ, ← Nat.div_div_eq_div_mul]
  omega

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem headerStep_run (s : Bank w) (m : Memory w) (n k : ℕ)
    (c : readings s 1 = 1) (cursor : readings s 21 = readings s 14 + (k+1))
    (acc : readings s 22 = n / 2^(k+1))
    (source : readings m (readings s 14 + k) = (n.testBit k).toNat) (fit : n < 2^w) :
    BoundedRun pub macros headerStep s m 4 (fun z => HeaderFixed (readings s) z.reg ∧
      z.reg 21 = readings s 14 + k ∧ z.reg 22 = n / 2^k ∧ z.mem = readings m) := by
  have cur : readings s 21 - readings s 1 = readings s 14 + k := by omega
  have subfit : readings s 1 ≤ readings s 21 := by omega
  have add := next_digit n k
  have small := (Nat.div_le_self n (2^k)).trans_lt fit
  have safe : headerStep.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [headerStep, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp, NatState.ofWords,
      cur, subfit, acc, source, add, small]
    omega
  apply (headerStep.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  refine ⟨fun j h16 h21 h22 => ?_, ?_, ?_, rfl⟩ <;>
    simp (config := {decide := true}) [headerStep, Code.block, Code.fixedEval, Code.evalNat,
      NatState.ofWords, addressOp, *]

/-- Starting at offset `k` with the upper digits already read, the loop loads precisely
those `k` remaining digits and returns the full length without modifying memory. -/
theorem headerLoop_run (s : Bank w) (m : Memory w) (n k : ℕ)
    (one : readings s 1 = 1) (cursor : readings s 21 = readings s 14 + k)
    (acc : readings s 22 = n / 2^k) (fit : n < 2^w)
    (source : ∀ i : Fin k, readings m (readings s 14 + i.val) = (n.testBit i.val).toNat) :
    BoundedRun pub macros (.whileLt 14 21 headerStep) s m (5*k+1) (fun z =>
      HeaderFixed (readings s) z.reg ∧ z.reg 22 = n ∧ z.mem = readings m) := by
  induction k generalizing s m with
  | zero =>
    have same : readings s 21 = readings s 14 := by simpa using cursor
    apply loop_done (show ¬ s 14 < s 21 from not_lt_of_ge same.le)
    exact ⟨fun _ _ _ _ => rfl, by simpa [NatState.ofWords] using acc, rfl⟩
  | succ k ih =>
    obtain ⟨es,t,mt,body,cost,regs,cur,acc',hm⟩ := headerStep_run (pub := pub) (macros := macros)
      s m n k one cursor acc (source ⟨k, by omega⟩) fit
    have hs : readings t 14 = readings s 14 := regs 14 (by decide) (by decide) (by decide)
    change readings t 21 = readings s 14 + k at cur
    change readings mt = readings m at hm
    obtain ⟨fs,z,mz,loop,cost',regs',total,mem⟩ := ih t mt
      ((regs 1 (by decide) (by decide) (by decide)).trans one) (by rw [hs,cur]) acc'
      (fun i => by rw [hm,hs]; exact source i.castSucc)
    refine ⟨_,z,mz,.whileStep (show readings s 14 < readings s 21 by omega) body loop, ?_,
      fun j a b c => (regs' j a b c).trans (regs j a b c), total, mem.trans hm⟩
    change 1 + traceCost (es ++ fs) ≤ _
    rw [show traceCost (es ++ fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
    omega

end RoutingISA.CellPacketCopy

end BorderVNP
end Computability
end OAI
