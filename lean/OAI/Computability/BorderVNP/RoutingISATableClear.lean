import OAI.Computability.BorderVNP.RoutingISATableSetup

/-! # Clearing the upper and lower triangles of the pair-width table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Overwrite the first `n` words of the given interval with zero. -/
def zeroPrefix (base n : ℕ) (mem : ℕ → ℕ) (a : ℕ) : ℕ :=
  if base ≤ a ∧ a < base+n then 0 else mem a

/-- One native zero store extends the cleared prefix by precisely one word. -/
theorem extend_zeroPrefix (base n : ℕ) (mem : ℕ → ℕ) :
    Function.update (zeroPrefix base n mem) (base+n) 0 = zeroPrefix base (n+1) mem := by
  funext a
  by_cases h : a = base+n
  · simp [h,zeroPrefix]
  · rw [Function.update_of_ne h]
    have he : (base ≤ a ∧ a < base+n) ↔ (base ≤ a ∧ a < base+(n+1)) := by omega
    simp only [zeroPrefix, he]

/-- The entire square pair-width array is zeroed by native word stores. Every
other shared-memory address, including all record and frame words, is preserved. -/
theorem run_clearPairWidths {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : TableLayout) (al : l.Allocated w) (s : Bank w) (m : Memory w)
    (ready : l.ready (.ofWords s m)) :
    BoundedRun pub macros clearPairWidths s m (4*l.teams^2+2)
      (fun z => l.ready z ∧ z.mem = zeroPrefix l.widths (l.teams^2) (readings m)) := by
  let b := Code.block [.binary .add 14 8 13, .store 14 0, .binary .add 13 13 1]
  let P (i : ℕ) (z : NatState) := l.ready z ∧ z.reg 13 = i ∧ z.mem = zeroPrefix l.widths i (readings m)
  have regs (i : ℕ) (z : NatState) (h : P i z) : z.reg 13 = i ∧ z.reg 4 = l.teams^2 :=
    ⟨h.2.1, (h.1 4 (by decide)).trans (pow_two _).symm⟩
  have step (i : ℕ) (hi : i < l.teams^2) (u : Bank w) (mu : Memory w)
      (h : P i (.ofWords u mu)) : BoundedRun pub macros b u mu 3 (P (i+1)) := by
    let z := NatState.ofWords u mu
    have h0 : z.reg 0 = 0 := h.1 0 (by decide)
    have h1 : z.reg 1 = 1 := h.1 1 (by decide)
    have h8 : z.reg 8 = l.widths := h.1 8 (by decide)
    have h13 : z.reg 13 = i := h.2.1
    have fit : l.widths+i < 2^w := al.address (l.contains_offset (a := .widths) hi)
    have inc : i+1 < 2^w := Nat.lt_of_le_of_lt hi al.square
    have hs : b.fixedSafe w (readings pub) z := by
      simp (config := { decide := true }) [b, Code.block, Code.fixedSafe, Code.fixedEval,
        Code.safeReadOnly, Code.evalNat, addressOpFits, h1,h8,h13,fit,inc]
    apply (b.runFixed pub macros u mu hs).mono (by decide)
    rintro y rfl
    refine ⟨TableLayout.ready_fixed h.1 (c := b) (by decide) _, ?_, ?_⟩
    · change (b.fixedEval (readings pub) z).reg 13 = i+1
      simp (config := { decide := true }) [b, Code.block, Code.fixedEval, Code.evalNat, addressOp,h13,h1]
    · change (b.fixedEval (readings pub) z).mem = _
      simp (config := { decide := true }) [b, Code.block, Code.fixedEval, Code.evalNat, addressOp,h8,h13,h0]
      rw [show z.mem = _ from h.2.2, extend_zeroPrefix]
  have init := (Code.copy 13 0).runFixed pub macros s m trivial
  have run := init.seq (b := .whileLt 13 4 b) (t := (l.teams^2-0)*(3+1)+1) (Q := P (l.teams^2))
    (fun u mu hu => run_counted_loop pub macros 13 4 b (l.teams^2) 3 P regs step 0 (Nat.zero_le _) u mu (by
      rw [hu]
      refine ⟨TableLayout.ready_fixed ready (c := .copy 13 0) (by decide) _, ?_, ?_⟩
      · simp [Code.fixedEval,Code.evalNat, show (NatState.ofWords s m).reg 0 = 0 from ready 0 (by decide)]
      · funext a
        simp [zeroPrefix, Code.fixedEval, NatState.ofWords]))
  exact run.mono (by change 1+(l.teams^2-0)*(3+1)+1 ≤ _; omega) fun _ h => ⟨h.1,h.2.2⟩

end RoutingISA

end BorderVNP
end Computability
end OAI
