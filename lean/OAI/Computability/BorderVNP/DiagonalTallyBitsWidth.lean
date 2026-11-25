import OAI.Computability.BorderVNP.DiagonalTallyBits

/-! # Native validation of the bit width for a tally broadcast -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyBits

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA
open DiagonalResidueRAM (TraceOK effect effect_runs)

/-- Width zero takes the short branch. Positive width performs a highest-bit test. -/
def widthTicks (width : ℕ) := if width = 0 then 3 else 6

/-- The physical width test accepts every fitting width, preserving every register
other than the two scratch values used for the high-bit calculation. -/
theorem widthGuard_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (hone : (s 63).val = 1) (hfit : (s 52).val ≤ w) :
    ∃ es t, Runs pub mac widthGuard s m es t m ∧ TraceOK es [] (widthTicks (s 52).val) ∧
      Preserves [60,61] s t := by
  let a := Function.update s (60 : Reg) (0 : Word w)
  have init : Runs pub mac (.constant 60 0) s m [tick w] a m := Runs.localStep _ rfl rfl
  by_cases hz : (s 52).val = 0
  · have eq : a 52 = a 60 := by apply Fin.ext; simp [a,hz]
    have tail : Runs pub mac (.ifEq 52 60 .nop (.seq (.binary .sub 61 52 63) (.seq (.binary .shiftLeft 61 63 61)
      (.ifEq 61 60 .reject .nop)))) a m [tick w,tick w] a m :=
      .ifEq (by rw [ite_eq_left eq]; exact Runs.localStep _ rfl rfl)
    refine ⟨_,a,.seq init tail,?_,?_⟩
    · simp [TraceOK,tick,widthTicks,hz]
    · intro j hj
      simp at hj
      simp [a,hj]
  · have neq : a 52 ≠ a 60 := fun he => hz (by simpa [a] using congrArg Fin.val he)
    let y := Function.update a (61 : Reg) (a 52-a 63)
    let z := Function.update y (61 : Reg) (BinaryOp.shiftLeft.eval (y 63) (y 61))
    have sub : Runs pub mac (.binary .sub 61 52 63) a m [tick w] y m := Runs.localStep _ rfl rfl
    have shift : Runs pub mac (.binary .shiftLeft 61 63 61) y m [tick w] z m := Runs.localStep _ rfl rfl
    have hle : s 63 ≤ s 52 := by change (s 63).val ≤ (s 52).val; omega
    have sy : (y 61).val = (s 52).val-1 := by simp [y,a,Fin.sub_val_of_le hle,hone]
    have sy63 : (y 63).val = 1 := by simpa [y,a,Function.update] using hone
    have hk : (s 52).val-1 < w := by omega
    have hpow : 2 ^ ((s 52).val-1) < 2^w := Nat.pow_lt_pow_right Nat.one_lt_two hk
    have high : (z 61).val = 2 ^ ((s 52).val-1) := by
      simp [z,BinaryOp.eval,sy,sy63,hk,Nat.shiftLeft_eq,Nat.mod_eq_of_lt hpow]
    have zero : (z 60).val = 0 := by simp [z,y,a,Function.update]
    have test : z 61 ≠ z 60 := fun he => by rw [he,zero] at high; exact (Nat.ne_of_gt (Nat.two_pow_pos _)) high.symm
    have yes : Runs pub mac (.ifEq 61 60 .reject .nop) z m [tick w,tick w] z m :=
      .ifEq (by rw [ite_eq_right test]; exact Runs.localStep _ rfl rfl)
    have main := Runs.ifEq (s := a) (x := 52) (y := 60) (a := .nop)
      (b := .seq (.binary .sub 61 52 63) (.seq (.binary .shiftLeft 61 63 61) (.ifEq 61 60 .reject .nop)))
      (by simpa only [ite_eq_right neq] using Runs.seq sub (Runs.seq shift yes))
    refine ⟨_,z,.seq init main,?_,?_⟩
    · simp [TraceOK,tick,widthTicks,hz]
    · intro j hj
      simp at hj
      simp [z,y,a,Function.update,hj]

end DiagonalTallyBits

end BorderVNP
end Computability
end OAI
