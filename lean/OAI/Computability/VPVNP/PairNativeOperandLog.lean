import OAI.Computability.VPVNP.PairNativeGeometryArithmetic

/-!
# Logarithmic operands inside the native pair burst

Repeated floor division by two needs no increment of the operand. For a
ceiling logarithm at `x > 1`, the same loop starts at `x-1` with counter
one. This covers the largest word as well as zero and powers of two.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeOperands.Log

open BurstRAM PrivateRAM PrimedInputRAM PrimedStackRAM

variable {w : ℕ}
/-- The twelve-register instruction flows used to evaluate binary logarithms inside a native
operand computation. -/
abbrev Code := Flow 12 11

private def step : Code := .seq (.line (.binary .div 2 2 1)) (.line (.binary .add 3 3 0))
private def loop : Code := .whileLt 0 2 step

private theorem loop_run (pub : Fin 11 → Word w) (state : Word w) (m : Memory w)
    (x c : ℕ) (rs : Regs w 12) (h1 : (rs 0).val = 1) (h2 : (rs 1).val = 2)
    (hx : (rs 2).val = x) (hc : (rs 3).val = c) (hfit : c+Nat.log 2 x < 2^w) :
    ∃ out, Flow.Exec pub state loop rs m (List.replicate (3*Nat.log 2 x+1) .tick) out m ∧
      (out 3).val = c+Nat.log 2 x ∧ ∀ i : Fin 12, i ≠ 2 → i ≠ 3 → out i = rs i := by
  induction x using Nat.strong_induction_on generalizing c rs with
  | h x ih =>
    by_cases small : x < 2
    · rw [Nat.log_of_lt small, Nat.mul_zero, Nat.zero_add,Nat.add_zero]
      exact ⟨rs,.whileDone (by change ¬ (rs 0).val < (rs 2).val; omega),hc,fun _ _ _ => rfl⟩
    · have hlog := Nat.log_of_one_lt_of_le Nat.one_lt_two (show 2 ≤ x by omega)
      let a := Function.update rs (2 : Fin 12) (BinaryOp.div.eval (rs 2) (rs 1))
      let b := Function.update a (3 : Fin 12) (BinaryOp.add.eval (a 3) (a 0))
      have keep (i : Fin 12) (h₂ : i ≠ 2) (h₃ : i ≠ 3) : b i = rs i := by
        simp [b,a,Function.update_of_ne h₂,Function.update_of_ne h₃]
      have hbx : (b 2).val = x/2 := by
        change ((rs 2).val/(rs 1).val) % (2^w) = x/2
        rw [Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt (rs 2).isLt),hx,h2]
      have hbc : (b 3).val = c+1 := by
        change ((a 3).val+(a 0).val) % (2^w) = c+1
        rw [show (a 3).val = c by simpa [a,Function.update_apply] using hc,
          show (a 0).val = 1 by simpa [a,Function.update_apply] using h1,Nat.mod_eq_of_lt (by omega)]
      have body : Flow.Exec pub state step rs m [.tick,.tick] b m :=
        Flow.Exec.seq (.line (rs' := a) rfl) (.line (rs' := b) rfl)
      obtain ⟨out,rest,value,frame⟩ := ih (x/2) (by omega) (c+1) b
        ((congrArg Fin.val (keep _ (by decide) (by decide))).trans h1)
        ((congrArg Fin.val (keep _ (by decide) (by decide))).trans h2) hbx hbc (by omega)
      refine ⟨out,?_,by omega,fun i h₂ h₃ => (frame i h₂ h₃).trans (keep i h₂ h₃)⟩
      rw [show 3*Nat.log 2 x+1 = (2+(3*Nat.log 2 (x/2)+1))+1 by omega,
        List.replicate_succ,List.replicate_add]
      exact .whileStep (by change (rs 0).val < (rs 2).val; omega) body rest

private theorem ceiling_eq (x : ℕ) (hx : 1 < x) : Nat.clog 2 x = 1+Nat.log 2 (x-1) := by
  apply Nat.le_antisymm
  · apply Nat.clog_le_of_le_pow
    rw [Nat.add_comm 1]
    have h := Nat.lt_pow_succ_log_self Nat.one_lt_two (x-1)
    omega
  · have h := Nat.pow_log_le_self 2 (by omega : x-1 ≠ 0)
    have hlt : Nat.log 2 (x-1) < Nat.clog 2 x := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).2 (by omega)
    omega

private def init : Code := straight (.constant 0 1) [.constant 1 2,.constant 3 0]

private def preCeil : Code := .seq (.line (.binary .sub 2 2 0)) (.line (.copy 3 0))

/-- Compute the floor or ceiling binary logarithm of register 2 in register 3 by repeated
halving. For a ceiling logarithm above one the loop starts from one less than the operand
and counts from one. -/
def program (ceil : Bool) : Code := .seq init (if ceil then
  .ifLt 0 2 (.seq preCeil loop) (.line (.constant 3 0)) else loop)

/-- The result occupies register three. Registers four and above, including
the word-width register, keep their original contents. -/
theorem run (ceil : Bool) (pub : Fin 11 → Word w) (state : Word w) (m : Memory w)
    (rs : Regs w 12) (hw : 2 ≤ w) :
    ∃ ticks ≤ 10*(w+1)+10, ∃ out,
      Flow.Exec pub state (program ceil) rs m (List.replicate ticks .tick) out m ∧
      (out 3).val = (if ceil then Nat.clog 2 (rs 2).val else Nat.log 2 (rs 2).val) ∧
      ∀ i : Fin 12, 4 ≤ i.val → out i = rs i := by
  let x := (rs 2).val
  let s := Function.update (Function.update (Function.update rs (0 : Fin 12) (Fin.ofNat (2^w) 1))
    (1 : Fin 12) (Fin.ofNat (2^w) 2)) (3 : Fin 12) (Fin.ofNat (2^w) 0)
  have hinit : Flow.Exec pub state init rs m (List.replicate 3 .tick) s m :=
    (Flow.once_sound pub state false _ rs m rfl).1
  have hfour : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  have h1 : (s 0).val = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (s 1).val = 2 := Nat.mod_eq_of_lt (by omega)
  have hx : (s 2).val = x := rfl
  have h0 : (s 3).val = 0 := rfl
  have hxlt : x < 2^w := (rs 2).isLt
  have hclog : Nat.clog 2 x ≤ w := Nat.clog_le_of_le_pow hxlt.le
  have hlog := (Nat.log_le_clog 2 x).trans hclog
  have hfit : w < 2^w := Nat.lt_two_pow_self
  have frame (i : Fin 12) (hi : 4 ≤ i.val) : s i = rs i := by
    have h₀ : i ≠ 0 := fun h => by subst i; contradiction
    have h₁ : i ≠ 1 := fun h => by subst i; contradiction
    have h₃ : i ≠ 3 := fun h => by subst i; contradiction
    simp [s,Function.update_of_ne h₀,Function.update_of_ne h₁,Function.update_of_ne h₃]
  have hne (i : Fin 12) (hi : 4 ≤ i.val) : i ≠ 2 ∧ i ≠ 3 := by
    constructor <;> intro he <;> subst i <;> contradiction
  cases ceil with
  | false =>
    obtain ⟨out,body,hv,hk⟩ := loop_run pub state m x 0 s h1 h2 hx h0 (by omega)
    exact ⟨_,by omega,out,PairNativeGeometry.seqTicks hinit body,by simpa using hv,
      fun i hi => (hk i (hne i hi).1 (hne i hi).2).trans (frame i hi)⟩
  | true =>
    by_cases small : x ≤ 1
    · let out := Function.update s (3 : Fin 12) (Fin.ofNat (2^w) 0)
      have branch : Flow.Exec pub state (.ifLt 0 2 (.seq preCeil loop) (.line (.constant 3 0)))
          s m (List.replicate 2 .tick) out m :=
        .ifLtNo (by change ¬ (s 0).val < (s 2).val; omega) (.line rfl)
      exact ⟨_,by omega,out,PairNativeGeometry.seqTicks hinit branch,
        by change 0 = Nat.clog 2 x; rw [Nat.clog_of_right_le_one small],
        fun i hi => (Function.update_of_ne (hne i hi).2 ..).trans (frame i hi)⟩
    · let t := Function.update s (2 : Fin 12) (BinaryOp.sub.eval (s 2) (s 0))
      let u := Function.update t (3 : Fin 12) (t 0)
      have adjust : Flow.Exec pub state preCeil s m (List.replicate 2 .tick) u m :=
        Flow.Exec.seq (.line (rs' := t) rfl) (.line (rs' := u) rfl)
      have hu (i : Fin 12) (h₂ : i ≠ 2) (h₃ : i ≠ 3) : u i = s i := by
        simp [u,t,Function.update_of_ne h₂,Function.update_of_ne h₃]
      have hux : (u 2).val = x-1 := by
        change (s 2 - s 0).val = x-1
        rw [Fin.sub_val_of_le (by change (s 0).val ≤ (s 2).val; omega),h1,hx]
      have hceil := ceiling_eq x (by omega)
      obtain ⟨out,body,hv,hk⟩ := loop_run pub state m (x-1) 1 u
        ((congrArg Fin.val (hu _ (by decide) (by decide))).trans h1)
        ((congrArg Fin.val (hu _ (by decide) (by decide))).trans h2) hux h1 (by omega)
      have branch := Flow.Exec.ifLtYes (b := (Flow.line (.constant 3 0) : Code))
        (show s 0 < s 2 by change (s 0).val < (s 2).val; omega) (PairNativeGeometry.seqTicks adjust body)
      change Flow.Exec pub state _ s m (List.replicate ((2+(3*Nat.log 2 (x-1)+1))+1) .tick) out m at branch
      exact ⟨_,by omega,out,PairNativeGeometry.seqTicks hinit branch,hv.trans hceil.symm,
        fun i hi => ((hk i (hne i hi).1 (hne i hi).2).trans (hu i (hne i hi).1 (hne i hi).2)).trans (frame i hi)⟩

end PairSimulation.NativeOperands.Log

end VPVNP
end Computability
end OAI
