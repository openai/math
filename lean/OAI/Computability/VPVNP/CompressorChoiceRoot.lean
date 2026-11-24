import OAI.Computability.VPVNP.MotifAdmission
import OAI.Computability.VPVNP.PrimedInputRAMOnce

/-!
# Native computation of the number of motif copies

Binary search on the integer interval from zero to the demand energy computes
the least integer whose square, multiplied by the fixed denominator, reaches
that energy. The search runs the same native instruction table for all inputs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RepetitionRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w k : ℕ}

/-- Registers 0 and 1 contain the numerator and denominator. Registers 2 and
3 hold the inclusive search interval, 4 and 5 hold one and two, and 6 and 7
hold the midpoint and its test score. -/
def body : Flow 8 k :=
  .seq (.line (.binary .add 6 2 3)) <|
  .seq (.line (.binary .div 6 6 5)) <|
  .seq (.line (.binary .mul 7 6 6)) <|
  .seq (.line (.binary .mul 7 7 1)) <|
  .ifLt 7 0 (.line (.binary .add 2 6 4)) (.line (.copy 3 6))

/-- Bisection includes the zero-energy case, for which the loop has no iterations. -/
def root : Flow 8 k :=
  .seq (.line (.constant 2 0)) <|
  .seq (.line (.copy 3 0)) <|
  .seq (.line (.constant 4 1)) <|
  .seq (.line (.constant 5 2)) (.whileLt 2 3 body)

private def update (rs : Regs w 8) (i : Fin 8) (v : Word w) := Function.update rs i v

private theorem bin (pub : Fin k → Word w) (s : Word w) (m : Memory w) (rs : Regs w 8)
    (op : BinaryOp) (dst x y : Fin 8) :
    Flow.Exec pub s (.line (.binary op dst x y)) rs m [.tick] (update rs dst (op.eval (rs x) (rs y))) m :=
  .line rfl

private theorem next (pub : Fin k → Word w) (s : Word w) (m : Memory w) (rs : Regs w 8)
    {n d lo hi : ℕ} (hn : (rs 0).val = n) (hd : (rs 1).val = d)
    (hlo : (rs 2).val = lo) (hhi : (rs 3).val = hi) (h₁ : (rs 4).val = 1) (h₂ : (rs 5).val = 2)
    (hlt : lo < hi) (hsum : lo + hi < 2^w) (hscore : hi^2 * d < 2^w) :
    let mid := (lo + hi) / 2
    let below := mid^2 * d < n
    ∃ out, Flow.Exec pub s body rs m (List.replicate 6 .tick) out m ∧
      (out 0).val = n ∧ (out 1).val = d ∧ (out 4).val = 1 ∧ (out 5).val = 2 ∧
      (out 2).val = (if below then mid + 1 else lo) ∧
      (out 3).val = (if below then hi else mid) := by
  dsimp only
  let mid := (lo+hi)/2
  let t := update rs 6 (rs 2 + rs 3)
  let a := update t 6 (BinaryOp.div.eval (t 6) (t 5))
  let b := update a 7 (a 6 * a 6)
  let c := update b 7 (b 7 * b 1)
  have hm : mid < hi := by dsimp [mid]; omega
  have hav : (a 6).val = mid := by
    simp (config := {decide := true}) [a,t,update,BinaryOp.eval,
      Fin.val_add,hlo,hhi,h₂,Nat.mod_eq_of_lt hsum,Nat.mod_eq_of_lt (hm.trans (hhi ▸ (rs 3).isLt)),mid]
  have hcv : (c 7).val = mid^2 * d := by
    have hfit := (Nat.mul_le_mul_right d (Nat.pow_le_pow_left hm.le 2)).trans_lt hscore
    have hab : b 1 = rs 1 := by simp (config := {decide := true}) [b,a,t,update,Function.update]
    change ((b 7 * b 1) : Word w).val = _
    rw [hab]
    change ((a 6 * a 6) * rs 1).val = _
    rw [Fin.val_mul, Fin.val_mul, Nat.mod_mul_mod, hav, hd, ← pow_two, Nat.mod_eq_of_lt hfit]
  have common (i : Fin 8) (hi₆ : i ≠ 6) (hi₇ : i ≠ 7) : c i = rs i := by
    simp [c,b,a,t,update,Function.update_of_ne hi₆, Function.update_of_ne hi₇]
  have midReg : (c 6).val = mid := by simpa (config := {decide := true}) [c,b,update,Function.update] using hav
  have prefixExec (out : Regs w 8)
      (h : Flow.Exec pub s (.ifLt 7 0 (.line (.binary .add 2 6 4)) (.line (.copy 3 6)))
        c m [.tick,.tick] out m) : Flow.Exec pub s body rs m (List.replicate 6 .tick) out m :=
    .seq (bin pub s m rs .add 6 2 3) (.seq (bin pub s m t .div 6 6 5)
      (.seq (bin pub s m a .mul 7 6 6) (.seq (bin pub s m b .mul 7 7 1) h)))
  by_cases hz : mid^2 * d < n
  · have ht : c 7 < c 0 := by rw [Fin.lt_def, hcv, common 0 (by decide) (by decide), hn]; exact hz
    let out := update c 2 (c 6 + c 4)
    have hnext : (out 2).val = mid+1 := by
      change (c 6 + c 4).val = _
      rw [Fin.val_add,midReg,common 4 (by decide) (by decide),h₁,Nat.mod_eq_of_lt
        ((show mid+1 ≤ hi by omega).trans_lt (hhi ▸ (rs 3).isLt))]
    refine ⟨out, prefixExec out (.ifLtYes ht (bin pub s m c .add 2 6 4)), ?_⟩
    change _ ∧ _ ∧ _ ∧ _ ∧ (out 2).val = (if mid^2*d < n then mid+1 else lo) ∧
      (out 3).val = (if mid^2*d < n then hi else mid)
    rw [ite_eq_left hz, ite_eq_left hz, hnext]
    simp (config := {decide := true}) [out, update, common, hn, hd, hhi, h₁, h₂]
  · have ht : ¬ c 7 < c 0 := by rw [Fin.lt_def,hcv,common 0 (by decide) (by decide),hn]; exact hz
    let out := update c 3 (c 6)
    refine ⟨out, prefixExec out (.ifLtNo ht (.line rfl)), ?_⟩
    simp (config := {decide := true}) [out,update,common, hn,hd,hlo,h₁,h₂,hz,midReg,mid]

private theorem search (pub : Fin k → Word w) (s : Word w) (m : Memory w) {n d : ℕ}
    (hdpos : 0 < d) (hfit : 2*n < 2^w) (hsq : n^2 * d < 2^w) (steps : ℕ) :
    ∀ (rs : Regs w 8), (rs 0).val = n → (rs 1).val = d → (rs 4).val = 1 → (rs 5).val = 2 →
      (rs 2).val ≤ MotifAdmission.ceilRoot n d → MotifAdmission.ceilRoot n d ≤ (rs 3).val →
      (rs 3).val ≤ n → (rs 3).val - (rs 2).val < 2^steps →
      ∃ count out, Flow.Exec pub s (.whileLt 2 3 body) rs m (List.replicate count .tick) out m ∧
        count ≤ 7*steps+1 ∧ (out 2).val = MotifAdmission.ceilRoot n d := by
  induction steps with
  | zero =>
    intro rs _ _ _ _ hlo hhi _ hspan
    have heq : rs 2 = rs 3 := Fin.ext (by simp at hspan; omega)
    exact ⟨1, rs, .whileDone (by simp [heq]), by simp, by simpa [heq] using Nat.le_antisymm hlo (heq ▸ hhi)⟩
  | succ steps ih =>
    intro rs hn hd h₁ h₂ hlo hhi hmax hspan
    by_cases ht : rs 2 < rs 3
    · let lo := (rs 2).val
      let hi := (rs 3).val
      let mid := (lo+hi)/2
      have hlt : lo < hi := ht
      have hsum : lo+hi < 2^w := by dsimp [lo,hi]; omega
      have hscore := (Nat.mul_le_mul_right d (Nat.pow_le_pow_left hmax 2)).trans_lt hsq
      obtain ⟨out, hrun, hn', hd', h₁', h₂', ha,hb⟩ := next pub s m rs hn hd rfl rfl h₁ h₂ hlt hsum hscore
      change (out 2).val = (if mid^2*d < n then mid+1 else lo) at ha
      change (out 3).val = (if mid^2*d < n then hi else mid) at hb
      have hbounds : (out 2).val ≤ MotifAdmission.ceilRoot n d ∧ MotifAdmission.ceilRoot n d ≤ (out 3).val ∧
          (out 3).val ≤ n ∧ (out 3).val - (out 2).val < 2^steps := by
        have hs : hi-lo < 2^steps * 2 := by simpa [lo, hi, pow_succ] using hspan
        change lo ≤ _ at hlo
        change _ ≤ hi at hhi
        change hi ≤ n at hmax
        by_cases hz : mid^2*d < n
        · have hr : mid < MotifAdmission.ceilRoot n d :=
            lt_of_not_ge fun h => (Nat.not_le_of_gt hz) ((MotifAdmission.ceilRoot_le_iff _ _ _ hdpos).mp h)
          simp only [hz, ↓reduceIte] at ha hb
          dsimp [mid] at *
          omega
        · have hr := (MotifAdmission.ceilRoot_le_iff n d mid hdpos).mpr (Nat.le_of_not_gt hz)
          simp only [hz, ↓reduceIte] at ha hb
          dsimp [mid] at *
          omega
      obtain ⟨t,last,hloop,hlen,he⟩ := ih out hn' hd' h₁' h₂' hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
      refine ⟨7+t,last,?_,by omega,he⟩
      simpa only [List.replicate_add, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append] using Flow.Exec.whileStep ht hrun hloop
    · have heq : (rs 2).val = MotifAdmission.ceilRoot n d := Nat.le_antisymm hlo (hhi.trans (Fin.not_lt.mp ht))
      exact ⟨1,rs,.whileDone ht,by omega,heq⟩

/-- Complete computation of the integral ceiling test with at most seven
instructions per binary digit of the numerator, including all loop tests.
Every recorded event is a private deterministic tick. -/
theorem root_exec (pub : Fin k → Word w) (s : Word w) (m : Memory w) (rs : Regs w 8)
    (n d : ℕ) (hn : (rs 0).val = n) (hd : (rs 1).val = d) (hdpos : 0 < d)
    (htwo : 2 < 2^w) (hsum : 2*n < 2^w) (hsq : n^2*d < 2^w) :
    ∃ count out, Flow.Exec pub s root rs m (List.replicate count .tick) out m ∧
      count ≤ 7*n.size+5 ∧ (out 2).val = MotifAdmission.ceilRoot n d := by
  let a := update rs 2 0
  let b := update a 3 (a 0)
  let c := update b 4 (Fin.ofNat (2^w) 1)
  let t := update c 5 (Fin.ofNat (2^w) 2)
  have hr : MotifAdmission.ceilRoot n d ≤ n := (MotifAdmission.ceilRoot_le_iff _ _ _ hdpos).mpr
    ((Nat.le_self_pow (by decide) n).trans (Nat.le_mul_of_pos_right _ hdpos))
  have one : 1 % 2^w = 1 := Nat.mod_eq_of_lt (by omega)
  have two : 2 % 2^w = 2 := Nat.mod_eq_of_lt htwo
  have hn' : (t 0).val = n := by simp (config := {decide := true}) [t,c,b,a,update,Function.update, hn]
  have hd' : (t 1).val = d := by simp (config := {decide := true}) [t,c,b,a,update,Function.update, hd]
  have hlo : (t 2).val = 0 := by simp (config := {decide := true}) [t,c,b,a,update,Function.update]
  have hhi : (t 3).val = n := by simp (config := {decide := true}) [t,c,b,a,update,Function.update,hn]
  have h₁ : (t 4).val = 1 := by simpa (config := {decide := true}) [t,c,update,Function.update] using one
  have h₂ : (t 5).val = 2 := by simpa [t,update] using two
  obtain ⟨count,out,he,hlen,hroot⟩ := search pub s m hdpos hsum hsq n.size t hn' hd' h₁ h₂
    (hlo ▸ Nat.zero_le _) (hhi ▸ hr) (hhi ▸ le_rfl) (by simpa [hhi,hlo] using Nat.lt_size_self n)
  refine ⟨4+count,out,?_,by omega,hroot⟩
  have init₁ : Flow.Exec pub s (.line (.constant 2 0)) rs m [.tick] a m := .line rfl
  have init₂ : Flow.Exec pub s (.line (.copy 3 0)) a m [.tick] b m := .line rfl
  have init₃ : Flow.Exec pub s (.line (.constant 4 1)) b m [.tick] c m := .line rfl
  have init₄ : Flow.Exec pub s (.line (.constant 5 2)) c m [.tick] t m := .line rfl
  simpa only [root, List.replicate_add, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
    using Flow.Exec.seq init₁ (.seq init₂ (.seq init₃ (.seq init₄ he)))

end CompressorRecords.RepetitionRAM

end VPVNP
end Computability
end OAI
