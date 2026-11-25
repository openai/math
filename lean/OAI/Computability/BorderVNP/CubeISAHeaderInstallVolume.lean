import OAI.Computability.BorderVNP.CubeISAHeaderInstallSetup
import OAI.Computability.BorderVNP.RoutingISADeterministic

/-! # Computing the oriented selector volume with fixed native arithmetic -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeHeaderInstall

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- A fixed number of accumulator instructions. The second source is unchanged. -/
def repeatOp (op : BinaryOp) (x y : Reg) : ℕ → Code
  | 0 => .nop
  | k+1 => .seq (repeatOp op x y k) (.binary op x x y)

/-- Each repeated arithmetic instruction is deterministic. -/
theorem repeatOp_deterministic (op : BinaryOp) (x y : Reg) (k : ℕ) :
    (repeatOp op x y k).deterministic = true := by
  induction k <;> simp [repeatOp,Code.deterministic, *]

private theorem repeat_effect (w : ℕ) (pub : Arg → ℕ) (z : NatState) (op : BinaryOp) (x y : Reg)
    (sep : y ≠ x) (f : ℕ → ℕ) (start : f 0 = z.reg x) (step : ∀ i, f (i+1) = addressOp op (f i) (z.reg y))
    (k : ℕ) (fits : ∀ i < k, addressOpFits w op (f i) (z.reg y)) :
    (repeatOp op x y k).fixedSafe w pub z ∧
    (repeatOp op x y k).fixedEval pub z = ⟨Function.update z.reg x (f k), z.mem⟩ := by
  induction k with
  | zero => simp [repeatOp,Code.fixedSafe,Code.safeReadOnly,Code.fixedEval,Code.evalNat,start]
  | succ k ih =>
    obtain ⟨safe,out⟩ := ih (fun i hi => fits i (by omega))
    simp only [repeatOp,Code.fixedSafe,Code.fixedEval,out,safe,true_and,Code.safeReadOnly,
      Code.evalNat,Function.update_self,Function.update_of_ne sep,Function.update_idem,← step]
    exact ⟨fits k (by omega),trivial⟩

/-- The fixed unrolling realizes the accumulator recurrence with exactly its final
natural value, preserving every other register and all of memory. -/
theorem repeatOp_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (op : BinaryOp) (x y : Reg) (sep : y ≠ x) (k : ℕ)
    (f : ℕ → ℕ) (start : f 0 = readings s x)
    (step : ∀ i, f (i+1) = addressOp op (f i) (readings s y))
    (fits : ∀ i < k, addressOpFits w op (f i) (readings s y)) :
    BoundedRun pub mac (repeatOp op x y k) s m (k+1) (fun z =>
      z.reg = Function.update (readings s) x (f k) ∧ z.mem = readings m) := by
  obtain ⟨safe,out⟩ := repeat_effect w (readings pub) (.ofWords s m) op x y sep f start step k fits
  have slots (i : ℕ) : (repeatOp op x y i).slots = i+1 := by
    induction i with
    | zero => rfl
    | succ j ih => simp [repeatOp,Code.slots,ih]
  apply (Code.runFixed _ pub mac s m safe).mono (slots k).le
  rintro _ rfl
  rw [out]
  exact ⟨rfl,rfl⟩

/-- Power by the alphabet-pair radix followed by fixed selector-width scaling. -/
def volumeCode (n bits : ℕ) : Code := .seq (repeatOp .mul 40 36 n) (repeatOp .add 27 40 bits)

private theorem pow_le_max {i n : ℕ} (x : ℕ) (hi : i ≤ n) : x^i ≤ max 1 (x^n) := by
  by_cases hx : 0 < x
  · exact (pow_le_pow_right' hx hi).trans (le_max_right ..)
  · obtain rfl : x = 0 := by omega
    cases i <;> simp

/-- The fixed program returns the selector volume without a large immediate operand. -/
theorem volumeCode_run {w n bits : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Inputs) (fit : l.Fits w n bits (readings pub 0))
    (p40 : readings s 40 = 2*l.blocks) (p36 : readings s 36 = l.d.choose 2) (p27 : readings s 27 = 0) :
    BoundedRun pub mac (volumeCode n bits) s m ((n+1)+(bits+1)) (fun z =>
      z.reg 27 = l.volume n bits ∧ (∀ j : Reg, j ≠ 27 → j ≠ 40 → z.reg j = readings s j) ∧
      z.mem = readings m) := by
  let f (k : ℕ) := 2*l.blocks*(l.d.choose 2)^k
  have recur (i : ℕ) : f (i+1) = addressOp .mul (f i) (readings s 36) := by
    simp [f,p36,addressOp,pow_succ,Nat.mul_assoc]
  have prefixFit (i : ℕ) (hi : i < n) : addressOpFits w .mul (f i) (readings s 36) := by
    change addressOp .mul (f i) (readings s 36) < _
    rw [← recur]
    exact (Nat.mul_le_mul_left _ (pow_le_max _ hi)).trans_lt fit.packets
  have first := repeatOp_run pub mac s m .mul 40 36 (by decide) n f (by simp [f,p40]) recur prefixFit
  apply first.seq
  rintro t mt ⟨regs,mem⟩
  have t40 : readings t 40 = f n := by rw [show readings t = _ from regs,Function.update_self]
  have t27 : readings t 27 = 0 := by rw [show readings t = _ from regs,Function.update_of_ne (by decide : (27:Reg) ≠ 40),p27]
  let g (k : ℕ) := f n * k
  have recg (i : ℕ) : g (i+1) = addressOp .add (g i) (readings t 40) := by
    simp [g,t40,addressOp,Nat.mul_succ]
  have bound (i : ℕ) (hi : i < bits) : addressOpFits w .add (g i) (readings t 40) := by
    change addressOp .add (g i) (readings t 40) < _
    rw [← recg]
    exact (Nat.mul_le_mul_left _ hi).trans_lt fit.volume
  apply (repeatOp_run pub mac t mt .add 27 40 (by decide) bits g (by simp [g,t27]) recg bound).mono le_rfl
  rintro z ⟨rz,mz⟩
  refine ⟨by rw [rz,Function.update_self]; rfl,?_,mz.trans mem⟩
  intro j j27 j40
  rw [rz,Function.update_of_ne j27,show readings t = _ from regs,Function.update_of_ne j40]

end RoutingISA.CubeHeaderInstall

end BorderVNP
end Computability
end OAI
