import OAI.Computability.VPVNP.PairNativeOperandArithmetic
import OAI.Computability.VPVNP.PairNativeOperandLog

/-! # Compiling public expressions to native instructions within a pair burst -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeOperands
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM LiveProgram
open scoped Fin.CommRing

/-- Evaluate an operand, pass it through the floor or ceiling binary-logarithm routine in fixed
registers 2 and 3, then copy the result back to its temporary slot. -/
def logarithm {r : ℕ} (ceil : Bool) (base : ℕ) (a : Code r) : Code r :=
  .seq (.seq (.seq a (.line (.copy (fixed r 2) (temp r base))))
    (PrimedCounter.renameFlow (fixed r) id (Log.program ceil))) (.line (.copy (temp r base) (fixed r 3)))

theorem logarithm_eval (g : Geometry) (lit : LiteralPrefix) {r base x u : ℕ} (hroom : base ≤ r)
    (ceil : Bool) {a : Code r} (ha : Eval g lit r base x u a) (hx : x < 2^g.w) (hw : 2 ≤ g.w) :
    Eval g lit r base (if ceil then Nat.clog 2 x else Nat.log 2 x) (u+(10*(g.w+1)+12)) (logarithm ceil base a) := by
  intro pub st m rs ready
  obtain ⟨t,ht,mid,run,hvalue,keep⟩ := ha pub st m rs ready
  let z := Function.update mid (fixed r 2) (mid (temp r base))
  have hcopy : Flow.Exec pub st (.line (.copy (fixed r 2) (temp r base))) mid m (List.replicate 1 .tick) z m := .line rfl
  obtain ⟨k,hk,localOut,small,hlog,houtside⟩ := Log.run ceil pub st m (z ∘ fixed r) hw
  obtain ⟨big,loop,restrict,others⟩ := PrimedCounter.liftExec (fixedEmbedding r) id pub small z rfl
  have hx' : ((z ∘ fixed r) 2).val = x := by
    change (z (fixed r 2)).val = _
    rw [show z (fixed r 2) = mid (temp r base) from Function.update_self ..,hvalue]
    exact Nat.mod_eq_of_lt hx
  have hout : big (fixed r 3) = Fin.ofNat _ (if ceil then Nat.clog 2 x else Nat.log 2 x) := by
    have h := congrFun restrict 3
    change big (fixed r 3) = localOut 3 at h
    rw [h,← hx',← hlog]; exact (Fin.ofNat_val_eq_self _).symm
  have hback : Flow.Exec pub st (.line (.copy (temp r base) (fixed r 3))) big m (List.replicate 1 .tick)
      (Function.update big (temp r base) (big (fixed r 3))) m := .line rfl
  have loopKeep : Keeps base z big := by
    intro i lo _
    by_cases hi : i ∈ Set.range (fixedEmbedding r)
    · obtain ⟨j,rfl⟩ := hi
      exact (congrFun restrict j).trans (houtside j lo)
    · exact others i hi
  exact ⟨_,by omega,_,seqTicks (seqTicks (seqTicks run hcopy) loop) hback,(Function.update_self ..).trans hout,
    (((keep.trans (scratch_keep mid 2 (by decide) _)).trans loopKeep).trans (update_keep hroom big _))⟩

/-- Compile a public geometry expression into native instructions writing temporary slot
`base`. A binary operation evaluates its right operand one slot higher to retain the left
value. -/
def compile (r base : ℕ) : PublicExpr → Code r
  | .lit n => literal (temp r base) n
  | .n => .line (.copy (temp r base) (inputReg r 0))
  | .d => .line (.copy (temp r base) (inputReg r 1))
  | .H => .line (.copy (temp r base) (inputReg r 2))
  | .w => .line (.copy (temp r base) (inputReg r 3))
  | .add a b => combine .add base (compile r base a) (compile r (base+1) b)
  | .sub a b => combine .sub base (compile r base a) (compile r (base+1) b)
  | .mul a b => combine .mul base (compile r base a) (compile r (base+1) b)
  | .divConst a n => combine .div base (compile r base a) (literal (temp r (base+1)) n)
  | .pow2 a => pow2 base (compile r base a)
  | .log2 a => logarithm false base (compile r base a)
  | .clog2 a => logarithm true base (compile r base a)

/-- Recursive tick bound for a compiled public expression. Literal costs grow with the literal
and logarithm costs grow with the machine word width. -/
def cost (w : ℕ) : PublicExpr → ℕ
  | .lit n => n+2
  | .add a b | .sub a b | .mul a b => cost w a + cost w b + 2
  | .divConst a n => cost w a + (n+2) + 2
  | .pow2 a => cost w a + 2
  | .log2 a | .clog2 a => cost w a + (10*(w+1)+12)
  | _ => 1

theorem cost_le (e : PublicExpr) (w : ℕ) : cost w e ≤ cost 0 e*(w+1) := by
  induction e <;> simp only [cost,Nat.zero_add,Nat.mul_one,Nat.add_mul] at *
  all_goals (simp only [Nat.mul_succ] at *; omega)

private theorem value_lt {e : PublicExpr} {g : Geometry} (h : e.Fits g (2^g.w)) : e.eval g < 2^g.w := by
  cases e <;> exact h.1

theorem compile_eval (g : Geometry) (lit : LiteralPrefix) (hw : 2 ≤ g.w) (r base : ℕ) (e : PublicExpr)
    (hr : base + RAMTape.PublicExprMachine.extra e ≤ r) (hf : e.Fits g (2^g.w)) :
    Eval g lit r base (e.eval g) (cost g.w e) (compile r base e) := by
  induction e generalizing base with
  | lit n => exact literal_eval g lit (by simpa [RAMTape.PublicExprMachine.extra] using hr) n
  | n => exact input_eval g lit (by simpa [RAMTape.PublicExprMachine.extra] using hr) 0 _ rfl
  | d => exact input_eval g lit (by simpa [RAMTape.PublicExprMachine.extra] using hr) 1 _ rfl
  | H => exact input_eval g lit (by simpa [RAMTape.PublicExprMachine.extra] using hr) 2 _ rfl
  | w => exact input_eval g lit (by simpa [RAMTape.PublicExprMachine.extra] using hr) 3 _ rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [RAMTape.PublicExprMachine.extra] at hr
    obtain ⟨_,fa,fb⟩ := hf
    exact combine_eval g lit (by omega) _ (ha _ (by omega) fa) (hb _ (by omega) fb) (value_lt fa) (value_lt fb)
  | divConst a n ha =>
    simp only [RAMTape.PublicExprMachine.extra] at hr
    obtain ⟨_,fa,fn⟩ := hf
    exact combine_eval g lit (by omega) .div (ha _ (by omega) fa) (literal_eval g lit (by omega) n) (value_lt fa) fn
  | pow2 a ha =>
    simp only [RAMTape.PublicExprMachine.extra] at hr
    exact pow2_eval g lit (by omega) (ha _ (by omega) hf.2) (value_lt hf.2) hf.1
  | log2 a ha =>
    exact logarithm_eval g lit (by simp only [RAMTape.PublicExprMachine.extra] at hr; omega)
      false (ha _ hr hf.2) (value_lt hf.2) hw
  | clog2 a ha =>
    exact logarithm_eval g lit (by simp only [RAMTape.PublicExprMachine.extra] at hr; omega)
      true (ha _ hr hf.2) (value_lt hf.2) hw

end PairSimulation.NativeOperands

end VPVNP
end Computability
end OAI
