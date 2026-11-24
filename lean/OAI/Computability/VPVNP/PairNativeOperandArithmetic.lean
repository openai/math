import OAI.Computability.VPVNP.PairNativeOperandBase

/-! # Native word arithmetic for the pair's private operand bank -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeOperands
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM LiveProgram
open scoped Fin.CommRing

/-- The four binary operations available when combining two native operand values. -/
inductive Arithmetic where | add | sub | mul | div

/-- Natural-number interpretation of the binary operand operations, using truncated subtraction
and integer division. -/
def Arithmetic.value : Arithmetic → ℕ → ℕ → ℕ
  | .add => (·+·) | .sub => (·-·) | .mul => (·*·) | .div => (·/·)

/-- Instruction flow that combines `dst` with `rhs` in place. The subtraction branch writes
zero when the right operand exceeds the left. -/
def Arithmetic.op {r : ℕ} (dst rhs : Fin (registerCount r)) : Arithmetic → Code r
  | .add => .line (.binary .add dst dst rhs)
  | .sub => .ifLt dst rhs (.line (.constant dst 0)) (.line (.binary .sub dst dst rhs))
  | .mul => .line (.binary .mul dst dst rhs)
  | .div => .line (.binary .div dst dst rhs)

private theorem op_run {r w : ℕ} (pub : Fin 11 → Word w) (st : Word w) (m : Memory w)
    (rs : Regs w (registerCount r)) (dst rhs : Fin (registerCount r)) (op : Arithmetic)
    {x y : ℕ} (hx : rs dst = Fin.ofNat _ x) (hy : rs rhs = Fin.ofNat _ y) (fx : x < 2^w) (fy : y < 2^w) :
    ∃ t ≤ 2, Flow.Exec pub st (op.op dst rhs) rs m (List.replicate t .tick)
      (Function.update rs dst (Fin.ofNat _ (op.value x y))) m := by
  have vx : (rs dst).val = x := hx ▸ Nat.mod_eq_of_lt fx
  have vy : (rs rhs).val = y := hy ▸ Nat.mod_eq_of_lt fy
  cases op with
  | add =>
    refine ⟨1,by decide,Flow.Exec.line ?_⟩
    simp only [Op.effect,BinaryOp.eval,hx,hy,Arithmetic.value]
    rw [show Fin.ofNat (2^w) x + Fin.ofNat (2^w) y = Fin.ofNat _ (x+y) from (Nat.cast_add (R := Word w) ..).symm]
  | mul =>
    refine ⟨1,by decide,Flow.Exec.line ?_⟩
    simp only [Op.effect,BinaryOp.eval,hx,hy,Arithmetic.value]
    rw [show Fin.ofNat (2^w) x * Fin.ofNat (2^w) y = Fin.ofNat _ (x*y) from (Nat.cast_mul (α := Word w) x y).symm]
  | div =>
    refine ⟨1,by decide,Flow.Exec.line ?_⟩
    simp only [Op.effect,BinaryOp.eval,vx,vy,Arithmetic.value]
  | sub =>
    by_cases h : x < y
    · refine ⟨2,le_rfl,.ifLtYes (by change (rs dst).val < (rs rhs).val; omega) (.line ?_)⟩
      simp [Op.effect,Arithmetic.value,Nat.sub_eq_zero_of_le h.le]
    · refine ⟨2,le_rfl,.ifLtNo (by change ¬(rs dst).val < (rs rhs).val; omega) (.line ?_)⟩
      simp only [Op.effect,BinaryOp.eval,hx,hy,Arithmetic.value]
      rw [show Fin.ofNat (2^w) x - Fin.ofNat (2^w) y = Fin.ofNat _ (x-y) from
        (Nat.cast_sub (R := Word w) (Nat.le_of_not_gt h)).symm]

/-- Run the two operand flows in order, then combine the values in temporary slots `base` and
`base+1` and leave the result in `base`. -/
def combine {r : ℕ} (op : Arithmetic) (base : ℕ) (a b : Code r) : Code r :=
  .seq (.seq a b) (op.op (temp r base) (temp r (base+1)))

theorem combine_eval (g : Geometry) (lit : LiteralPrefix) {r base x y u v : ℕ} (hroom : base+1 ≤ r)
    (op : Arithmetic) {a b : Code r} (ha : Eval g lit r base x u a) (hb : Eval g lit r (base+1) y v b)
    (fx : x < 2^g.w) (fy : y < 2^g.w) : Eval g lit r base (op.value x y) (u+v+2) (combine op base a b) := by
  intro pub st m rs ready
  obtain ⟨t,ht,mid,first,hx,keep⟩ := ha pub st m rs ready
  obtain ⟨s,hs,z,second,hy,preserve⟩ := hb pub st m mid (keep.ready ready)
  have hx' : z (temp r base) = Fin.ofNat _ x := by
    apply Eq.trans (preserve _ ?_ ?_) hx
    all_goals rw [temp_val (by omega)]; omega
  obtain ⟨k,hk,run⟩ := op_run pub st m z _ _ op hx' hy fx fy
  exact ⟨_,by omega,_,seqTicks (seqTicks first second) run,Function.update_self ..,
    (keep.trans (preserve.mono (by omega))).trans (update_keep (by omega) z _)⟩

/-- Evaluate the exponent at `base` and replace it with a left shift of one by that exponent. -/
def pow2 {r : ℕ} (base : ℕ) (a : Code r) : Code r :=
  .seq (.seq a (.line (.constant (fixed r 0) 1)))
    (.line (.binary .shiftLeft (temp r base) (fixed r 0) (temp r base)))

theorem pow2_eval (g : Geometry) (lit : LiteralPrefix) {r base x u : ℕ} (hroom : base ≤ r)
    {a : Code r} (ha : Eval g lit r base x u a) (hx : x < 2^g.w) (hf : 2^x < 2^g.w) :
    Eval g lit r base (2^x) (u+2) (pow2 base a) := by
  intro pub st m rs ready
  obtain ⟨t,ht,mid,run,hval,keep⟩ := ha pub st m rs ready
  let z := Function.update mid (fixed r 0) (Fin.ofNat (2^g.w) 1)
  have h1 : Flow.Exec pub st (.line (.constant (fixed r 0) 1)) mid m (List.replicate 1 .tick) z m := .line rfl
  have hval' : (z (temp r base)).val = x := by
    rw [show z (temp r base) = mid (temp r base) from Function.update_of_ne (temp_ne_fixed (r := r) base 0) _ _,hval]
    exact Nat.mod_eq_of_lt hx
  have he : x < g.w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hf
  have hone : (z (fixed r 0)).val = 1 := by
    rw [show z (fixed r 0) = Fin.ofNat _ 1 from Function.update_self ..]
    exact Nat.mod_eq_of_lt ((Nat.one_le_two_pow (n := x)).trans_lt hf)
  have h2 : Flow.Exec pub st (.line (.binary .shiftLeft (temp r base) (fixed r 0) (temp r base)))
      z m (List.replicate 1 .tick) (Function.update z (temp r base) (Fin.ofNat _ (2^x))) m := by
    apply Flow.Exec.line
    simp [Op.effect,BinaryOp.eval,hval',hone,he,Nat.shiftLeft_eq]
  exact ⟨_,by omega,_,seqTicks (seqTicks run h1) h2,Function.update_self ..,
    (keep.trans (scratch_keep mid 0 (by decide) _)).trans (update_keep hroom z _)⟩

end PairSimulation.NativeOperands

end VPVNP
end Computability
end OAI
