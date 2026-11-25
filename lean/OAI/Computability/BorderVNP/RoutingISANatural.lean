import OAI.Computability.BorderVNP.RoutingISAInverse
import OAI.Computability.BorderVNP.RoutingISADeterministic

/-! # Natural address arithmetic on read-only signed team instructions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Integer results of the five unsigned address arithmetic operations. -/
def addressOp : BinaryOp → ℕ → ℕ → ℕ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .mod, x, y => x % y
  | _, _, _ => 0

/-- Arithmetic bounds ensuring that the actual operation has its ordinary
natural value, including a nonzero divisor for division and remainder. -/
def addressOpFits (w : ℕ) : BinaryOp → ℕ → ℕ → Prop
  | .add, x, y => x + y < 2^w
  | .sub, x, y => y ≤ x
  | .mul, x, y => x * y < 2^w
  | .div, _, y | .mod, _, y => 0 < y
  | _, _, _ => False

/-- Natural interpretation of a loop-free read-only fragment. Its bounds
are checked separately by `Code.safeReadOnly`. -/
def Code.evalNat (pub : Arg → ℕ) (mem : ℕ → ℕ) : Code → (Reg → ℕ) → Reg → ℕ
  | .nop, s => s
  | .constant d v, s => Function.update s d v.val
  | .publicWord d i, s => Function.update s d (pub i)
  | .copy d i, s => Function.update s d (s i)
  | .binary op d x y, s => Function.update s d (addressOp op (s x) (s y))
  | .load d a, s => Function.update s d (mem (s a))
  | .seq a b, s => b.evalNat pub mem (a.evalNat pub mem s)
  | .ifLt x y a b, s => if s x < s y then a.evalNat pub mem s else b.evalNat pub mem s
  | .ifEq x y a b, s => if s x = s y then a.evalNat pub mem s else b.evalNat pub mem s
  | _, s => s

/-- Every arithmetic instruction reached by this fragment fits its word, every
divisor is positive, and the fragment uses only the address-calculation opcodes. -/
def Code.safeReadOnly (w : ℕ) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Code → (Reg → ℕ) → Prop
  | .nop, _ | .publicWord .., _ | .load .., _ | .copy .., _ => True
  | .constant _ v, _ => v.val < 2^w
  | .binary op _ x y, s => addressOpFits w op (s x) (s y)
  | .seq a b, s => a.safeReadOnly w pub mem s ∧ b.safeReadOnly w pub mem (a.evalNat pub mem s)
  | .ifLt x y a b, s => if s x < s y then a.safeReadOnly w pub mem s else b.safeReadOnly w pub mem s
  | .ifEq x y a b, s => if s x = s y then a.safeReadOnly w pub mem s else b.safeReadOnly w pub mem s
  | _, _ => False

/-- Numeric readings of a finite word array. -/
def readings {ι : Type*} {w : ℕ} (s : ι → Word w) (i : ι) : ℕ := (s i).val

private theorem readings_update {ι : Type*} [DecidableEq ι] {w : ℕ}
    (s : ι → Word w) (i : ι) (v : Word w) :
    readings (Function.update s i v) = Function.update (readings s) i v.val := by
  funext j
  by_cases h : j = i <;> simp [readings, h]

private theorem eval_addressOp {w : ℕ} {op : BinaryOp} (x y : Word w)
    (h : addressOpFits w op x.val y.val) :
    (op.eval x y).val = addressOp op x.val y.val ∧ ¬ ((op = .div ∨ op = .mod) ∧ y = 0) := by
  cases op <;> simp_all [addressOpFits, addressOp, BinaryOp.eval]
  · exact Nat.mod_eq_of_lt h
  · exact Fin.sub_val_of_le h
  · exact Nat.mod_eq_of_lt h
  · exact ⟨Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt), fun he => by simp [he] at h⟩
  · exact ⟨Nat.mod_eq_of_lt ((Nat.mod_lt _ h).trans y.isLt), fun he => by simp [he] at h⟩

/-- Cost at the actual burst accounting rate of the paper. -/
abbrev traceCost {w : ℕ} (es : List (TeamRAM.Event w)) : ℕ :=
  VPVNP.RAMBuckets.cost (fun e : TeamRAM.Event w ↦ e.action.extra) es

/-- The unsigned, read-only straight-line evaluator executes on the physical bank
and true memory with at most one tick per code slot. Its returned word values
are exactly those of the unbounded interpretation. -/
theorem Code.runReadOnly {w : ℕ} (c : Code) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (safe : c.safeReadOnly w (readings pub) (readings m) (readings s)) :
    ∃ es t, Runs pub macros c s m es t m ∧ traceCost es ≤ c.slots ∧
      readings t = c.evalNat (readings pub) (readings m) (readings s) := by
  induction c generalizing s with
  | nop =>
    exact ⟨_,_,Runs.localStep m rfl rfl,le_rfl,rfl⟩
  | constant d v =>
    refine ⟨_,_,Runs.localStep m rfl rfl,le_rfl,?_⟩
    rw [readings_update]
    simp only [evalNat, Fin.val_ofNat, Nat.mod_eq_of_lt safe]
  | publicWord d i | copy d i =>
    exact ⟨_,_,Runs.localStep m rfl rfl,le_rfl,readings_update ..⟩
  | load d a => exact ⟨_,_,Runs.load pub macros d a s m,le_rfl,readings_update ..⟩
  | binary op d x y =>
    obtain ⟨hv,hn⟩ := eval_addressOp (s x) (s y) safe
    refine ⟨_,Function.update s d (op.eval (s x) (s y)),Runs.localStep m (by rfl) (by simp [Code.atom, hn]),le_rfl,?_⟩
    rw [readings_update, hv]
    rfl
  | seq a b iha ihb =>
    obtain ⟨es,t,r,hc,hr⟩ := iha s safe.1
    obtain ⟨fs,u,r',hc',hu⟩ := ihb t (hr ▸ safe.2)
    refine ⟨_,u,r.seq r',?_,?_⟩
    · exact (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add hc hc')
    · simpa only [Code.evalNat, ← hr] using hu
  | ifLt x y a b iha ihb =>
    by_cases guard : s x < s y
    · have hg : readings s x < readings s y := guard
      obtain ⟨es,t,r,hc,hr⟩ := iha s (by simpa [safeReadOnly, hg] using safe)
      refine ⟨_,t,Runs.ifLt (by simpa [guard] using r),?_,?_⟩
      · change 1 + traceCost es ≤ 1 + a.slots + b.slots
        omega
      · simpa only [Code.evalNat, hg, ite_true] using hr
    · have hg : ¬ readings s x < readings s y := guard
      obtain ⟨es,t,r,hc,hr⟩ := ihb s (by simpa [safeReadOnly, hg] using safe)
      refine ⟨_,t,Runs.ifLt (by simpa [guard] using r),?_,?_⟩
      · change 1 + traceCost es ≤ 1 + a.slots + b.slots
        omega
      · simpa only [Code.evalNat, hg, ite_false] using hr
  | ifEq x y a b iha ihb =>
    by_cases guard : s x = s y
    · have hg : readings s x = readings s y := congrArg Fin.val guard
      obtain ⟨es,t,r,hc,hr⟩ := iha s (by simpa [safeReadOnly, hg] using safe)
      refine ⟨_,t,Runs.ifEq (by simpa [guard] using r),?_,?_⟩
      · change 1 + traceCost es ≤ 1 + a.slots + b.slots
        omega
      · simpa only [Code.evalNat, hg, ite_true] using hr
    · have hg : readings s x ≠ readings s y := fun he => guard (Fin.ext he)
      obtain ⟨es,t,r,hc,hr⟩ := ihb s (by simpa [safeReadOnly, hg] using safe)
      refine ⟨_,t,Runs.ifEq (by simpa [guard] using r),?_,?_⟩
      · change 1 + traceCost es ≤ 1 + a.slots + b.slots
        omega
      · simpa only [Code.evalNat, hg, ite_false] using hr
  | _ => exact safe.elim

/-- A read-only calculation changes none of the registers below a given boundary. -/
def Code.protects (lo : ℕ) : Code → Bool
  | .constant d _ | .publicWord d _ | .copy d _ | .binary _ d _ _ | .load d _ => decide (lo ≤ d.val)
  | .seq a b | .ifLt _ _ a b | .ifEq _ _ a b => a.protects lo && b.protects lo
  | _ => true

/-- Protected register values survive address evaluation, independently of all
the loaded words and the path of the conditionals. -/
theorem Code.evalNat_protected (c : Code) (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    {lo : ℕ} (hc : c.protects lo = true) (i : Reg) (hi : i.val < lo) :
    c.evalNat pub mem s i = s i := by
  induction c generalizing s with
  | seq a b iha ihb =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hc
    exact (ihb _ hb).trans (iha s ha)
  | ifEq x y a b iha ihb | ifLt x y a b iha ihb =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hc
    simp only [Code.evalNat]
    split
    · exact iha _ ha
    · exact ihb _ hb
  | constant d _ | publicWord d _ | copy d _ | binary _ d _ _ | load d _ =>
    have hd : lo ≤ d.val := of_decide_eq_true hc
    exact Function.update_of_ne (fun he => by subst i; omega) ..
  | _ => rfl

end RoutingISA

end BorderVNP
end Computability
end OAI
