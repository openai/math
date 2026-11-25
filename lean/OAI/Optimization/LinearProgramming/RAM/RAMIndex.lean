import OAI.Optimization.LinearProgramming.RAM.RAMArithmetic

/-! A straight-line address expression compiler over a fixed set of input index registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Tape

open Block

inductive AddressOp where | plus | minus | times
  deriving DecidableEq, Repr

def AddressOp.value : AddressOp → Nat → Nat → Nat
  | .plus => Nat.add
  | .minus => Nat.sub
  | .times => Nat.mul

def AddressOp.cost : AddressOp → Nat → Nat → Nat
  | .plus | .minus => fun _ y => 2+4*y
  | .times => fun x y => 4+(5+4*x)*y

def AddressOp.code : AddressOp → Nat → Block
  | .plus => addSub true
  | .minus => addSub false
  | .times => multiply

inductive AddressTerm (n : Nat) where
  | val (value : Nat)
  | reg (reg : Fin n)
  | binary (op : AddressOp) (left right : AddressTerm n)
  deriving Repr

namespace AddressTerm

variable {n : Nat}

instance : Add (AddressTerm n) := ⟨binary .plus⟩
instance : Sub (AddressTerm n) := ⟨binary .minus⟩
instance : Mul (AddressTerm n) := ⟨binary .times⟩
instance (k : Nat) : OfNat (AddressTerm n) k := ⟨val k⟩

def value (env : Fin n → Nat) : AddressTerm n → Nat
  | .val k => k
  | .reg i => env i
  | .binary o x y => o.value (value env x) (value env y)

def cost (env : Fin n → Nat) : AddressTerm n → Nat
  | .val _ | .reg _ => 1
  | .binary o x y => cost env x + (cost env y + o.cost (value env x) (value env y))

def code (e : AddressTerm n) (base : Nat) : Block :=
  match e with
  | .val k => .op (.addrConst base k)
  | .reg i => .op (.addrCopy base i)
  | .binary o x y => .seq (x.code base) (.seq (y.code (base+1)) (o.code base))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem op_correct (o : AddressOp) (a : Nat) (m : Memory K) (hm : Good P m) :
    ∃ k t, Eval (Good P) (o.code a) m k t ∧ k ≤ o.cost (m.index a) (m.index (a+1)) ∧
      t.data = m.data ∧ (∀ i < a, t.index i = m.index i) ∧
      t.index a = o.value (m.index a) (m.index (a+1)) := by
  cases o with
  | plus => exact addSub_correct true a m hm
  | minus => exact addSub_correct false a m hm
  | times => exact multiply_correct a m hm

/-- Every computed address is produced by the finite fixed instruction sequence, with an
explicit step bound. All lower index registers and all scalar data survive evaluation. -/
theorem correct (e : AddressTerm n) (env : Fin n → Nat) (a : Nat) (m : Memory K)
    (hbase : n ≤ a) (henv : ∀ i : Fin n, m.index i = env i) (hs : Good P m) :
    ∃ k t, Eval (Good P) (e.code a) m k t ∧ k ≤ e.cost env ∧ t.data = m.data ∧
      (∀ i < a, t.index i = m.index i) ∧ t.index a = e.value env := by
  induction e generalizing a m with
  | val x =>
    exact ⟨_,_,eval_constI m hs a x,le_rfl,rfl,fun i hi => getPutDifferent _ hi.ne,
      getPutSame _ _ _⟩
  | reg i =>
    exact ⟨_,_,eval_copyI m hs a i,le_rfl,rfl,fun j hj => getPutDifferent _ hj.ne,
      (getPutSame _ _ _).trans (henv i)⟩
  | binary o x y hx hy =>
    obtain ⟨k,s,hx',hk,hd,hf,hv⟩ := hx a m hbase henv hs
    obtain ⟨l,t,hy',hl,hd',hf',hv'⟩ := hy (a+1) s (by omega)
      (fun i => (hf i (i.isLt.trans_le hbase)).trans (henv i)) hx'.safe_end
    obtain ⟨v,z,ho,hw,hf'',hh,hz⟩ := op_correct o a t hy'.safe_end
    have hleft : t.index a = x.value env := (hf' a (by omega)).trans hv
    rw [hleft,hv'] at hz hw
    exact ⟨_,z,.seq hx' (.seq hy' ho), Nat.add_le_add hk (Nat.add_le_add hl hw), hf''.trans (hd'.trans hd),
      fun i hi => (hh i hi).trans ((hf' i (by omega)).trans (hf i hi)),hz⟩

end AddressTerm
end Tape
end RAM
end LinearProgramming
end Optimization
end OAI
