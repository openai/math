import OAI.Optimization.LinearProgramming.RAM.RAMIndex
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-! Compile each compact decoder header into the permanent cursor registers.
Address expressions are evaluated in ascending destination order, preserving every
earlier entry. No scalar word is touched. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Block RAM.Tape

namespace Header

def write {n : Nat} (dst : Nat) : List (AddressTerm n) → Block
  | [] => .skip
  | e :: es => .seq (e.code dst) (write (dst+1) es)

theorem write_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}
    {n : Nat} (es : List (AddressTerm n)) (env : Fin n → Nat) (dst : Nat) (s : Memory K)
    (hbase : n ≤ dst) (hsrc : ∀ i : Fin n, s.index i.val = env i) (hs : Good P s) :
    ∃ t k, Eval (Good P) (write dst es) s k t ∧ k ≤ (es.map (·.cost env)).sum ∧ t.data = s.data ∧
      (∀ i < dst, t.index i = s.index i) ∧
      (∀ i : Fin es.length, t.index (dst+i.val) = (es.get i).value env) := by
  induction es generalizing s dst with
  | nil =>
    exact ⟨s,0,.skip hs,le_rfl,rfl,fun _ _ => rfl,fun i => Fin.elim0 i⟩
  | cons e es ih =>
    obtain ⟨k,u,first,hk,hd,hlo,hw⟩ := e.correct env dst s hbase hsrc hs
    obtain ⟨t,l,rest,hl,hd',hlo',hval⟩ := ih (dst+1) u (by omega)
      (fun i => (hlo i.val (i.isLt.trans_le hbase)).trans (hsrc i)) first.safe_end
    refine ⟨t,k+l,first.seq rest,by simpa using Nat.add_le_add hk hl,hd'.trans hd,
      fun i hi => (hlo' i (by omega)).trans (hlo i hi),?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hlo' dst (Nat.lt_succ_self _)).trans hw
    · have heq : (e::es).get j.succ = es.get j := by cases j; rfl
      rw [heq]
      simpa only [Fin.val_succ,show dst+1+j.val=dst+(j.val+1) by omega] using hval j

/-- Compact input [m,certificate base]. -/
def certTerms : List (AddressTerm 2) :=
  let m := AddressTerm.reg 0
  let src := AddressTerm.reg 1
  [m,src+m-1,m-1]

/-- Compact input [m,d,joint answer base,objective base]. -/
def optimumTerms : List (AddressTerm 4) :=
  let m := AddressTerm.reg 0
  let d := AddressTerm.reg 1
  let z := AddressTerm.reg 2
  let obj := AddressTerm.reg 3
  [d,d+m+1,z,obj,z+d+m,d+m]

/-- Compact input [d,positive multipliers,negative multipliers,objective,base point,staging base]. -/
def rayTerms : List (AddressTerm 6) :=
  let d := AddressTerm.reg 0
  let pos := AddressTerm.reg 1
  let neg := AddressTerm.reg 2
  let obj := AddressTerm.reg 3
  let base := AddressTerm.reg 4
  let out := AddressTerm.reg 5
  [d,d+d,pos,neg,obj,out+d,out,base,out+(d+d)-1,(d+d)-1]

private theorem cost_plus {n} (env : Fin n → Nat) (a b : AddressTerm n) :
    (a+b).cost env = a.cost env+(b.cost env+(2+4*b.value env)) := rfl
private theorem cost_minus {n} (env : Fin n → Nat) (a b : AddressTerm n) :
    (a-b).cost env = a.cost env+(b.cost env+(2+4*b.value env)) := rfl
private theorem val_plus {n} (env : Fin n → Nat) (a b : AddressTerm n) :
    (a+b).value env = a.value env+b.value env := rfl
private theorem val_one {n} (env : Fin n → Nat) : (1 : AddressTerm n).value env = 1 := rfl
private theorem cost_one {n} (env : Fin n → Nat) : (1 : AddressTerm n).cost env = 1 := rfl
private theorem val_reg {n} (env : Fin n → Nat) (i : Fin n) : (AddressTerm.reg i).value env = env i := rfl
private theorem cost_reg {n} (env : Fin n → Nat) (i : Fin n) : (AddressTerm.reg i).cost env = 1 := rfl
attribute [local simp] cost_plus cost_minus val_plus val_one cost_one val_reg cost_reg

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem cert_header (m src : Nat) (s : Memory K) (safe : Good P s)
    (h0 : s.index 0 = m) (h1 : s.index 1 = src) :
    ∃ t k, Eval (Good P) (write 6 certTerms) s k t ∧ k ≤ 40*(m+1) ∧ t.data = s.data ∧
      t.index 6=m ∧ t.index 7=src+m-1 ∧ t.index 8=m-1 := by
  let env : Fin 2 → Nat := ![m,src]
  have henv (i : Fin 2) : s.index i.val = env i := by fin_cases i <;> assumption
  obtain ⟨t,k,run,hk,hd,_,v⟩ := write_correct certTerms env 6 s (by decide) henv safe
  refine ⟨t,k,run,?_,hd,v ⟨0,by decide⟩,v ⟨1,by decide⟩,v ⟨2,by decide⟩⟩
  apply hk.trans
  simp [certTerms,env]; omega

theorem optimum_header (m d z obj : Nat) (s : Memory K) (safe : Good P s)
    (h0 : s.index 0 = m) (h1 : s.index 1 = d) (h2 : s.index 2 = z) (h3 : s.index 3 = obj) :
    ∃ t k, Eval (Good P) (write 6 optimumTerms) s k t ∧ k ≤ 40*(m+d+1) ∧ t.data = s.data ∧
      t.index 6=d ∧ t.index 7=d+m+1 ∧ t.index 8=z ∧ t.index 9=obj ∧
      t.index 10=z+d+m ∧ t.index 11=d+m := by
  let env : Fin 4 → Nat := ![m,d,z,obj]
  have henv (i : Fin 4) : s.index i.val = env i := by fin_cases i <;> assumption
  obtain ⟨t,k,run,hk,hd,_,v⟩ := write_correct optimumTerms env 6 s (by decide) henv safe
  refine ⟨t,k,run,?_,hd,v ⟨0,by decide⟩,v ⟨1,by decide⟩,v ⟨2,by decide⟩,
    v ⟨3,by decide⟩,v ⟨4,by decide⟩,v ⟨5,by decide⟩⟩
  apply hk.trans
  simp [optimumTerms,env]; omega

theorem ray_header (d pos neg obj base out : Nat) (s : Memory K) (safe : Good P s)
    (h0 : s.index 0=d) (h1 : s.index 1=pos) (h2 : s.index 2=neg)
    (h3 : s.index 3=obj) (h4 : s.index 4=base) (h5 : s.index 5=out) :
    ∃ t k, Eval (Good P) (write 6 rayTerms) s k t ∧ k ≤ 80*(d+1) ∧ t.data = s.data ∧
      t.index 6=d ∧ t.index 7=2*d ∧ t.index 8=pos ∧ t.index 9=neg ∧ t.index 10=obj ∧
      t.index 11=out+d ∧ t.index 12=out ∧ t.index 13=base ∧ t.index 14=out+2*d-1 ∧ t.index 15=2*d-1 := by
  let env : Fin 6 → Nat := ![d,pos,neg,obj,base,out]
  have henv (i : Fin 6) : s.index i.val = env i := by fin_cases i <;> assumption
  obtain ⟨t,k,run,hk,hd,_,v⟩ := write_correct rayTerms env 6 s (by decide) henv safe
  rw [two_mul]
  refine ⟨t,k,run,?_,hd,v ⟨0,by decide⟩,v ⟨1,by decide⟩,v ⟨2,by decide⟩,
    v ⟨3,by decide⟩,v ⟨4,by decide⟩,v ⟨5,by decide⟩,v ⟨6,by decide⟩,
    v ⟨7,by decide⟩,v ⟨8,by decide⟩,v ⟨9,by decide⟩⟩
  apply hk.trans
  simp [rayTerms,env]; omega

end Header
end PrimalDual
end LinearProgramming
end Optimization
end OAI
