import OAI.Hierarchy.DescentGLScoreRAM
import OAI.Hierarchy.DescentWordProduct

namespace OAI
/-! # Native correlation columns for a current load vector -/

namespace Hierarchy.DescentCorrelationRAM
open DescentGL DescentGLScoreRAM DescentIntegerScale ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing Classical BigOperators
noncomputable section

def left (k src : ℕ) (i : Fin (2^k)) : Expr := .lookup ⟨src,k⟩ (.lit i.val)
def right (k src : ℕ) (i : Fin (2^k)) : Expr :=
  .lookup ⟨src,k⟩ (lookupRow (2^k) (fun d=>(finFunctionFinEquiv (vec i+vec d)).val))

def mulTerm {w n : ℕ} (bits : ℕ) (a b : Term w 0 n) : Term w 0 n :=
  a.letThen ((b.rename Fin.succ).letThen ((DescentWordProduct.product w bits).rename ![1,0]))

theorem mulTerm_eval {w n : ℕ} (m : Memory w) (v : Fin n→Word w) (bits : ℕ) (h : bits≤w)
    (a b : Term w 0 n) (carry : (b.eval Fin.elim0 m v).val<2^bits) :
    (mulTerm bits a b).eval Fin.elim0 m v=a.eval Fin.elim0 m v*b.eval Fin.elim0 m v := by
  simp [mulTerm,Term.eval_letThen,Term.eval_rename,DescentWordProduct.product_eval _ _ _ h,
    Function.comp_def,Nat.mod_eq_of_lt carry]

def addTerms {w n : ℕ} : (j : ℕ)→(Fin j→Term w 0 n)→Term w 0 n
  | 0,_=>.literal 0
  | j+1,f=>.binary .add (addTerms j (fun i=>f i.castSucc)) (f (Fin.last j))

theorem addTerms_eval {w n : ℕ} (m : Memory w) (v : Fin n→Word w) (j : ℕ) (f : Fin j→Term w 0 n) :
    (addTerms j f).eval Fin.elim0 m v=∑i,(f i).eval Fin.elim0 m v := by
  induction j with
  | zero => simp [addTerms]
  | succ j ih => simp [addTerms,Fin.sum_univ_castSucc,ih,BinaryOp.eval]

def term (w k src out bits : ℕ) : Term w 0 1 :=
  addTerms (2^k) fun i=>mulTerm bits ((left k src i).compile w out) ((right k src i).compile w out)

def machine (w k src out bits : ℕ) : Procedure w :=
  PhysicalInputPhases.writing (term w k src out bits) Fin.elim0 out (2^k)

theorem eval {w k src out bits : ℕ} (m : Memory w) (a : Word w) (x : DescentGL.Bits k→ℕ)
    (d : Fin (2^k)) (atRow : a-(out:Word w)=(d.val:Word w))
    (fit : (Bank.mk src k).Fits w out) (addr : out<2^w) (precision : bits≤w)
    (values : ∀j : Fin (2^k),m (src+j.val)=(x (vec j):Word w))
    (small : ∀i,x i<2^bits) :
    (term w k src out bits).eval Fin.elim0 m (fun _=>a)=((natCorrelation x (vec d):ℕ):Word w) := by
  have power := Nat.pow_le_pow_right (n:=2) (by decide) precision
  have r (i : Fin (2^k)) : ((right k src i).compile w out).eval Fin.elim0 m (fun _=>a) =
      (x (vec i+vec d):Word w) := by
    have safe : (right k src i).Fits w out := ⟨fit,lookupRow_fits ..⟩
    rw [eval_compile (right k src i) m a safe addr,atRow]
    let index := fun j : Fin (2^k) => (finFunctionFinEquiv (vec i+vec j)).val
    let key : Fin (2^k) := finFunctionFinEquiv (vec i+vec d)
    have hk : key.val<2^w := key.isLt.trans fit.2.1
    have rowKey : (lookupRow (2^k) index).eval m (d.val:Word w)=(key.val:Word w) :=
      lookupRow_eval m index fit.2.1.le d
    change (Bank.mk src k).read m ((lookupRow (2^k) index).eval m (d.val:Word w)) = _
    rw [rowKey]
    have decoded : vec key=vec i+vec d := finFunctionFinEquiv.symm_apply_apply _
    calc
      _ = m (src+key.val) := by
        simp only [Bank.read,Bank.size,Fin.val_cast_of_lt hk,Nat.mod_eq_of_lt key.isLt]
      _ = _ := (values key).trans (congrArg (fun j => (x j : Word w)) decoded)
  have l (i : Fin (2^k)) : ((left k src i).compile w out).eval Fin.elim0 m (fun _=>a)=
      (x (vec i):Word w) := by
    have safe : (left k src i).Fits w out := ⟨fit,trivial⟩
    rw [eval_compile (left k src i) m a safe addr]
    simp [left,Expr.eval,Bank.read,Bank.size,Fin.val_cast_of_lt (i.isLt.trans fit.2.1),Nat.mod_eq_of_lt i.isLt,values]
  rw [term,addTerms_eval]
  have one (i : Fin (2^k)) : (mulTerm bits ((left k src i).compile w out) ((right k src i).compile w out)).eval
      Fin.elim0 m (fun _=>a)=(x (vec i)*x (vec i+vec d):ℕ) := by
    have carry : (((right k src i).compile w out).eval Fin.elim0 m (fun _=>a)).val<2^bits := by
      rw [r i,Fin.val_cast_of_lt ((small _).trans_le power)]
      exact small _
    rw [mulTerm_eval m _ bits precision _ _ carry,l i,r i,Nat.cast_mul]
  simp only [one,natCorrelation,Nat.cast_sum]
  exact finFunctionFinEquiv.symm.sum_comp (fun j : DescentGL.Bits k=>((x j*x (j+vec d):ℕ):Word w))

def after {w : ℕ} (k out : ℕ) (m : Memory w) (x : DescentGL.Bits k→ℕ) : Memory w :=
  fillSegment out (2^k) (fun addr=>(natCorrelation x (vec ⟨(addr-out)%2^k,Nat.mod_lt _ (Nat.two_pow_pos _)⟩):Word w)) m

theorem run {w k src out bits : ℕ} (m : Memory w) (x : DescentGL.Bits k→ℕ)
    (fit : (Bank.mk src k).Fits w out) (room : out+2^k<2^w) (precision : bits≤w)
    (values : ∀j : Fin (2^k),m (src+j.val)=(x (vec j):Word w))
    (small : ∀i,x i<2^bits) :
    (machine w k src out bits).Exec m (after k out m x) (4+2^k*(2*(term w k src out bits).binds+4)) := by
  let field := fun addr : ℕ=>(natCorrelation x (vec ⟨(addr-out)%2^k,Nat.mod_lt _ (Nat.two_pow_pos _)⟩):Word w)
  have spec : (machine w k src out bits).Spec (·=m) (fun src dst=>dst=fillSegment out (2^k) field src)
      (4+2^k*(2*(term w k src out bits).binds+4)) :=
    PhysicalInputPhases.writing_spec (term w k src out bits) Fin.elim0 out (2^k) room (·=m) field (by
      intro start eq a now lo inside same
      subst start
      have bounded : a.val-out<2^k := by omega
      let d : Fin (2^k) := ⟨a.val-out,bounded⟩
      have difference : a-(out:Word w)=(d.val:Word w) := by simp [d,Nat.cast_sub lo]
      have observed (i : Fin (2^k)) : now (src+i.val)=(x (vec i):Word w) := by
        rw [same _ (.inl (by have := i.isLt;have := fit.2.2;change src+2^k≤out at this;omega)),values]
      simpa [field,d,Nat.mod_eq_of_lt bounded] using eval now a x d difference fit (by omega) precision observed small)
  intro P R K M pc reg pub exit installed data cfg start entry eq
  subst start
  exact spec M pc reg pub exit installed data cfg m entry rfl

end
end Hierarchy.DescentCorrelationRAM

end OAI
