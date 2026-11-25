import OAI.Optimization.LinearProgramming.Recovery.ConstraintBases
import OAI.Optimization.LinearProgramming.Geometry.UniformCopy
import OAI.Optimization.LinearProgramming.Geometry.UniformTable

/-! Append the support constraints below the matrix of the opposite subspace by
writing its n×n diagonal restriction block from the actual scalar flags. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace MaskedTable

open RAM Compression
open _root_.OAI.Optimization.LinearProgramming.Geometry

/-- Diagonal entry `1-flag[row]`, zero at every off-diagonal position. -/
def diagonal : Block := .seq (cellAddress 38 39 42 162 41 14 30)
  (.seq (.op (.load 6 38)) (.seq (.op (.const 7 1)) (.op (.sub 6 7 6))))

def cell : Block := GramCopy.ifAddressEq 30 32 diagonal (.op (.const 6 0))

def program : Block := uniformTableBlock cell

def Keep (p : ℕ) := ¬TableScratch p ∧ p≠38 ∧ p≠39 ∧ p≠42
instance (p : ℕ) : Decidable (Keep p) := by unfold Keep; infer_instance

def delta {K : Type*} [Zero K] [One K] {n : ℕ} (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i=j ∧ i∉S then 1 else 0

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem callback {n mask out : ℕ} (S : Finset (Fin n)) (P : K → Prop) (h0 : P 0) (h1 : P 1)
    (v : Memory K) (z14 : v.index 14=0) (m162 : v.index 162=mask)
    (flags : ∀ i : Fin n,v.data (mask+i.val)=if i∈S then 1 else 0)
    (lo : 8 ≤ mask) (sep : mask+n ≤ out ∨ out+n*n ≤ mask) :
    TableCallbackSpec cell P (fun a=>8 ≤ a) Keep v n n out (delta S) (4*n+11) := by
  intro i j m hs i30 j32 inds words
  have mi14 := (inds 14 (Or.inr (by decide))).trans z14
  have mi162 := (inds 162 (Or.inr (by decide))).trans m162
  have mf : m.data (mask+i.val) = if i∈S then 1 else 0 :=
    (words _ (by omega) (by have := i.isLt; omega)).trans (flags i)
  by_cases hij : i=j
  · have eij : m.index 30 = m.index 32 := by rw [i30,j32,hij]
    obtain ⟨a,ea,ad,ai,av⟩ := cellAddress_spec (fun f=>∀ k,P (f k)) m hs 38 39 42 162 41 14 30 (by simp [CellScratchOK])
    have addr : a.index 38=mask+i.val := by simpa [mi162,mi14,i30] using av
    let b := a.putData 6 (a.data (a.index 38))
    have sb : b.AllData P := (show a.AllData P from ea.safe_end).putData 6 (ea.safe_end _)
    let c := b.putData 7 (1 : K)
    have sc : c.AllData P := sb.putData 7 h1
    have stored : c.data 6 = if i∈S then 1 else 0 := by
      calc
        c.data 6 = a.data (a.index 38) := by simp [c,b]
        _ = m.data (mask+i.val) := by rw [addr,ad]
        _ = _ := mf
    have sign : c.data 7 - c.data 6 = delta S i j := by
      rw [show c.data 7=1 by simp [c],stored]
      subst j
      by_cases active : i∈S <;> simp [delta,active]
    let t := c.putData 6 (c.data 7-c.data 6)
    have val : P (delta S i j) := by unfold delta; split <;> assumption
    have st : t.AllData P := sc.putData 6 (sign ▸ val)
    have eb := Block.Eval.op_load a 6 38 ea.safe_end sb
    have ec : Block.Eval (Memory.AllData P) (.op (.const 7 1)) b 1 c := by
      simpa only [Rat.cast_one] using Block.Eval.op_const b 7 1 sb (by simpa only [Rat.cast_one] using sc)
    have et := ea.seq (eb.seq (ec.seq (Block.Eval.op_sub c 6 7 6 sc st)))
    let cost := m.index 14*(4*m.index 41+5)+4*m.index 30+5+(1+(1+1))
    have explicitRun : Block.Eval (fun z : Memory K => ∀ k, P (z.data k)) diagonal m cost t := by
      simpa only [diagonal,cost,t] using et
    have policy : (fun z : Memory K => ∀ k, P (z.data k)) = Memory.AllData P := rfl
    have exactRun : Block.Eval (Memory.AllData P) diagonal m cost t :=
      Eq.mp (congrArg (fun Q : Memory K → Prop => Block.Eval Q diagonal m cost t) policy) explicitRun
    obtain ⟨l,hl,run⟩ := GramCopy.eval_ifAddressEq (safe:=Memory.AllData P)
      30 32 diagonal (.op (.const 6 0)) m t cost (by simpa only [ite_eq_left eij] using exactRun)
    refine ⟨t,l,?_,run,by simpa [t] using sign,?_,?_⟩
    · apply hl.trans
      have hi := i.isLt
      simp [cost,mi14,i30]
    · intro p hp
      have h6 : p≠6 := by omega
      have h7 : p≠7 := by omega
      simp [t,c,b,Memory.putData_ne _ h6,Memory.putData_ne _ h7,ad]
    · intro p hp
      rcases hp with hp | hp
      · unfold TableControl at hp
        exact ai _ (by omega) (by omega) (by omega)
      · exact ai _ hp.2.1 hp.2.2.1 hp.2.2.2
  · have ne : m.index 30 ≠ m.index 32 := fun h => hij (Fin.ext (i30.symm.trans (h.trans j32)))
    let t := m.putData 6 (0 : K)
    have st : t.AllData P := hs.putData 6 h0
    have e : Block.Eval (Memory.AllData P) (.op (.const 6 0)) m 1 t := by
      simpa only [Rat.cast_zero] using Block.Eval.op_const m 6 0 hs (by simpa only [Rat.cast_zero] using st)
    obtain ⟨l,hl,run⟩ := GramCopy.eval_ifAddressEq 30 32 diagonal (.op (.const 6 0)) m t 1
      (by simpa only [ne,ite_false] using e)
    exact ⟨t,l,by omega,run,by simp [t,delta,hij],fun a ha => Memory.putData_ne _ (by omega) _,fun _ _=>rfl⟩

/-- Ordinary RAM assembly of the exact restricted equations used by the marked oracle.
It reads the preserved matrix of opposite rows and the actual scalar mask. -/
theorem program_spec {s n base mask : ℕ} (E : Matrix (Fin s) (Fin n) K) (S : Finset (Fin n))
    (P : K→Prop) (h0 : P 0) (h1 : P 1) (v : Memory K) (hs : v.AllData P)
    (z14 : v.index 14=0) (m31 : v.index 31=n) (m33 : v.index 33=n) (m35 : v.index 35=base+s*n)
    (m162 : v.index 162=mask) (flags : ∀ i : Fin n,v.data (mask+i.val)=if i∈S then 1 else 0)
    (below : 8 ≤ base) (lo : 8 ≤ mask) (sep : mask+n ≤ base+s*n ∨ base+s*n+n*n ≤ mask)
    (top : uniformRect s n base v=E) :
    ∃ t c, c ≤ uniformTableTime n n (4*n+11) ∧ Block.Eval (Memory.AllData P) program v c t ∧
      uniformRect (s+n) n base t=maskedEquations E S ∧
      (∀ a,8 ≤ a→(a < base+s*n ∨ base+s*n+n*n ≤ a)→t.data a=v.data a) ∧
      ∀ p, TableParameter p ∨ Keep p → t.index p=v.index p := by
  obtain ⟨t,c,hc,e,lower,frame,ix⟩ := uniformTableBlock_spec cell P (fun a=>8 ≤ a) Keep v n n (base+s*n)
    (delta S) _ (callback S P h0 h1 v z14 m162 flags lo sep) (fun _ h=>h.1)
    (fun _ _=>by omega) m31 m33 m35 hs
  refine ⟨t,c,hc,e,?_,frame,ix⟩
  ext i j
  refine Fin.addCases (fun a=>?_) (fun a=>?_) i
  · have f:=frame (base+a.val*n+j.val) (by omega) (Or.inl (by have:=rectOffset_lt a j; omega))
    have v:=congrFun (congrFun top a) j
    change t.data (base+a.val*n+j.val) = Fin.append (fun i k=>E i k)
      (fun i=>if i∈S then (0 : Fin n→K) else (1 : Matrix (Fin n) (Fin n) K) i) (Fin.castAdd n a) j
    rw [Fin.append_left]
    exact f.trans v
  · have v:=congrFun (congrFun lower a) j
    change t.data ((base+s*n)+a.val*n+j.val)=delta S a j at v
    change t.data (base+(s+a.val)*n+j.val) = Fin.append (fun i k=>E i k)
      (fun i=>if i∈S then (0 : Fin n→K) else (1 : Matrix (Fin n) (Fin n) K) i) (Fin.natAdd s a) j
    rw [Fin.append_right,Nat.add_mul,←Nat.add_assoc,v]
    by_cases ha : a∈S
    · simp [delta,ha]
    · simp [delta,ha,Matrix.one_apply]

end MaskedTable
end Recovery
end LinearProgramming
end Optimization
end OAI
