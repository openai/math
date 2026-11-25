import OAI.Optimization.LinearProgramming.Recovery.SupportBundleContext
import OAI.Optimization.LinearProgramming.RAM.FrameFirstHeader
import OAI.Optimization.LinearProgramming.RAM.FrameHeaders

/-! Select the opposite block in place after the first marked-subspace decision.
In the primal branch it is the second packed matrix, and in the dual branch it is the
first. The support flags use the n scalar cells immediately following the selected rows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace SupportBundle

open RAM RAM.Call RAM.Callable RAM.Tape Geometry

private def capTerm (coefficient degree : ℕ) : AddressTerm 520 :=
  .val coefficient * addressPower ((.reg 28)+(.reg 29)+2) degree+2

def capacity (c k m d : ℕ) := polyBound c k (m+d+1)+2

private def plan (positive : Bool) (c k : ℕ) : HeaderPlan 520 :=
  let source : AddressTerm 520:=if positive then (.reg 55)+(.reg 208)*(.reg 150) else .reg 55
  let height : AddressTerm 520:=if positive then .reg 209 else .reg 208
  let n : AddressTerm 520:=.reg 150
  [(60,capTerm c k),(150,(.reg 28)+1),(512,height),(513,n),(156,.reg 154),(55,source),
   (151,(.reg 55)+(.reg 512)*n),(56,(.reg 512)*n+n),(57,.val 512),(58,.val 2)]

def select (c k : ℕ) : Block := .seq (.op (.addrConst 159 0)) (.branch (.addrLT 159 154)
  (HeaderPlan.code 530 (plan true c k)) (HeaderPlan.code 530 (plan false c k)))

noncomputable def selectTime (c k : ℕ) : Polynomial ℕ := (plan true c k).budget+(plan false c k).budget+3

def selectedHeight (b : Bool) (k s : ℕ) := if b then s else k
def selectedBase (b : Bool) (out k n : ℕ) := if b then out+k*n else out

private theorem values (b : Bool) (c k : ℕ) (f : Fin 520→ℕ) : let g:=(plan b c k).output f
    let n:=f 28+1
    let h:=selectedHeight b (f 208) (f 209)
    let src:=selectedBase b (f 55) (f 208) n
    g 55=src ∧ g 56=h*n+n ∧ g 57=512 ∧ g 58=2 ∧ g 60=(capTerm c k).value f ∧ g 512=h ∧ g 513=n ∧
    g 156=f 154 ∧ g 150=n ∧ g 151=src+h*n ∧ g 24=f 24 ∧ g 28=f 28 ∧ g 29=f 29 := by
  cases b <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem capTerm_value (c k : ℕ) (f : Fin 520→ℕ) : (capTerm c k).value f=capacity c k (f 28) (f 29) := by
  let base : AddressTerm 520 := .reg 28 + .reg 29 + 2
  exact congrArg (fun v : ℕ => c * v + 2) (addressPower_value base k f)

theorem select_run {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c k m d rowsD rowsE out limit : ℕ) (b : Bool) (a : Memory K) (P : K→Prop)
    (E : Matrix (Fin (selectedHeight b rowsD rowsE)) (Fin (m+1)) K) (safe : a.AllData P)
    (shape : uniformRect (selectedHeight b rowsD rowsE) (m+1) (selectedBase b out rowsD (m+1)) a=E)
    (m28 : a.index 28=m) (m29 : a.index 29=d) (ptr : a.index 55=out) (k208 : a.index 208=rowsD)
    (s209 : a.index 209=rowsE) (answer : a.index 154=b.toNat) (bounded : ∀ j,a.index j ≤ limit) :
    ∃ t q,q ≤ (selectTime c k).eval limit ∧ Block.Eval (Memory.AllData P) (select c k) a q t ∧
      Context E b (selectedBase b out rowsD (m+1)) (capacity c k m d) t ∧ t.data=a.data ∧
      t.index 24=a.index 24 ∧ t.index 28=m ∧ t.index 29=d := by
  let u:=a.putIndex 159 0
  let f:=fun j : Fin 520=>u.index j.val
  have first:=Block.Eval.op_addrConst (safe:=Memory.AllData P) a 159 0 safe safe
  obtain ⟨t,q,e,time,data,registers⟩:=(plan b c k).correct 530 (by decide) u f (fun _=>rfl) (show u.AllData P from safe)
  have ub (i : Fin 520) : f i ≤ limit := by
    by_cases hi : i.val=159
    · simp [f,u,hi]
    · simpa [f,u,Memory.putIndex_ne _ hi] using bounded i.val
  have count:=time.trans ((plan b c k).cost_le _ _ ub)
  obtain ⟨a55,a56,a57,a58,a60,a512,a513,a156,a150,a151,a24,a28,a29⟩:=values b c k f
  have f28 : f 28=m:=m28
  have f29 : f 29=d:=m29
  have f154 : f 154=b.toNat:=answer
  have f208 : f 208=rowsD:=k208
  have f209 : f 209=rowsE:=s209
  have f55 : f 55=out:=ptr
  rw [f55,f208,f28] at a55
  rw [f208,f209,f28] at a56
  rw [capTerm_value,f28,f29] at a60
  rw [f208,f209] at a512
  rw [f28] at a513 a150
  rw [f154] at a156
  rw [f55,f208,f209,f28] at a151
  have ctx : Context E b (selectedBase b out rowsD (m+1)) (capacity c k m d) t := by
    refine ⟨(registers 55).trans a55,(registers 56).trans a56,(registers 57).trans a57,(registers 58).trans a58,
      (registers 60).trans a60,(registers 512).trans a512,(registers 513).trans a513,(registers 156).trans a156,
      (registers 150).trans a150,(registers 151).trans a151,?_⟩
    ext i j
    exact (congrFun data _).trans (congrFun (congrFun shape i) j)
  have test : (Cond.addrLT 159 154).test u=b := by cases b <;> simp [Cond.test,u,answer]
  have ends:=And.intro ((registers 24).trans a24) (And.intro ((registers 28).trans (a28.trans f28)) ((registers 29).trans (a29.trans f29)))
  cases b with
  | false =>
    refine ⟨t,_,?_,first.seq (Block.Eval.branchFalse test e),ctx,data,ends⟩
    simp only [selectTime,Polynomial.eval_add,Polynomial.eval_ofNat];omega
  | true =>
    refine ⟨t,_,?_,first.seq (Block.Eval.branchTrue test e),ctx,data,ends⟩
    simp only [selectTime,Polynomial.eval_add,Polynomial.eval_ofNat];omega

end SupportBundle
end Recovery
end LinearProgramming
end Optimization
end OAI
