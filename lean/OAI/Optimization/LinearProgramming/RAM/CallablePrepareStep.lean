import OAI.Optimization.LinearProgramming.RAM.CallablePrepareBase

/-! The high-cell loop copies a caller word at odd address to a callee word at even
address. Its two guards read the original source length headers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

def prepareScalarStep : Block :=
  .seq (.branch (.addrLT 0 113) (.op (.load 0 2)) (.op (.const 0 0))) (.op (.store 6 0))

def prepareAddressStep : Block :=
  .seq (.branch (.addrLT 0 117) (.seq (.op (.addrLoad 8 4)) (.op (.decr 8 8)))
      (.op (.addrConst 8 0))) (.op (.addrStore 6 8))

def prepareAdvance : Block :=
  .seq (bumpIndex 0 2) (.seq (bumpIndex 2 2) (.seq (bumpIndex 4 2) (bumpIndex 6 2)))

def prepareStep : Block := .seq prepareScalarStep (.seq prepareAddressStep prepareAdvance)

def scalarStepMem {K : Type*} (m : Memory K) (j : ℕ) (v : K) : Memory K :=
  (m.putData 0 v).putData (2*j) v

def addressStepMem {K : Type*} (m : Memory K) (j v : ℕ) : Memory K :=
  (m.putIndex 8 (2*v)).putIndex (2*j) (2*v)

def advanceMem {K : Type*} (m : Memory K) : Memory K :=
  (((m.putIndex 0 (m.index 0+2)).putIndex 2 (m.index 2+2)).putIndex 4
    (m.index 4+2)).putIndex 6 (m.index 6+2)

def afterPrepareStep {K : Type*} (m : Memory K) (j : ℕ) (x : K) (v : ℕ) : Memory K :=
  advanceMem (addressStepMem (scalarStepMem m j x) j v)

theorem odd_scalarStepMem {K : Type*} (m : Memory K) (j : ℕ) (v : K) :
    OddFrame m (scalarStepMem m j v) := ((OddFrame.refl m).putData 0 v).putData j v

theorem odd_afterPrepareStep {K : Type*} (m : Memory K) (j : ℕ) (x : K) (v : ℕ) :
    OddFrame m (afterPrepareStep m j x v) :=
  ((((((odd_scalarStepMem m j x).putIndex 4 _).putIndex j _).putIndex 0 _).putIndex 1 _).putIndex 2 _).putIndex 3 _

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem prepareScalarStep_spec (m : Memory K) (sb ab B j : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hc : m.index 0=2*j+1)
    (hp : m.index 2=2*(sb+j)+1) (hd : m.index 6=2*j) (hm : m.AllData P) (hz : P 0) :
    ∃ k ≤ 4, Block.Eval (Memory.AllData P) prepareScalarStep m k (scalarStepMem m j (xs[j]?.getD 0)) := by
  let x := xs[j]?.getD 0
  let u := m.putData 0 x
  have protect (hx : P x) : Block.Eval (Memory.AllData P) (.op (.store 6 0)) u 1 (scalarStepMem m j x) := by
    have hu := hm.putData 0 hx
    have e := Block.Eval.op_store (safe := Memory.AllData P) u 6 0 hu (hu.putData _ (hu 0))
    simpa [scalarStepMem,u,hd] using e
  by_cases hit : j<xs.length
  · have val : m.data (m.index 2)=x := by simp [x,hp,src.scalarAt j hit,List.getElem?_eq_getElem hit]
    have hx : P x := val ▸ hm (m.index 2)
    have e := Block.Eval.op_load (safe := Memory.AllData P) m 0 2 hm (hm.putData _ (hm _))
    have read : Block.Eval (Memory.AllData P) (.op (.load 0 2)) m 1 u := by simpa [u,val] using e
    have htest : (Cond.addrLT 0 113).test m=true := by simp [Cond.test,hc,src.scalarLength]; omega
    exact ⟨4,le_rfl,(Block.Eval.branchTrue (b := .op (.const 0 0)) htest read).seq (protect hx)⟩
  · have val : x=0 := by simp [x,List.getElem?_eq_none (Nat.le_of_not_gt hit)]
    have hx : P x := val ▸ hz
    have e := Block.Eval.op_const (safe := Memory.AllData P) m 0 0 hm
      (hm.putData 0 (show P ((0:ℚ) : K) by simpa using hz))
    have zero : Block.Eval (Memory.AllData P) (.op (.const 0 0)) m 1 u := by simpa [u,val] using e
    have htest : (Cond.addrLT 0 113).test m=false := by simp [Cond.test,hc,src.scalarLength]; omega
    exact ⟨3,by decide,(Block.Eval.branchFalse (a := .op (.load 0 2)) htest zero).seq (protect hx)⟩

theorem prepareAddressStep_spec (m : Memory K) (sb ab B j : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hc : m.index 0=2*j+1)
    (hp : m.index 4=2*(ab+j)+1) (hd : m.index 6=2*j) (hm : m.AllData P) :
    ∃ k ≤ 5, Block.Eval (Memory.AllData P) prepareAddressStep m k
      (addressStepMem m j (dims[j]?.getD 0)) := by
  let x := dims[j]?.getD 0
  let u := m.putIndex 8 (2*x)
  have protect : Block.Eval (Memory.AllData P) (.op (.addrStore 6 8)) u 1 (addressStepMem m j x) := by
    have e := Block.Eval.op_addrStore (safe := Memory.AllData P) u 6 8 hm hm
    simpa [addressStepMem,u,hd] using e
  by_cases hit : j<dims.length
  · have val : m.index (m.index 4)=2*x+1 := by
      simp [x,hp,src.addressAt j hit,List.getElem?_eq_getElem hit]
    let v := m.putIndex 8 (2*x+1)
    have read : Block.Eval (Memory.AllData P) (.op (.addrLoad 8 4)) m 1 v := by
      simpa [v,val] using Block.Eval.op_addrLoad (safe := Memory.AllData P) m 8 4 hm hm
    have decr : Block.Eval (Memory.AllData P) (.op (.decr 8 8)) v 1 u := by
      have e := Block.Eval.op_decr (safe := Memory.AllData P) v 8 8 hm hm
      simpa [v,u,Memory.putIndex,Function.update_idem] using e
    have htest : (Cond.addrLT 0 117).test m=true := by simp [Cond.test,hc,src.addressLength]; omega
    exact ⟨5,le_rfl,(Block.Eval.branchTrue (b := .op (.addrConst 8 0)) htest (read.seq decr)).seq protect⟩
  · have val : x=0 := by simp [x,List.getElem?_eq_none (Nat.le_of_not_gt hit)]
    have zero : Block.Eval (Memory.AllData P) (.op (.addrConst 8 0)) m 1 u := by
      simpa [u,val] using Block.Eval.op_addrConst (safe := Memory.AllData P) m 8 0 hm hm
    have htest : (Cond.addrLT 0 117).test m=false := by simp [Cond.test,hc,src.addressLength]; omega
    exact ⟨3,by decide,(Block.Eval.branchFalse (a := .seq (.op (.addrLoad 8 4)) (.op (.decr 8 8))) htest zero).seq protect⟩

theorem prepareAdvance_spec (m : Memory K) (hm : m.AllData P) :
    Block.Eval (Memory.AllData P) prepareAdvance m 8 (advanceMem m) := by
  let a := m.putIndex 0 (m.index 0+2)
  let b := a.putIndex 2 (a.index 2+2)
  let c := b.putIndex 4 (b.index 4+2)
  have h := (bumpIndex_spec m 0 2 hm).seq ((bumpIndex_spec a 2 2 hm).seq
    ((bumpIndex_spec b 4 2 hm).seq (bumpIndex_spec c 6 2 hm)))
  simpa [prepareAdvance,advanceMem,c,b,a] using h

theorem prepareStep_spec (m : Memory K) (sb ab B j : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hc : m.index 0=2*j+1)
    (hsp : m.index 2=2*(sb+j)+1) (hap : m.index 4=2*(ab+j)+1)
    (hd : m.index 6=2*j) (hm : m.AllData P) (hz : P 0) :
    ∃ k ≤ 17, Block.Eval (Memory.AllData P) prepareStep m k
      (afterPrepareStep m j (xs[j]?.getD 0) (dims[j]?.getD 0)) := by
  let s := scalarStepMem m j (xs[j]?.getD 0)
  let a := addressStepMem s j (dims[j]?.getD 0)
  obtain ⟨r,hr,er⟩ := prepareScalarStep_spec m sb ab B j xs dims src hc hsp hd hm hz
  obtain ⟨q,hq,eq⟩ := prepareAddressStep_spec s sb ab B j xs dims
    (src.ofOdd (odd_scalarStepMem ..)) hc hap hd er.safe_end
  exact ⟨r+(q+8),by omega,er.seq (eq.seq (prepareAdvance_spec a eq.safe_end))⟩

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
