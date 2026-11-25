import OAI.Optimization.LinearProgramming.Compression.ServiceGeneratorTable
import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan
import OAI.Optimization.LinearProgramming.Compression.ServiceReadHeader
import OAI.Optimization.LinearProgramming.Compression.UniformIndex

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

private def tableRegisters : List AddressSet := [.fix 0 1,.fix 1 0,.fix 2 2,.fix 3 0,
  .fix 14 7,.next 15 17,.fix 16 0,.fix 18 3,.fix 19 0]

/-- Recover the two dimensions actually used by lookup from persistent scalars, then compute
all table addresses. The incoming address-bank request occupies registers numbered at least 40. -/
def prepareTable : Block := .seq (headerToAddress 3 22) (.seq (headerToAddress 4 17)
  (.seq (addressPlan tableRegisters) (.seq (cellAddress 14 10 11 14 22 22 3)
    (.seq (cellAddress 18 10 11 18 22 2 3) (.seq (cellAddress 21 10 11 14 18 15 3)
      (.op (.addrCopy 20 14)))))))

def prepareCost (n g : ℕ) : ℕ := (4*n+4)+((4*g+4)+(9+((n*(4*n+5)+5)+
  ((2*(4*n+5)+5)+((g+1)*(4*stride n+5)+5+1)))))

structure Prepared {K : Type*} (n g : ℕ) (s t : Memory K) : Prop where
  count : t.index 17=g
  width : t.index 18=stride n
  matrixEnd : t.index 14=tableBase n
  first : t.index 20=tableBase n
  incoming : t.index 21=slotBase n (g+1)
  dimension : t.index 22=n
  one : t.index 0=1
  found : t.index 1=0
  two : t.index 2=2
  zero : t.index 3=0
  counter : t.index 16=0
  rank : t.index 19=0
  indices : ∀ a, 40≤a → t.index a=s.index a
  data : ∀ a, a≠0 → a≠6 → t.data a=s.data a

set_option maxHeartbeats 1200000 in
/-- No precomputed row address, generator count address, or matrix-end pointer is required. -/
theorem prepareTable_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (n g : ℕ)
    (hn : s.data 3=(n:K)) (hg : s.data 4=(g:K)) (hs : ∀ a,P (s.data a))
    (h1 : P 1) (hv : ∀ j≤max n g,P (j:K)) :
    ∃ t, Block.Eval (fun z => ∀a,P (z.data a)) prepareTable s (prepareCost n g) t ∧ Prepared n g s t := by
  let safe := fun z : Memory K => ∀a,P (z.data a)
  obtain ⟨a,ea,a22,ai,ad⟩ := headerToAddress_spec P s 3 22 n (by decide) (by decide) hn hs h1
    (fun j hj => hv j (hj.trans (le_max_left _ _)))
  obtain ⟨b,eb,b17,bi,bd⟩ := headerToAddress_spec P a 4 17 g (by decide) (by decide)
    ((ad 4 (by decide) (by decide)).trans hg) ea.safe_end h1 (fun j hj => hv j (hj.trans (le_max_right _ _)))
  let c := applyPlan tableRegisters b
  have ec : Block.Eval safe (addressPlan tableRegisters) b 9 c :=
    addressPlan_spec (fun z => ∀a,P (z a)) tableRegisters b eb.safe_end
  have c14 : c.index 14=7 := by simp [c,tableRegisters,applyPlan,AddressSet.apply]
  have c18 : c.index 18=3 := by simp [c,tableRegisters,applyPlan,AddressSet.apply]
  have c2 : c.index 2=2 := by simp [c,tableRegisters,applyPlan,AddressSet.apply]
  have c3 : c.index 3=0 := by simp [c,tableRegisters,applyPlan,AddressSet.apply]
  have c15 : c.index 15=g+1 := by simp [c,tableRegisters,applyPlan,AddressSet.apply,b17]
  have c22 : c.index 22=n := by simp [c,tableRegisters,applyPlan,AddressSet.apply,bi 22 (by decide),a22]
  obtain ⟨d,ed,dd,di,d14⟩ := cellAddress_spec (fun f => ∀ x,P (f x)) c ec.safe_end 14 10 11 14 22 22 3 (by simp [CellScratchOK])
  simp only [c14,c22,c3,Nat.mul_zero,Nat.add_zero] at ed d14
  have d2 := (di 2 (by decide) (by decide) (by decide)).trans c2
  have d3 := (di 3 (by decide) (by decide) (by decide)).trans c3
  have d18 := (di 18 (by decide) (by decide) (by decide)).trans c18
  have d22 := (di 22 (by decide) (by decide) (by decide)).trans c22
  obtain ⟨e,ee,edat,ei,e18⟩ := cellAddress_spec (fun f => ∀ x,P (f x)) d ed.safe_end 18 10 11 18 22 2 3 (by simp [CellScratchOK])
  simp only [d2,d3,d18,d22,Nat.mul_zero,Nat.add_zero] at ee e18
  have e14 : e.index 14=tableBase n := (ei 14 (by decide) (by decide) (by decide)).trans d14
  have e15 := (ei 15 (by decide) (by decide) (by decide)).trans ((di 15 (by decide) (by decide) (by decide)).trans c15)
  have e3 := (ei 3 (by decide) (by decide) (by decide)).trans d3
  have es : e.index 18=stride n := by simpa [stride,Nat.add_comm] using e18
  obtain ⟨f,ef,fd,fi,f21⟩ := cellAddress_spec (fun z => ∀ x,P (z x)) e ee.safe_end 21 10 11 14 18 15 3 (by simp [CellScratchOK])
  simp only [e3,e14,e15,es,Nat.mul_zero,Nat.add_zero] at ef f21
  let t := f.putIndex 20 (f.index 14)
  have et : Block.Eval safe (.op (.addrCopy 20 14)) f 1 t := Block.Eval.op_addrCopy _ _ _ ef.safe_end ef.safe_end
  have tx (p : ℕ) (h : p≠20 ∧ p≠21 ∧ p≠18 ∧ p≠14 ∧ p≠10 ∧ p≠11) : t.index p=c.index p := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := h
    simpa [t,h1] using (fi p h2 h5 h6).trans ((ei p h3 h5 h6).trans (di p h4 h5 h6))
  have f14 := (fi 14 (by decide) (by decide) (by decide)).trans e14
  refine ⟨t,ea.seq (eb.seq (ec.seq (ed.seq (ee.seq (ef.seq et))))),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [tx 17 (by decide),c,tableRegisters,applyPlan,AddressSet.apply] using b17
  · simpa [t] using (fi 18 (by decide) (by decide) (by decide)).trans es
  · simpa [t] using f14
  · simp [t,f14]
  · simpa [t,slotBase] using f21
  · exact (tx 22 (by decide)).trans c22
  · simp [tx 0 (by decide),c,tableRegisters,applyPlan,AddressSet.apply]
  · simp [tx 1 (by decide),c,tableRegisters,applyPlan,AddressSet.apply]
  · exact (tx 2 (by decide)).trans c2
  · exact (tx 3 (by decide)).trans c3
  · simp [tx 16 (by decide),c,tableRegisters,applyPlan,AddressSet.apply]
  · simp [tx 19 (by decide),c,tableRegisters,applyPlan,AddressSet.apply]
  · intro p hp
    have h : ∀ j≤22,p≠j := by omega
    simpa [tx p (by omega),c,tableRegisters,applyPlan,AddressSet.apply,h _ (by decide : 19≤22),h _ (by decide : 18≤22),
      h _ (by decide : 16≤22),h _ (by decide : 15≤22),h _ (by decide : 14≤22),h _ (by decide : 3≤22),
      h _ (by decide : 2≤22),h _ (by decide : 1≤22),h _ (by decide : 0≤22)] using
      (bi p (h 17 (by decide))).trans (ai p (h 22 (by decide)))
  · intro p hp hq
    change f.data p=s.data p
    rw [fd,edat,dd,show c.data=b.data from applyPlan_data _ _,bd p hp hq,ad p hp hq]

theorem prepareCost_le (n g : ℕ) : prepareCost n g ≤ 100*(g+1)*(n+1)^2 := by
  unfold prepareCost stride; ring_nf; omega

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
