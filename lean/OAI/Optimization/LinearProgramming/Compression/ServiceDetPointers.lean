import OAI.Optimization.LinearProgramming.Compression.ServiceDetLayout
import OAI.Optimization.LinearProgramming.Compression.ServiceTableAddress

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def chooseMatrix : Block := .branch (.addrLT 6 43)
  (cellAddress 0 10 11 12 22 13 6) (.op (.addrCopy 0 12))

private def matrixCost (tag d n : ℕ) := if tag = 0 then 2 else d*(4*n+5)+7

private theorem chooseMatrix_spec (P : K→Prop) (s : Memory K) (tag d n : ℕ)
    (hbit : tag ≤ 1) (h6 : s.index 6 = 0) (h12 : s.index 12 = 7) (h13 : s.index 13 = d)
    (h22 : s.index 22 = n) (h43 : s.index 43 = tag) (hs : ∀ a,P (s.data a)) :
    ∃t,Block.Eval (fun z => ∀ a,P (z.data a)) chooseMatrix s (matrixCost tag d n) t ∧
      t.index 0 = (if tag = 0 then 7 else 7+d*n) ∧ t.data = s.data ∧
      ∀ j,j ≠ 0 → j ≠ 10 → j ≠ 11 → t.index j = s.index j := by
  by_cases ht : tag = 0
  · let t := s.putIndex 0 (s.index 12)
    have et : Block.Eval (fun z => ∀ a,P (z.data a)) (.op (.addrCopy 0 12)) s 1 t := Block.Eval.op_addrCopy _ _ _ hs hs
    refine ⟨t,?_,by simp [t,ht,h12],rfl,fun j h0 _ _ => by simp [t,h0]⟩
    simpa [matrixCost,ht,chooseMatrix] using (Block.Eval.branchFalse (a := cellAddress 0 10 11 12 22 13 6)
      (c := Cond.addrLT 6 43) (by simp [Cond.test,h43,ht,h6]) et)
  · have ho : tag = 1 := by omega
    obtain ⟨t,et,td,ti,t0⟩ := cellAddress_spec (fun f => ∀ j,P (f j)) s hs 0 10 11 12 22 13 6 (by simp [CellScratchOK])
    rw [h6,h13,h22] at et
    refine ⟨t,?_,by simpa [h12,h13,h22,h6,ht] using t0,td,ti⟩
    unfold chooseMatrix matrixCost
    rw [ite_eq_right ht]
    convert Block.Eval.branchTrue (c := Cond.addrLT 6 43) (by simp [Cond.test,h6,h43,ho]) et using 1
    omega

private def detRegisters : List AddressSet := [.read 1 22,.read 2 42,.next 3 40,.next 3 3,
  .fix 6 0,.fix 12 7,.next 5 30,.next 5 5,.next 5 5,.next 5 5]

/-- Set the callable minor ABI using the scalar row count and the protected request address
bank. The reserved scalar frame follows the candidate's slot. -/
def prepareDet : Block := .seq (headerToAddress 1 13) (.seq (cellAddress 30 10 11 21 22 3 18)
  (.seq (addressPlan detRegisters) (.seq chooseMatrix (cellAddress 4 10 11 3 22 6 42))))

def detPointerCost (n d k tag : ℕ) := (4*d+4)+((4*stride n+5)+(10+(matrixCost tag d n+(4*k+5))))

set_option maxHeartbeats 1100000 in
theorem prepareDet_spec {d e n : ℕ} (u : PairMinorIndex d e n) (g : ℕ) (P : K→Prop) (s : Memory K)
    (hd : s.data 1 = (d:K)) (hw : Wire u s) (h3 : s.index 3 = 0) (h18 : s.index 18 = stride n)
    (h21 : s.index 21 = slotBase n (g+1)) (h22 : s.index 22 = n)
    (hs : ∀ a,P (s.data a)) (hone : P 1) (hv : ∀ j ≤ d,P (j:K)) :
    ∃t,Block.Eval (fun z => ∀ a,P (z.data a)) prepareDet s (detPointerCost n d (order u) (tag u)) t ∧
      DetParameters u g t ∧ (∀ a,40 ≤ a → t.index a = s.index a) ∧ ∀ a,a ≠ 0 → a ≠ 6 → t.data a = s.data a := by
  obtain ⟨a,ea,a13,ai,ad⟩ := headerToAddress_spec P s 1 13 d (by decide) (by decide) hd hs hone hv
  obtain ⟨b,eb,bd,bi,b30⟩ := cellAddress_spec (fun f => ∀ j,P (f j)) a ea.safe_end 30 10 11 21 22 3 18 (by simp [CellScratchOK])
  have a3 := (ai 3 (by decide)).trans h3
  have a18 := (ai 18 (by decide)).trans h18
  have a21 := (ai 21 (by decide)).trans h21
  rw [a3,a18] at eb b30
  simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add] at eb b30
  have bx (j : ℕ) (h₁ : j ≠ 30) (h₂ : j ≠ 10) (h₃ : j ≠ 11) (h₄ : j ≠ 13) : b.index j = s.index j := (bi j h₁ h₂ h₃).trans (ai j h₄)
  have bf : b.index 30 = slotBase n (g+2) := by rw [b30,a21]; simp [slotBase,Nat.add_mul,two_mul,Nat.add_assoc]
  let c := applyPlan detRegisters b
  have ec : Block.Eval (fun z => ∀ a,P (z.data a)) (addressPlan detRegisters) b 10 c := addressPlan_spec (fun f => ∀ j,P (f j)) _ _ eb.safe_end
  have cx (j : ℕ) (h : j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3 ∧ j ≠ 6 ∧ j ≠ 12 ∧ j ≠ 5) : c.index j = b.index j := by
    obtain ⟨h1,h2,h3,h6,h12,h5⟩ := h; simp [c,detRegisters,applyPlan,AddressSet.apply,h1,h2,h3,h6,h12,h5]
  have b22 := (bx 22 (by decide) (by decide) (by decide) (by decide)).trans h22
  have b42 := (bx 42 (by decide) (by decide) (by decide) (by decide)).trans hw.size
  have b40 := bx 40 (by decide) (by decide) (by decide) (by decide)
  have c1 : c.index 1 = n := by simp [c,detRegisters,applyPlan,AddressSet.apply,b22]
  have c2 : c.index 2 = order u := by simp [c,detRegisters,applyPlan,AddressSet.apply,b42]
  have c3 : c.index 3 = s.index 40+2 := by simp [c,detRegisters,applyPlan,AddressSet.apply,b40,Nat.add_assoc]
  have c5 : c.index 5 = slotBase n (g+2)+4 := by simp [c,detRegisters,applyPlan,AddressSet.apply,bf,Nat.add_assoc]
  have c6 : c.index 6 = 0 := by simp [c,detRegisters,applyPlan,AddressSet.apply]
  have c12 : c.index 12 = 7 := by simp [c,detRegisters,applyPlan,AddressSet.apply]
  have c13 := (cx 13 (by decide)).trans ((bi 13 (by decide) (by decide) (by decide)).trans a13)
  have c22 := (cx 22 (by decide)).trans b22
  have c43 := (cx 43 (by decide)).trans ((bx 43 (by decide) (by decide) (by decide) (by decide)).trans hw.side)
  obtain ⟨e,ee,e0,ed,ei⟩ := chooseMatrix_spec P c (tag u) d n (tag_le _) c6 c12 c13 c22 c43 ec.safe_end
  have e6 := (ei 6 (by decide) (by decide) (by decide)).trans c6
  have e42 := (ei 42 (by decide) (by decide) (by decide)).trans ((cx 42 (by decide)).trans b42)
  obtain ⟨t,et,td,ti,t4⟩ := cellAddress_spec (fun f => ∀ j,P (f j)) e ee.safe_end 4 10 11 3 22 6 42 (by simp [CellScratchOK])
  rw [e6,e42] at et t4
  simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add] at et t4
  have tx (j : ℕ) (h₁ : j ≠ 4) (h₂ : j ≠ 10) (h₃ : j ≠ 11) (h₄ : j ≠ 0) : t.index j = c.index j := (ti j h₁ h₂ h₃).trans (ei j h₄ h₂ h₃)
  have high (j : ℕ) (hj : 40 ≤ j) : t.index j = s.index j := (tx j (by omega) (by omega) (by omega) (by omega)).trans
    ((cx j (by omega)).trans (bx j (by omega) (by omega) (by omega) (by omega)))
  refine ⟨t,ea.seq (eb.seq (ec.seq (ee.seq et))),?_,high,?_⟩
  · exact ⟨(ti 0 (by decide) (by decide) (by decide)).trans e0,(tx 1 (by decide) (by decide) (by decide) (by decide)).trans c1,
      (tx 2 (by decide) (by decide) (by decide) (by decide)).trans c2,by rw [high 40 (by decide)]; exact (tx 3 (by decide) (by decide) (by decide) (by decide)).trans c3,
      by rw [high 40 (by decide),t4,ei 3 (by decide) (by decide) (by decide),c3],
      (tx 5 (by decide) (by decide) (by decide) (by decide)).trans c5,
      (tx 30 (by decide) (by decide) (by decide) (by decide)).trans ((cx 30 (by decide)).trans bf)⟩
  · intro j h0 h6
    rw [td,ed,show c.data = b.data from applyPlan_data _ _,bd,ad j h0 h6]

theorem detPointerCost_le (n d k tag : ℕ) (hd : d ≤ n) (hk : k ≤ n) :
    detPointerCost n d k tag ≤ 80*(n+1)^2 := by
  have h := Nat.mul_le_mul_right (4*n+5) hd
  unfold detPointerCost matrixCost stride
  split <;> ring_nf at * <;> omega

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
