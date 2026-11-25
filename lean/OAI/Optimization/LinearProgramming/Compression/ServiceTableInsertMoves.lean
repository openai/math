import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan
import OAI.Optimization.LinearProgramming.Compression.UniformIndex

/-! Native pointer setup and count publication for inserting a scalar record. These
operations depend only on integer offsets and the scalar RAM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def movePointers : List AddressSet := [.read 8 20,.read 9 21,.fix 15 0]
private def copyPointers : List AddressSet := [.read 9 8,.read 8 21,.read 11 18]

def openInsertion : Block := .seq (addressPlan movePointers) (cellAddress 10 11 12 14 18 19 15)
def prepareFill : Block := addressPlan copyPointers
def publishCount : Block := .seq (.op (.const 0 1)) (.op (.add 4 4 0))

/-- The source and destination stops are copied and the rank pointer is calculated at runtime. -/
theorem openInsertion_spec (P : K→Prop) (s : Memory K) (base width pos : ℕ)
    (h14 : s.index 14 = base) (h18 : s.index 18 = width) (h19 : s.index 19 = pos) (hs : ∀ a,P (s.data a)) :
    ∃t,Block.Eval (fun z => ∀ a,P (z.data a)) openInsertion s (3+(pos*(4*width+5)+5)) t ∧
      t.data = s.data ∧ t.index 8 = s.index 20 ∧ t.index 9 = s.index 21 ∧ t.index 10 = base+pos*width ∧
      ∀ j,j ≥ 17 → t.index j = s.index j := by
  let a := applyPlan movePointers s
  have ea : Block.Eval (fun z => ∀ a,P (z.data a)) (addressPlan movePointers) s 3 a := addressPlan_spec (fun f => ∀ j,P (f j)) _ _ hs
  have a8 : a.index 8 = s.index 20 := by simp [a,movePointers,applyPlan,AddressSet.apply]
  have a9 : a.index 9 = s.index 21 := by simp [a,movePointers,applyPlan,AddressSet.apply]
  have a15 : a.index 15 = 0 := by simp [a,movePointers,applyPlan,AddressSet.apply]
  have ai (i : ℕ) (h₁ : i ≠ 8) (h₂ : i ≠ 9) (h₃ : i ≠ 15) : a.index i = s.index i := by simp [a,movePointers,applyPlan,AddressSet.apply,h₁,h₂,h₃]
  have a14 := (ai 14 (by decide) (by decide) (by decide)).trans h14
  have a18 := (ai 18 (by decide) (by decide) (by decide)).trans h18
  have a19 := (ai 19 (by decide) (by decide) (by decide)).trans h19
  obtain ⟨b,eb,bd,bi,b10⟩ := cellAddress_spec (fun f => ∀ j,P (f j)) a ea.safe_end 10 11 12 14 18 19 15 (by simp [CellScratchOK])
  simp only [a14,a18,a19,a15,Nat.mul_zero,Nat.add_zero] at eb b10
  exact ⟨b,ea.seq eb,bd.trans (applyPlan_data _ _),(bi 8 (by decide) (by decide) (by decide)).trans a8,
    (bi 9 (by decide) (by decide) (by decide)).trans a9,b10,
    fun j hj => (bi j (by omega) (by omega) (by omega)).trans (ai j (by omega) (by omega) (by omega))⟩

/-- Set up a forward copy of the staged record into the hole left by the backward move. -/
theorem prepareFill_spec (P : K→Prop) (s : Memory K) (hs : ∀ a,P (s.data a)) :
    ∃t,Block.Eval (fun z => ∀ a,P (z.data a)) prepareFill s 3 t ∧ t.data = s.data ∧
      t.index 8 = s.index 21 ∧ t.index 9 = s.index 8 ∧ t.index 11 = s.index 18 ∧
      ∀ j,17 ≤ j → t.index j = s.index j := by
  let t := applyPlan copyPointers s
  refine ⟨t,addressPlan_spec (fun f => ∀ j,P (f j)) copyPointers s hs,applyPlan_data _ _,?_,?_,?_,?_⟩
  · simp [t,copyPointers,applyPlan,AddressSet.apply]
  · simp [t,copyPointers,applyPlan,AddressSet.apply]
  · simp [t,copyPointers,applyPlan,AddressSet.apply]
  · intro j hj
    simp [t,copyPointers,applyPlan,AddressSet.apply,show j ≠ 8 by omega,show j ≠ 9 by omega,show j ≠ 11 by omega]

/-- Publish an additional record only after it has been written. -/
theorem publishCount_spec (P : K→Prop) (s : Memory K) (hs : ∀ a,P (s.data a)) (hone : P 1)
    (hnext : P (s.data 4+1)) :
    ∃t,Block.Eval (fun z => ∀ a,P (z.data a)) publishCount s 2 t ∧ t.data 4 = s.data 4+1 ∧
      t.index = s.index ∧ ∀ j,j ≠ 0 → j ≠ 4 → t.data j = s.data j := by
  let a := s.putData 0 ((1:ℚ):K)
  let t := a.putData 4 (a.data 4+a.data 0)
  have put {m : Memory K} {j : ℕ} {v : K} (hm : ∀ i,P (m.data i)) (hv : P v) : ∀ i,P ((m.putData j v).data i) := by
    intro i;by_cases h : i = j
    · simpa [h] using hv
    · simpa [h] using hm i
  have ha : ∀ j,P (a.data j) := put hs (by simpa using hone)
  have ht : ∀ j,P (t.data j) := put ha (by simpa [a] using hnext)
  have ea : Block.Eval (fun z => ∀ j,P (z.data j)) (.op (.const 0 1)) s 1 a := Block.Eval.op_const _ _ _ hs ha
  have et : Block.Eval (fun z => ∀ j,P (z.data j)) (.op (.add 4 4 0)) a 1 t := Block.Eval.op_add _ _ _ _ ha ht
  exact ⟨t,ea.seq et,by simp [t,a],rfl,fun j h0 h4 => by simp [t,a,h0,h4]⟩

def wordInsertCost (width g pos : ℕ) : ℕ := (3+(pos*(4*width+5)+5))+
  ((6*((g-pos)*width)+1)+(3+((7*width+2)+2)))

theorem wordInsertCost_le (width g pos : ℕ) (hp : pos ≤ g) : wordInsertCost width g pos ≤ 30*(g+1)*(width+1) := by
  have k := Nat.mul_le_mul_right (4*width+5) hp
  have j := Nat.mul_le_mul_right width (Nat.sub_le g pos)
  unfold wordInsertCost
  calc
    _ ≤ (3+(g*(4*width+5)+5))+((6*(g*width)+1)+(3+((7*width+2)+2))) := by omega
    _ ≤ _ := by ring_nf; omega

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
