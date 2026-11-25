import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan
import OAI.Optimization.LinearProgramming.Compression.ServiceGeneratorTable
import OAI.Optimization.LinearProgramming.Compression.UniformIndex

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Set read cursor 8 to the last scalar of the row at address `row`. -/
def lastAddress (row : ℕ) : Block := .seq (cellAddress 8 10 11 row 18 2 18) (.op (.decr 8 8))

theorem lastAddress_spec (P : K→Prop) (s : Memory K) (row width : ℕ) (h2 : s.index 2 = 0)
    (h18 : s.index 18 = width) (hs : ∀ a,P (s.data a)) :
    ∃t,Block.Eval (fun z => ∀ a,P (z.data a)) (lastAddress row) s (4*width+6) t ∧
      t.index 8 = s.index row+width-1 ∧ t.data = s.data ∧
      ∀ j,j ≠ 8 → j ≠ 10 → j ≠ 11 → t.index j = s.index j := by
  obtain ⟨a,ea,ad,ai,a8⟩ := cellAddress_spec (fun f => ∀ j,P (f j)) s hs 8 10 11 row 18 2 18 (by simp [CellScratchOK])
  rw [h2,h18] at ea a8
  simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add] at ea a8
  let t := a.putIndex 8 (a.index 8-1)
  have et : Block.Eval (fun z => ∀ j,P (z.data j)) (.op (.decr 8 8)) a 1 t := Block.Eval.op_decr _ _ _ ea.safe_end ea.safe_end
  exact ⟨t,ea.seq et,by simp [t,a8],ad,fun j h8 h10 h11 => by simpa [t,h8] using ai j h8 h10 h11⟩

private def starts : List AddressSet := [.read 9 5,.fix 15 0]

def startGather : Block := .seq (.op (.addrConst 2 0)) (.seq (lastAddress 14)
  (.seq (cellAddress 5 10 11 21 18 2 18) (addressPlan starts)))

theorem startGather_spec (P : K→Prop) (s : Memory K) (n g : ℕ) (h14 : s.index 14 = tableBase n)
    (h18 : s.index 18 = stride n) (h21 : s.index 21 = slotBase n (g+1)) (hs : ∀ a,P (s.data a)) :
    ∃t,Block.Eval (fun z => ∀ a,P (z.data a)) startGather s (8*stride n+14) t ∧
      t.index 2 = 0 ∧ t.index 5 = slotBase n (g+2) ∧ t.index 8 = tableBase n+stride n-1 ∧
      t.index 9 = slotBase n (g+2) ∧ t.index 15 = 0 ∧ t.data = s.data ∧
      ∀ a,a = 1 ∨ a = 14 ∨ 17 ≤ a → t.index a = s.index a := by
  let a := s.putIndex 2 0
  have ea : Block.Eval (fun z => ∀ j,P (z.data j)) (.op (.addrConst 2 0)) s 1 a := Block.Eval.op_addrConst _ _ _ hs hs
  obtain ⟨b,eb,b8,bd,bi⟩ := lastAddress_spec P a 14 (stride n) (by simp [a]) (by simpa [a] using h18) ea.safe_end
  have b2 := (bi 2 (by decide) (by decide) (by decide)).trans (show a.index 2 = 0 by simp [a])
  have b18 := (bi 18 (by decide) (by decide) (by decide)).trans (show a.index 18 = stride n by simpa [a] using h18)
  have b21 := (bi 21 (by decide) (by decide) (by decide)).trans (show a.index 21 = slotBase n (g+1) by simpa [a] using h21)
  obtain ⟨c,ec,cd,ci,c5⟩ := cellAddress_spec (fun f => ∀ j,P (f j)) b eb.safe_end 5 10 11 21 18 2 18 (by simp [CellScratchOK])
  rw [b2,b18] at ec c5
  simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add] at ec c5
  have cf : c.index 5 = slotBase n (g+2) := by rw [c5,b21];simp [slotBase,Nat.add_mul,two_mul,Nat.add_assoc]
  let t := applyPlan starts c
  have et : Block.Eval (fun z => ∀ j,P (z.data j)) (addressPlan starts) c 2 t := addressPlan_spec (fun f => ∀ j,P (f j)) _ _ ec.safe_end
  have ti (j : ℕ) (h9 : j ≠ 9) (h15 : j ≠ 15) : t.index j = c.index j := by simp [t,starts,applyPlan,AddressSet.apply,h9,h15]
  refine ⟨t,?_,(ti 2 (by decide) (by decide)).trans ((ci 2 (by decide) (by decide) (by decide)).trans b2),
    (ti 5 (by decide) (by decide)).trans cf,?_,?_,?_,(applyPlan_data _ _).trans (cd.trans bd),?_⟩
  · have addrRun : Block.Eval (fun z => ∀ j,P (z.data j))
        (cellAddress 5 10 11 21 18 2 18) b (4*stride n+5) c := ec
    have setupCost : 1+((4*stride n+6)+((4*stride n+5)+2)) = 8*stride n+14 := by omega
    rw [← setupCost]
    exact ea.seq (eb.seq (addrRun.seq et))
  · simpa [ti 8 (by decide) (by decide),ci 8 (by decide) (by decide) (by decide),a,h14] using b8
  · simp [t,starts,applyPlan,AddressSet.apply,cf]
  · simp [t,starts,applyPlan,AddressSet.apply]
  · intro j h
    have eq := (ti j (by omega) (by omega)).trans ((ci j (by omega) (by omega) (by omega)).trans (bi j (by omega) (by omega) (by omega)))
    simpa [a,show j ≠ 2 by omega] using eq

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
