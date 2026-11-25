import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan
import OAI.Optimization.LinearProgramming.Compression.ServiceStageArray

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

def smallStore (reg : ℕ) : Block := .seq (natCastBlock 0 6 30 reg)
  (.seq (.op (.store 26 0)) (.op (.incr 26 26)))

theorem smallStore_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K→Prop) (m : Memory K) (reg val dst : ℕ)
    (hr : reg ≠ 30) (hreg : m.index reg = val) (h26 : m.index 26 = dst) (hs : ∀ a,P (m.data a))
    (hone : P 1) (hv : ∀ j ≤ val,P (j:K)) :
    ∃t,Block.Eval (fun z => ∀ a,P (z.data a)) (smallStore reg) m (4*val+6) t ∧
      t.data dst = (val:K) ∧ t.index 26 = dst+1 ∧
      (∀a,a ≠ 0 → a ≠ 6 → a ≠ dst → t.data a = m.data a) ∧
      ∀a,a ≠ 26 → a ≠ 30 → t.index a = m.index a := by
  obtain ⟨a,ea,a0,_,_,ai,ad⟩ := natCastBlock_correct P m 0 6 30 reg val (by decide) (Ne.symm hr)
    hreg hs hone hv
  have a26 := (ai 26 (by decide)).trans h26
  let b := a.putData (a.index 26) (a.data 0)
  let t := b.putIndex 26 (b.index 26+1)
  have sb : ∀j,P (b.data j) := by
    intro j
    by_cases h : j = a.index 26
    · simpa [b,h] using ea.safe_end 0
    · simpa [b,h] using ea.safe_end j
  have eb : Block.Eval (fun z => ∀a,P (z.data a)) (.op (.store 26 0)) a 1 b := Block.Eval.op_store _ _ _ ea.safe_end sb
  have et : Block.Eval (fun z => ∀a,P (z.data a)) (.op (.incr 26 26)) b 1 t := Block.Eval.op_incr _ _ _ sb sb
  refine ⟨t,?_,by simp [t,b,a26,a0],by simp [t,b,a26],?_,?_⟩
  · rw [show 4*val+6 = (4*val+4)+(1+1) by omega]
    exact ea.seq (eb.seq et)
  · intro j h0 h6 hdst
    simpa [t,b,a26,hdst] using ad j h0 h6
  · intro j h26' h30
    simpa [t,b,h26'] using ai j h30

def stagePointers : List AddressSet := [.read 26 21,.next 27 40,.next 27 27]

/-- Write one complete candidate slot beyond the current table. Register 5 carries its
positive magnitude. The protected request prefix supplies the order and coordinate arrays. -/
def stageSlot : Block := .seq (addressPlan stagePointers) (.seq (smallStore 43)
  (.seq (smallStore 42) (.seq stageArray (.seq stageArray (.op (.store 26 5))))))


end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
