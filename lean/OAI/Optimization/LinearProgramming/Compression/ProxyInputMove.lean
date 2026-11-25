import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan
import OAI.Optimization.LinearProgramming.RAM.StrideCopy

/-! Preserve the raw scalar input while moving it past the service header workspace. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM GeneratorTable

private def proxyInputPointers : List AddressSet :=
  [.read 12 1] ++ List.replicate 8 (.next 12 12) ++ [.fix 8 1, .next 9 12]

/-- Copy scalars `0..g` to `g+8..2g+8`. The address-only prologue protects
scalar zero before the stride copy uses it, and the last load restores it. -/
def moveProxyInputBlock : Block :=
  .seq (addressPlan proxyInputPointers) <| .seq (.op (.store 12 0)) <|
    .seq (StrideCopy.block false 8 9 10 1 0 1 1) (.op (.load 0 12))

theorem moveProxyInput_steps_le (g : ℕ) : 7*g+15 ≤ 15*(g+1) := by omega

/-- The scalar bank and the four pointer facts after the address-only prologue. -/
private theorem proxyInputPointerSetup {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (g : ℕ) (hg : s.index 1 = g) (hs : s.AllData P) :
    ∃ a, Block.Eval (Memory.AllData P) (addressPlan proxyInputPointers) s 11 a ∧
      a.data = s.data ∧ a.index 8 = 1 ∧ a.index 9 = g+9 ∧ a.index 12 = g+8 ∧
      ∀ j, j ≠ 8 → j ≠ 9 → j ≠ 12 → a.index j = s.index j := by
  refine ⟨applyPlan proxyInputPointers s, addressPlan_spec (fun f => ∀ i, P (f i)) _ _ hs,
    applyPlan_data _ _, ?_, ?_, ?_, ?_⟩
  · simp [proxyInputPointers, applyPlan, AddressSet.apply]
  · simp [proxyInputPointers, applyPlan, AddressSet.apply, hg]
  · simp [proxyInputPointers, applyPlan, AddressSet.apply, hg]
  · intro j j8 j9 j12
    simp [proxyInputPointers, applyPlan, AddressSet.apply, j8, j9, j12]

theorem moveProxyInputBlock_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (g : ℕ) (hg : s.index 1 = g) (hs : s.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) moveProxyInputBlock s (7*g+15) t ∧
      (∀ i ≤ g, t.data (g+8+i) = s.data i) ∧
      (∀ i, (i < g+8 ∨ g+8+(g+1) ≤ i) → t.data i = s.data i) ∧
      (∀ j, j ≠ 8 → j ≠ 9 → j ≠ 10 → j ≠ 12 → t.index j = s.index j) ∧
      t.index 12 = g+8 := by
  obtain ⟨a, ea, da, a8, a9, a12, af⟩ :=
    proxyInputPointerSetup P s g hg hs
  let b := a.putData (g+8) (s.data 0)
  have eb : Block.Eval (Memory.AllData P) (.op (.store 12 0)) a 1 b := by
    simpa only [b, a12, da] using
      Block.Eval.op_store a 12 0 ea.safe_end (ea.safe_end.putData _ (ea.safe_end _))
  have b8 : b.index 8 = 1 := a8
  have b9 : b.index 9 = g+9 := a9
  have b1 : b.index 1 = g := (af 1 (by decide) (by decide) (by decide)).trans hg
  obtain ⟨c, ec, copied, frame, _, _, _, addr⟩ :=
    StrideCopy.block_correct P b false 8 9 10 1 0 1 1 g eb.safe_end b1
      (by decide) (by decide) (by simp)
      (by intro j _; simp [b8])
      (by intro j _; simp [b9])
      (by intro i j hij hj; simp [b8,b9]; omega)
  have cp (j : ℕ) (hj : j < g) : c.data (g+9+j) = b.data (1+j) := by
    simpa [b8,b9] using copied j hj
  have fr (i : ℕ) (hi : i ≠ 0) (outside : i < g+9 ∨ g+9+g ≤ i) : c.data i = b.data i := by
    exact frame i hi (by intro j hj; simp [b9]; omega)
  have c12 : c.index 12 = g+8 := (addr 12 (by decide) (by decide) (by decide)).trans a12
  have saved : c.data (g+8) = s.data 0 :=
    (fr _ (by omega) (Or.inl (by omega))).trans (Memory.putData_same _ _ _)
  let t := c.putData 0 (s.data 0)
  have et : Block.Eval (Memory.AllData P) (.op (.load 0 12)) c 1 t := by
    simpa only [t, c12, saved] using
      Block.Eval.op_load c 0 12 ec.safe_end (ec.safe_end.putData _ (ec.safe_end _))
  refine ⟨t, ?_, ?_, ?_, ?_, c12⟩
  · rw [show 7*g+15 = 11+(1+(g*(1+1+5)+2+1)) by omega]
    exact ea.seq (eb.seq (ec.seq et))
  · intro i hi
    cases i with
    | zero => simpa [t] using saved
    | succ j =>
      have hj : j < g := by omega
      rw [show g+8+(j+1) = g+9+j by omega]
      exact (Memory.putData_ne c (by omega : g+9+j ≠ 0) _).trans ((cp j hj).trans
        ((Memory.putData_ne a (by omega : 1+j ≠ g+8) _).trans (by rw [da, Nat.add_comm 1 j])))
  · intro i outside
    by_cases hi : i = 0
    · subst i; simp [t]
    · exact (Memory.putData_ne c hi _).trans ((fr i hi (by omega)).trans
        ((Memory.putData_ne a (by omega : i ≠ g+8) _).trans (congrFun da i)))
  · intro j j8 j9 j10 j12
    exact (addr j j8 j9 j10).trans (af j j8 j9 j12)

end Compression
end LinearProgramming
end Optimization
end OAI
