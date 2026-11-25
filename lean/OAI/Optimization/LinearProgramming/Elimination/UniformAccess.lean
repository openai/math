import OAI.Optimization.LinearProgramming.Compression.UniformIndex

/-! Uniform row-major loads and stores. The register indices in these instruction lists are
fixed at compile time; dimensions, indices and base addresses are read from the address bank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression

/-- Address temporaries are confined to three fixed registers. -/
def accessFrame {K : Type*} (m t : Memory K) : Prop :=
  ∀ r, r ≠ 8 → r ≠ 9 → r ≠ 10 → t.index r = m.index r

theorem accessFrame_trans {K : Type*} {m s t : Memory K}
    (h : accessFrame m s) (g : accessFrame s t) : accessFrame m t :=
  fun r h8 h9 h10 => (g r h8 h9 h10).trans (h r h8 h9 h10)

/-- Read the row-major entry `base + row * dimension + column` into a scalar register. -/
def indexedLoad (dst base row col : ℕ) : Block :=
  .seq (cellAddress 8 9 10 base 0 row col) (.op (.load dst 8))

/-- Write a scalar register to a row-major entry. -/
def indexedStore (src base row col : ℕ) : Block :=
  .seq (cellAddress 8 9 10 base 0 row col) (.op (.store 8 src))

private theorem access_safe_write {K : Type*} {P : K → Prop} {m : Memory K}
    (h : ∀ j, P (m.data j)) (r : ℕ) (v : K) (hv : P v) : ∀ j, P ((m.putData r v).data j) := by
  intro j; by_cases hr : j=r <;> simp [Memory.putData, hr, h, hv]

theorem indexedLoad_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (dst base row col : ℕ) (hm : ∀ r, P (m.data r))
    (hs : CellScratchOK 8 9 10 0 row col) :
    let idx := m.index base + m.index row * m.index 0 + m.index col
    ∃ t, Block.Eval (fun w => ∀ i, P (w.data i)) (indexedLoad dst base row col) m
      (m.index row * (4*m.index 0+5)+4*m.index col+6) t ∧
      t.data = Function.update m.data dst (m.data idx) ∧ accessFrame m t := by
  obtain ⟨u,he,hd,hf,ha⟩ := cellAddress_spec (fun f => ∀ i, P (f i)) m hm 8 9 10 base 0 row col hs
  let t := u.putData dst (u.data (u.index 8))
  have hload : Block.Eval (fun w => ∀ i, P (w.data i)) (.op (.load dst 8)) u 1 t :=
    Block.Eval.op_load _ _ _ he.safe_end (access_safe_write he.safe_end _ _ (he.safe_end _))
  exact ⟨t,by simpa [indexedLoad,Nat.add_assoc] using he.seq hload,
    by simp [t,Memory.putData,hd,ha],hf⟩

theorem indexedStore_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (src base row col : ℕ) (hm : ∀ r, P (m.data r))
    (hs : CellScratchOK 8 9 10 0 row col) :
    let idx := m.index base + m.index row * m.index 0 + m.index col
    ∃ t, Block.Eval (fun w => ∀ i, P (w.data i)) (indexedStore src base row col) m
      (m.index row * (4*m.index 0+5)+4*m.index col+6) t ∧
      t.data = Function.update m.data idx (m.data src) ∧ accessFrame m t := by
  obtain ⟨u,he,hd,hf,ha⟩ := cellAddress_spec (fun f => ∀ i, P (f i)) m hm 8 9 10 base 0 row col hs
  let t := u.putData (u.index 8) (u.data src)
  have hstore : Block.Eval (fun w => ∀ i, P (w.data i)) (.op (.store 8 src)) u 1 t :=
    Block.Eval.op_store _ _ _ he.safe_end (access_safe_write he.safe_end _ _ (he.safe_end _))
  exact ⟨t,by simpa [indexedStore,Nat.add_assoc] using he.seq hstore,
    by simp [t,Memory.putData,hd,ha],hf⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
