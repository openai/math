import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! ## In-place backwards move of an overlapping scalar window

The guard compares the current source cursor with the beginning of the source window.
A separate remaining-length register is unnecessary. No scalar arithmetic is performed.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

private def moveBackWord : Block :=
  .seq (.op (.decr 8 8)) (.seq (.op (.decr 9 9))
    (.seq (.op (.load 0 8)) (.op (.store 9 0))))

/-- Address 8 is the exclusive source end; 9 is the exclusive destination end;
10 is the inclusive source start. Scalar zero is the only scratch scalar. -/
def moveRight : Block := .loop (.addrLT 10 8) moveBackWord

private structure MoveInvariant {K : Type*} (P : K → Prop) (entry : Memory K)
    (base stride len k : ℕ) (m : Memory K) : Prop where
  safe : m.AllData P
  src : m.index 8 = base+(len-k)
  dst : m.index 9 = base+stride+(len-k)
  low : m.index 10 = base
  pending : ∀ r < len-k, m.data (base+r)=entry.data (base+r)
  copied : ∀ r, len-k ≤ r → r < len → m.data (base+stride+r)=entry.data (base+r)
  scalars : ∀ i, i≠0 → (i < base+stride ∨ base+stride+len ≤ i) → m.data i=entry.data i
  indices : ∀ i, i≠8 → i≠9 → m.index i=entry.index i

/-- Move `[base,base+len)` right by `stride` even when the windows overlap. The exact
count also covers an empty window. Addresses other than the cursors survive, and all
scalars outside the destination survive except the declared scratch register. -/
theorem moveRight_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (base stride len : ℕ) (hb : 0 < base) (hs : 0 < stride)
    (h8 : s.index 8=base+len) (h9 : s.index 9=base+stride+len) (h10 : s.index 10=base)
    (hm : s.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) moveRight s (6*len+1) t ∧
      t.index 8=base ∧ t.index 9=base+stride ∧
      (∀ r < len, t.data (base+stride+r)=s.data (base+r)) ∧
      (∀ i, i≠0 → (i < base+stride ∨ base+stride+len ≤ i) → t.data i=s.data i) ∧
      ∀ i, i≠8 → i≠9 → t.index i=s.index i := by
  let Inv := MoveInvariant P s base stride len
  have start : Inv 0 s := ⟨hm,by simpa using h8,by simpa using h9,h10,
    fun _ _ => rfl,fun _ _ _ => by omega, fun _ _ _ => rfl,fun _ _ _ => rfl⟩
  have step (k : ℕ) (hk : k < len) (m : Memory K) (h : Inv k m) :
      (Cond.addrLT 10 8).test m = true ∧ ∃ t, Block.Eval (Memory.AllData P) moveBackWord m 4 t ∧ Inv (k+1) t := by
    refine ⟨by simp [Cond.test,h.low,h.src]; omega, ?_⟩
    let j := len-(k+1)
    have hj : j < len-k := by dsimp [j]; omega
    let a := m.putIndex 8 (m.index 8-1)
    let b := a.putIndex 9 (a.index 9-1)
    let c := b.putData 0 (b.data (b.index 8))
    let t := c.putData (c.index 9) (c.data 0)
    have ha : b.index 8 = base+j := by
      simp [a,b,Memory.putIndex,h.src,j]; omega
    have hz : c.index 9 = base+stride+j := by
      simp only [c,b,a,Memory.putData_index,Memory.putIndex_same,Memory.putIndex_ne _ (by decide : 9≠8) _,h.dst]
      dsimp [j]; omega
    have hc : c.AllData P := h.safe.putData 0 (h.safe _)
    have ht : t.AllData P := hc.putData _ (hc _)
    have ea : Block.Eval (Memory.AllData P) (.op (.decr 8 8)) m 1 a := Block.Eval.op_decr _ _ _ h.safe h.safe
    have eb : Block.Eval (Memory.AllData P) (.op (.decr 9 9)) a 1 b := Block.Eval.op_decr _ _ _ h.safe h.safe
    have ec : Block.Eval (Memory.AllData P) (.op (.load 0 8)) b 1 c := Block.Eval.op_load _ _ _ h.safe hc
    have ed : Block.Eval (Memory.AllData P) (.op (.store 9 0)) c 1 t := Block.Eval.op_store _ _ _ hc ht
    have val : c.data 0 = s.data (base+j) := by
      simp only [c,Memory.putData_same,ha,b,a,Memory.putIndex_data]
      exact h.pending j hj
    have same (i : ℕ) (h₀ : i≠0) (h₁ : i≠base+stride+j) : t.data i=m.data i := by
      change (c.putData (c.index 9) (c.data 0)).data i = _
      rw [Memory.putData_ne _ (hz.symm ▸ h₁) _]
      exact Memory.putData_ne _ h₀ _
    refine ⟨t,ea.seq (eb.seq (ec.seq ed)),ht,ha,hz,?_,?_,?_,?_,?_⟩
    · simpa [t,c,b,a] using h.low
    · intro r hr
      exact (same _ (by omega) (by dsimp [j]; omega)).trans (h.pending r (by dsimp [j] at hj; omega))
    · intro r hlo hhi
      by_cases eq : r=j
      · subst r; simpa [t,hz] using val
      · have horig : len-k ≤ r := by dsimp [j] at eq; omega
        exact (same _ (by omega) (by omega)).trans (h.copied r horig hhi)
    · intro i h₀ hfar
      exact (same _ h₀ (by dsimp [j]; omega)).trans (h.scalars i h₀ hfar)
    · intro i h₈ h₉
      simpa [t,c,b,a,h₈,h₉] using h.indices i h₈ h₉
  have stop (m : Memory K) (h : Inv len m) : (Cond.addrLT 10 8).test m=false ∧ m.AllData P :=
    ⟨by simp [Cond.test,h.low,h.src],h.safe⟩
  obtain ⟨t,run,h⟩ := Block.Eval.loop_invariant_exact Inv s len 4 start step stop
  refine ⟨t,?_,by simpa using h.src,by simpa using h.dst,fun r hr => h.copied r (by omega) hr,
    h.scalars,h.indices⟩
  change Block.Eval _ (.loop _ _) s (6*len+1) t
  simpa only [show 4+2=6 by decide,Nat.mul_comm len] using run

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
