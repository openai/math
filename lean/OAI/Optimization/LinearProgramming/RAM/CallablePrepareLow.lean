import OAI.Optimization.LinearProgramming.RAM.CallablePrepareBase

/-! Initialize the five even-bank working cells after the variable-length copy loop.
The last address cell serves as the only pointer scratch and receives its input last. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

private def lowScalar (j : ℕ) : Block :=
  .seq (.op (.addrConst 8 (2*j+1))) (.branch (.addrLT 8 113)
    (.seq (copyIndexPlus 8 111 (2*j)) (.op (.load (2*j) 8)))
    (.op (.const (2*j) 0)))

private def lowAddress (j : ℕ) : Block :=
  .seq (.op (.addrConst 8 (2*j+1))) (.branch (.addrLT 8 117)
    (.seq (copyIndexPlus 8 115 (2*j))
      (.seq (.op (.addrLoad (2*j) 8)) (.op (.decr (2*j) (2*j)))))
    (.op (.addrConst (2*j) 0)))

private def lowCells : ℕ → Block
  | 0 => .skip
  | n+1 => .seq (lowCells n) (.seq (lowScalar n) (lowAddress n))

def prepareLow : Block := lowCells 5

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem lowScalar_spec (m : Memory K) (sb ab B j : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hm : m.AllData P) (hzero : P 0) :
    ∃ u k, k ≤ 2*j+5 ∧ Block.Eval (Memory.AllData P) (lowScalar j) m k
      ((m.putIndex 8 u).putData (2*j) (xs[j]?.getD 0)) := by
  let s := m.putIndex 8 (2*j+1)
  have hs : s.AllData P := hm
  have e₀ := Block.Eval.op_addrConst (safe := Memory.AllData P) m 8 (2*j+1) hm hs
  have htest : (Cond.addrLT 8 113).test s = decide (j < xs.length) := by
    have hiff : 2*j+1 < 2*xs.length+1 ↔ j < xs.length := by omega
    simp only [Cond.test, s, Memory.putIndex_same, Memory.putIndex_ne _ (by decide : 113≠8),
      src.scalarLength, hiff]
  by_cases hj : j < xs.length
  · let y := m.putIndex 8 (2*(sb+j)+1)
    have hy : y.AllData P := hm
    have eq : s.putIndex 8 (s.index 111+2*j) = y := by
      have hbase : s.index 111 = 2*sb+1 :=
        (Memory.putIndex_ne _ (by decide : 111≠8) _).trans src.scalarBase
      rw [hbase, show 2*sb+1+2*j = 2*(sb+j)+1 by omega]
      simp [s,y,Memory.putIndex,Function.update_idem]
    have e₁ := copyIndexPlus_spec s 8 111 (2*j) hs
    rw [eq] at e₁
    have hx : y.data (y.index 8) = xs[j]?.getD 0 := by
      simpa [y,List.getElem?_eq_getElem hj] using src.scalarAt j hj
    have e₂ := Block.Eval.op_load (safe := Memory.AllData P) y (2*j) 8 hy
      (hy.putData _ (hy _))
    rw [hx] at e₂
    have guard : (Cond.addrLT 8 113).test s = true := by simp [htest,hj]
    exact ⟨2*(sb+j)+1, 1+(1+((1+2*j)+1)+1), by omega,
      e₀.seq (.branchTrue guard (e₁.seq e₂))⟩
  · have eq : ((0 : ℚ) : K) = xs[j]?.getD 0 := by
      simp [List.getElem?_eq_none (Nat.le_of_not_gt hj)]
    have e₁ := Block.Eval.op_const (safe := Memory.AllData P) s (2*j) 0 hs
      (hs.putData _ (by simpa using hzero))
    rw [eq] at e₁
    have guard : (Cond.addrLT 8 113).test s = false := by simp [htest,hj]
    exact ⟨2*j+1,3,by omega,e₀.seq (.branchFalse guard e₁)⟩

private theorem lowAddress_spec (m : Memory K) (sb ab B j : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hm : m.AllData P) :
    ∃ u k, k ≤ 2*j+6 ∧ Block.Eval (Memory.AllData P) (lowAddress j) m k
      ((m.putIndex 8 u).putIndex (2*j) (2*(dims[j]?.getD 0))) := by
  let s := m.putIndex 8 (2*j+1)
  have hs : s.AllData P := hm
  have e₀ := Block.Eval.op_addrConst (safe := Memory.AllData P) m 8 (2*j+1) hm hs
  have htest : (Cond.addrLT 8 117).test s = decide (j < dims.length) := by
    have hiff : 2*j+1 < 2*dims.length+1 ↔ j < dims.length := by omega
    simp only [Cond.test, s, Memory.putIndex_same, Memory.putIndex_ne _ (by decide : 117≠8),
      src.addressLength, hiff]
  by_cases hj : j < dims.length
  · let y := m.putIndex 8 (2*(ab+j)+1)
    have hy : y.AllData P := hm
    have eq : s.putIndex 8 (s.index 115+2*j) = y := by
      have hbase : s.index 115 = 2*ab+1 :=
        (Memory.putIndex_ne _ (by decide : 115≠8) _).trans src.addressBase
      rw [hbase, show 2*ab+1+2*j = 2*(ab+j)+1 by omega]
      simp [s,y,Memory.putIndex,Function.update_idem]
    have e₁ := copyIndexPlus_spec s 8 115 (2*j) hs
    rw [eq] at e₁
    have hv : y.index (y.index 8) = 2*dims[j]+1 := by
      simp [y, Memory.putIndex_ne _ (by omega : 2*(ab+j)+1 ≠ 8), src.addressAt j hj]
    have e₂ := Block.Eval.op_addrLoad (safe := Memory.AllData P) y (2*j) 8 hy hy
    rw [hv] at e₂
    let z := y.putIndex (2*j) (2*dims[j]+1)
    have hz : z.AllData P := hy
    have e₃ := Block.Eval.op_decr (safe := Memory.AllData P) z (2*j) (2*j) hz hz
    have out : z.putIndex (2*j) (z.index (2*j)-1) = y.putIndex (2*j) (2*(dims[j]?.getD 0)) := by
      simp [z,Memory.putIndex,Function.update_idem,List.getElem?_eq_getElem hj]
    rw [out] at e₃
    have guard : (Cond.addrLT 8 117).test s = true := by simp [htest,hj]
    exact ⟨2*(ab+j)+1,1+(1+((1+2*j)+(1+1))+1),by omega,
      e₀.seq (.branchTrue guard (e₁.seq (e₂.seq e₃)))⟩
  · have eq : 0 = 2*(dims[j]?.getD 0) := by
      simp [List.getElem?_eq_none (Nat.le_of_not_gt hj)]
    have e₁ := Block.Eval.op_addrConst (safe := Memory.AllData P) s (2*j) 0 hs hs
    have guard : (Cond.addrLT 8 117).test s = false := by simp [htest,hj]
    have ef : Block.Eval (Memory.AllData P) (.op (.addrConst (2*j) 0)) s 1
        (s.putIndex (2*j) (2*(dims[j]?.getD 0))) := by rw [← eq]; exact e₁
    exact ⟨2*j+1,3,by omega,e₀.seq (.branchFalse guard ef)⟩

private theorem lowCells_spec (m : Memory K) (sb ab B : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hm : m.AllData P) (hzero : P 0)
    (n : ℕ) (hn : n ≤ 5) :
    ∃ t k, k ≤ 40*n ∧ Block.Eval (Memory.AllData P) (lowCells n) m k t ∧ OddFrame m t ∧
      (∀ j, j<n → t.data (2*j)=xs[j]?.getD 0 ∧ t.index (2*j)=2*(dims[j]?.getD 0)) ∧
      (∀ j, n≤j → t.data (2*j)=m.data (2*j) ∧ (j≠4 → t.index (2*j)=m.index (2*j))) := by
  induction n with
  | zero =>
    exact ⟨m,0,by simp,.skip hm,OddFrame.refl m,fun j hj => by omega,
      fun _ _ => ⟨rfl,fun _ => rfl⟩⟩
  | succ n ih =>
    obtain ⟨s,l,hl,r₀,fs,lo,hi⟩ := ih (by omega)
    obtain ⟨u,k,hk,r₁⟩ := lowScalar_spec s sb ab B n xs dims (src.ofOdd fs) r₀.safe_end hzero
    let y := (s.putIndex 8 u).putData (2*n) (xs[n]?.getD 0)
    have fy : OddFrame m y := (fs.putIndex 4 u).putData n _
    obtain ⟨v,p,hp,r₂⟩ := lowAddress_spec y sb ab B n xs dims (src.ofOdd fy) r₁.safe_end
    let t := (y.putIndex 8 v).putIndex (2*n) (2*(dims[n]?.getD 0))
    have ft : OddFrame m t := (fy.putIndex 4 v).putIndex n _
    have sd (j : ℕ) (hne : j≠n) : t.data (2*j)=s.data (2*j) := by
      simp [t,y,Memory.putData_ne _ (by omega : 2*j ≠ 2*n)]
    have si (j : ℕ) (hne : j≠n) (hw : j≠4) : t.index (2*j)=s.index (2*j) := by
      simp [t,y,Memory.putIndex_ne _ (by omega : 2*j ≠ 2*n),
        Memory.putIndex_ne _ (by omega : 2*j ≠ 8)]
    refine ⟨t,l+(k+p),by omega,r₀.seq (r₁.seq r₂),ft,?_,?_⟩
    · intro j hj
      by_cases he : j=n
      · subst j; simp [t,y]
      · rw [sd j he, si j he (by omega)]
        exact lo j (by omega)
    · intro j hj
      have he : j≠n := by omega
      exact ⟨(sd j he).trans (hi j (by omega)).1, fun hw =>
        (si j he hw).trans ((hi j (by omega)).2 hw)⟩

theorem prepareLow_spec (m : Memory K) (sb ab B : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hm : m.AllData P) (hzero : P 0) :
    ∃ t k, k ≤ 200 ∧ Block.Eval (Memory.AllData P) prepareLow m k t ∧ OddFrame m t ∧
      (∀ j, j<5 → t.data (2*j)=xs[j]?.getD 0 ∧ t.index (2*j)=2*(dims[j]?.getD 0)) ∧
      (∀ j, 5≤j → t.data (2*j)=m.data (2*j) ∧ t.index (2*j)=m.index (2*j)) := by
  obtain ⟨t,k,hk,run,fr,lo,hi⟩ := lowCells_spec m sb ab B xs dims src hm hzero 5 (by decide)
  exact ⟨t,k,hk,run,fr,lo,fun j hj => ⟨(hi j hj).1,(hi j hj).2 (by omega)⟩⟩

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
