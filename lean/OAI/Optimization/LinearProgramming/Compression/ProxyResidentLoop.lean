import OAI.Optimization.LinearProgramming.Compression.ProxyResidentRow

/-! Complete reverse expansion of a finite ordinary cache into its nested physical lanes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ResidentInstall

open RAM

structure PhysicalPair {K : Type*} [Zero K] (j : ℕ) (caller raw : Memory K) : Prop where
  innerData : raw.data (4*j) = 0
  innerIndex : raw.index (4*j) = 0
  outerData : raw.data (4*j+2) = caller.data j
  outerIndex : raw.index (4*j+2) = 4*sourceAddress j caller+2

/-- The loop preserves all outside odd controller addresses and the four dedicated
low metadata backups. At every higher even address it preserves the initial parity. -/
structure Expanded {K : Type*} [Zero K] (cap : ℕ) (entry caller raw : Memory K) : Prop where
  pairs : ∀ j, 16≤j → j≤cap → PhysicalPair j caller raw
  exterior : ∀ i, 2*cap+1 < i → raw.index (2*i)%2 = 0
  odd : ∀ i, 16 ≤ i → i%2=1 → raw.index i = entry.index i
  metadata : ∀ i<4, raw.index (10+i) = entry.index (10+i)

private structure Invariant {K : Type*} [Zero K] (P : K→Prop) (cap done : ℕ) (entry caller raw : Memory K) : Prop where
  safe : raw.AllData P
  cursor : Cursor (cap-done) raw
  inputData : ∀ i, 16 ≤ i → i≤cap-done → raw.data i = caller.data i
  inputIndex : ∀ i, 60 ≤ i → i≤cap-done → raw.index i = caller.index i
  filled : ∀ i, cap-done < i → i≤cap → PhysicalPair i caller raw
  exterior : ∀ i, 2*cap+1 < i → raw.index (2*i)%2 = 0
  odd : ∀ i, 16 ≤ i → i%2=1 → raw.index i = entry.index i
  metadata : ∀ i<4, raw.index (10+i) = entry.index (10+i)

theorem scatterResidentLoop_eval {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (P : K→Prop) (entry caller : Memory K) (cap R : ℕ)
    (hcap : 16≤cap) (hs : entry.AllData P) (hc : Cursor cap entry)
    (inputData : ∀ j, 16≤j → j≤cap → entry.data j = caller.data j)
    (inputIndex : ∀ j, 60≤j → j≤cap → entry.index j = caller.index j)
    (bound : ∀ j, caller.index j ≤ R)
    (exterior : ∀ i, 2*cap+1 < i → entry.index (2*i)%2 = 0) :
    ∃ t k, k ≤ (cap-15)*(12*R+27)+1 ∧
      Block.Eval (Memory.AllData P) scatterResidentLoop entry k t ∧ Expanded cap entry caller t := by
  let I := fun done r => Invariant P cap done entry caller r
  have init : I 0 entry := ⟨hs,by simpa using hc,
    fun j lo hi => inputData j lo (by omega),fun j lo hi => inputIndex j lo (by omega),
    fun _ hi hi' => False.elim (by omega),exterior,fun _ _ _ => rfl,fun _ _ => rfl⟩
  have body (i : ℕ) (hi : i<cap-15) (s : Memory K) (h : I i s) :
      (Cond.addrLT 8 0).test s = true ∧
      ∃ t k, k≤12*R+25 ∧ Block.Eval (Memory.AllData P) scatterResidentRow s k t ∧ I (i+1) t := by
    let j := cap-i
    have hj : 16≤j := by dsimp [j]; omega
    have jc : j≤cap := Nat.sub_le ..
    have eqnext : cap-(i+1) = j-1 := by dsimp [j]; omega
    have addr : sourceAddress j s = sourceAddress j caller := by
      by_cases lo : j<60
      · simp [sourceAddress,lo]
      · simp [sourceAddress,lo,h.inputIndex j (by omega) le_rfl]
    have small : sourceAddress j s ≤ R := by
      rw [addr]; unfold sourceAddress; split <;> first | omega | exact bound _
    have datum : s.data j = caller.data j := h.inputData j hj le_rfl
    obtain ⟨t,k,hk,et,row⟩ := scatterResidentRow_eval P s j hj h.safe h.cursor
    have test : (Cond.addrLT 8 0).test s = true := by
      simp only [Cond.test,h.cursor.stop,h.cursor.source,decide_eq_true_eq]
      omega
    refine ⟨test,t,k,by omega,et,?_⟩
    have nextCursor : Cursor (cap-(i+1)) t := by rw [eqnext]; exact row.cursor
    refine ⟨et.safe_end,nextCursor,?_,?_,?_,?_,?_,?_⟩
    · intro a ha hh
      have prior := h.inputData a ha (by omega)
      exact (row.scalar a (by omega) (by omega) (by omega)).trans prior
    · intro a ha hh
      have prior := h.inputIndex a ha (by omega)
      exact (row.address a (by omega) (by omega) (by omega)).trans prior
    · intro a ha hac
      by_cases eq : a=j
      · subst a
        exact ⟨row.innerData,row.innerIndex,row.outerData.trans datum,
          row.outerIndex.trans (congrArg (fun v => 4*v+2) addr)⟩
      · have ja : j<a := by omega
        have prev := h.filled a ja hac
        exact ⟨(row.scalar _ (by omega) (by omega) (by omega)).trans prev.innerData,
          (row.address _ (by omega) (by omega) (by omega)).trans prev.innerIndex,
          (row.scalar _ (by omega) (by omega) (by omega)).trans prev.outerData,
          (row.address _ (by omega) (by omega) (by omega)).trans prev.outerIndex⟩
    · intro a ha
      rw [row.address _ (by omega) (by omega) (by omega)]
      exact h.exterior a ha
    · intro a ha odd
      exact (row.address a (by omega) (by omega) (by omega)).trans (h.odd a ha odd)
    · intro a ha
      exact (row.address _ (by omega) (by omega) (by omega)).trans (h.metadata a ha)
  have stop (t : Memory K) (h : I (cap-15) t) :
      (Cond.addrLT 8 0).test t = false ∧ t.AllData P := by
    refine ⟨?_,h.safe⟩
    have cursorEnd : cap-(cap-15) = 15 := by omega
    simp [Cond.test,h.cursor.source,h.cursor.stop,cursorEnd]
  obtain ⟨t,k,hk,et,h⟩ := Block.Eval.loop_invariant I entry (cap-15) (12*R+25) init body stop
  exact ⟨t,k,hk,et,
    ⟨fun j lo hi => h.filled j (by omega) hi,h.exterior,h.odd,h.metadata⟩⟩

end ResidentInstall
end Compression
end LinearProgramming
end Optimization
end OAI
