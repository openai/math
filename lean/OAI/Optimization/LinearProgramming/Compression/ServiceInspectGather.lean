import OAI.Optimization.LinearProgramming.Compression.ServiceInspectNative
import OAI.Optimization.LinearProgramming.Compression.ServiceInspectProgram

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM OracleSpec

private theorem Inspected.afterGather {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    {J : Finset (NonzeroPairMinor D E)} {H : ℕ} {q : NonzeroPairMinor D E} {s t : Memory ℚ}
    (h : Inspected D E J q H s) (idx : ∀ j,j = 1 ∨ j = 14 ∨ 17 ≤ j → t.index j = s.index j)
    (fr : ∀ j,j ≠ 6 → (j < slotBase n (J.card+2) ∨ slotBase n (J.card+2)+J.card+1 ≤ j) → t.data j = s.data j)
    (bits : ∀ j,ratBits (t.data j) ≤ H) : Inspected D E J q H t := by
  let F := slotBase n (J.card+2)
  have low : tableBase n ≤ F := Nat.le_add_right ..
  have seven : 7 ≤ F := by dsimp [F,slotBase,tableBase];omega
  have small (i : ℕ) (hi : i < 5) := fr i (by omega) (Or.inl (by omega))
  have full {y : NonzeroPairMinor D E} {r : ℕ} (hr : r ≤ J.card+1) (hs : SlotAt D E y (slotBase n r) s) : SlotAt D E y (slotBase n r) t := by
    apply hs.transfer
    intro j hj
    have mul := Nat.mul_le_mul_right (GeneratorTable.stride n) (show r+1 ≤ J.card+2 by omega)
    rw [Nat.add_mul,one_mul] at mul
    exact fr _ (by unfold slotBase tableBase;omega) (Or.inl (by unfold slotBase;omega))
  have table : Stored D E J.sort t := ⟨h.persistent.generators.sorted,(small 4 (by decide)).trans h.persistent.generators.count,
    fun i => full (by
      have hi : i.val < J.card := by simpa using i.isLt
      exact (Nat.le_of_lt hi).trans (Nat.le_succ _)) (h.persistent.generators.slots i)⟩
  have pt : Persistent D E J H t := ⟨(small 1 (by decide)).trans h.persistent.leftRows,
    (small 2 (by decide)).trans h.persistent.rightRows,(small 3 (by decide)).trans h.persistent.columns,
    fun j hj => (fr _ (by omega) (Or.inl (by change 7+j < F;have := low;unfold tableBase at this;omega))).trans
      (h.persistent.entries j hj),table,bits⟩
  exact ⟨pt,full le_rfl h.candidate,(idx 19 (by omega)).trans h.rank,(idx 1 (by simp)).trans h.found,
    (idx 14 (by simp)).trans h.base,(idx 17 (by omega)).trans h.count,(idx 18 (by omega)).trans h.stride,
    (idx 20 (by omega)).trans h.stop,(idx 21 (by omega)).trans h.next,(idx 22 (by omega)).trans h.dimension⟩

/-- A single fixed structured RAM computation produces the exact compact positive vector,
while leaving the complete public state and all generator-lookup continuation registers live. -/
theorem inspectAndGather_native {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (J : Finset (NonzeroPairMinor D E)) (H : ℕ) (s : State ℚ) (u : MinorLog.Index D E)
    (hdim : d+e = n) (persist : Persistent D E J H s.memory) (hg : J.card ≤ (n+1)^6)
    (height : 50*(totalBits (MinorLog.entries D++MinorLog.entries E)+1)^6 ≤ H) :
    ∃t l,l ≤ 6200*(n+1)^13 ∧ Block.Eval (Memory.AllData (fun r => ratBits r ≤ H)) inspectAndGather
      (MinorLog.resume s (MinorLog.words u.val)).memory l t ∧
      Inspected D E J (MinorLog.indexEquiv D E u) H t ∧ MagnitudeTape D E J (MinorLog.indexEquiv D E u) t := by
  obtain ⟨m,k,hk,ex,loc⟩ := inspect_native D E J H s u hdim persist hg height
  obtain ⟨t,et,tape,idx,fr⟩ := gatherMagnitudes_spec D E J (MinorLog.indexEquiv D E u) (fun r => ratBits r ≤ H) m
    loc.persistent.generators loc.candidate loc.base loc.count loc.stride loc.next ex.safe_end
  have gatherSafe : (fun m : Memory ℚ => ∀ i, ratBits (m.data i) ≤ H) =
      Memory.AllData (fun r : ℚ => ratBits r ≤ H) := by
    funext m
    rfl
  rw [gatherSafe] at et
  have htime := gatherCost_le n J.card
  have gc := Nat.mul_le_mul_left (100*(n+1)) (Nat.succ_le_succ hg)
  have hbound : 100*(n+1)*((n+1)^6+1) ≤ 200*(n+1)^13 := by ring_nf;omega
  have gatherBound : gatherCost n J.card ≤ 200*(n+1)^13 := htime.trans (gc.trans hbound)
  exact ⟨t,k+gatherCost n J.card,by omega,ex.seq et,loc.afterGather idx fr et.safe_end,tape⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
