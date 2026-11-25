import OAI.Optimization.LinearProgramming.Compression.ServiceGatherLoop
import OAI.Optimization.LinearProgramming.Compression.ServiceGatherPointers
import OAI.Optimization.LinearProgramming.Compression.ServiceMagnitudeView

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

private def finishGather : Block := .seq (lastAddress 21) (.seq (.op (.load 6 8))
  (.seq (.op (.store 9 6)) (.op (.incr 7 9))))

private theorem finishGather_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K→Prop) (s : Memory K) (width : ℕ) (h2 : s.index 2 = 0)
    (h18 : s.index 18 = width) (hs : ∀ a,P (s.data a)) :
    ∃t,Block.Eval (fun z => ∀ a,P (z.data a)) finishGather s (4*width+9) t ∧
      t.data (s.index 9) = s.data (s.index 21+width-1) ∧ t.index 7 = s.index 9+1 ∧
      (∀ j,j ≠ 6 → j ≠ s.index 9 → t.data j = s.data j) ∧
      ∀ j,j ≠ 7 → j ≠ 8 → j ≠ 10 → j ≠ 11 → t.index j = s.index j := by
  obtain ⟨a,ea,a8,ad,ai⟩ := lastAddress_spec P s 21 width h2 h18 hs
  let b := a.putData 6 (a.data (a.index 8))
  let c := b.putData (b.index 9) (b.data 6)
  let t := c.putIndex 7 (c.index 9+1)
  have put {u : Memory K} (h : ∀ i,P (u.data i)) {j : ℕ} {v : K} (good : P v) : ∀ i,P ((u.putData j v).data i) := by
    intro i;by_cases hi : i = j
    · simpa [hi] using good
    · simpa [hi] using h i
  have hb : ∀ i,P (b.data i) := put ea.safe_end (ea.safe_end _)
  have hc : ∀ i,P (c.data i) := put hb (hb 6)
  have eb : Block.Eval (fun z => ∀ i,P (z.data i)) (.op (.load 6 8)) a 1 b := Block.Eval.op_load _ _ _ ea.safe_end hb
  have ec : Block.Eval (fun z => ∀ i,P (z.data i)) (.op (.store 9 6)) b 1 c := Block.Eval.op_store _ _ _ hb hc
  have et : Block.Eval (fun z => ∀ i,P (z.data i)) (.op (.incr 7 9)) c 1 t := Block.Eval.op_incr _ _ _ hc hc
  have a9 := ai 9 (by decide) (by decide) (by decide)
  refine ⟨t,?_,by simp [t,c,b,a9,a8,ad],by simp [t,c,b,a9],?_,?_⟩
  · have finishCost : (4*width+6)+(1+(1+1)) = 4*width+9 := by omega
    rw [← finishCost]
    exact ea.seq (eb.seq (ec.seq et))
  · intro j h6 h9; simp [t,c,b,a9,h6,h9,ad]
  · intro j h7 h8 h10 h11; simpa [t,c,b,h7] using ai j h8 h10 h11

/-- Gather the positive magnitudes for all existing generators and the candidate directly
from their variable-stride scalar records. -/
def gatherMagnitudes : Block := .seq startGather (.seq gatherLoop finishGather)

def gatherCost (n g : ℕ) := 8*stride n+14+((g*(4*stride n+11)+1)+(4*stride n+9))

theorem gatherCost_le (n g : ℕ) : gatherCost n g ≤ 100*(n+1)*(g+1) := by unfold gatherCost stride;ring_nf;omega

set_option maxHeartbeats 1200000 in
/-- Execute the register program once for an arbitrary scalar table. The first
`g` output coordinates come from the existing rows and the last from the
candidate, one row past the temporary insertion slot. -/
theorem gatherMagnitudes_raw {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (n g : ℕ)
    (h14 : s.index 14 = tableBase n) (h17 : s.index 17 = g) (h18 : s.index 18 = stride n)
    (h21 : s.index 21 = slotBase n (g+1)) (hs : ∀ j, P (s.data j)) :
    ∃ t, Block.Eval (fun z => ∀ j, P (z.data j)) gatherMagnitudes s (gatherCost n g) t ∧
      t.index 5 = slotBase n (g+2) ∧ t.index 7 = slotBase n (g+2)+g+1 ∧
      (∀ i : Fin (g+1), t.data (t.index 5+i.val) =
        s.data (slotBase n (if i.val < g then i.val else g+1)+stride n-1)) ∧
      (∀ j, j = 1 ∨ j = 14 ∨ 17 ≤ j → t.index j = s.index j) ∧
      ∀ j, j ≠ 6 → (j < slotBase n (g+2) ∨ slotBase n (g+2)+g+1 ≤ j) →
        t.data j = s.data j := by
  let F := slotBase n (g+2)
  let R := tableBase n+stride n-1
  have first : 7 ≤ R := by dsimp [R,tableBase,stride];omega
  have free : 7 ≤ F := by dsimp [F,slotBase,tableBase];omega
  have offset (i : ℕ) : R+i*stride n = slotBase n i+stride n-1 := by
    unfold R slotBase
    have pos : 0 < stride n := by unfold stride;omega
    omega
  have sep (i : ℕ) (hi : i < g) : R+i*stride n < F := by
    rw [offset]
    have len := Nat.mul_le_mul_right (stride n) (show i+1 ≤ g+2 by omega)
    rw [Nat.add_mul,one_mul] at len
    dsimp [F,slotBase,tableBase] at *;omega
  have pre : slotBase n (g+1)+stride n-1 < F := by
    have eq : F = slotBase n (g+1)+stride n := by simp [F,slotBase,Nat.add_mul,two_mul,Nat.add_assoc]
    omega
  obtain ⟨a,ea,a2,a5,a8,a9,a15,ad,ai⟩ := startGather_spec P s n g h14 h18 h21 hs
  have a17 := (ai 17 (Or.inr (Or.inr (by decide)))).trans h17
  have a18 := (ai 18 (Or.inr (Or.inr (by decide)))).trans h18
  obtain ⟨b,eb,b9,bc,bd,bi⟩ := gatherLoop_spec P a g R F (stride n) first free sep a2 a8 a9 a15 a17 a18 ea.safe_end
  have b2 := (bi 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a2
  have b18 := (bi 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a18
  have b21 := (bi 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ai 21 (Or.inr (Or.inr (by decide)))).trans h21)
  obtain ⟨t,et,got,t7,td,ti⟩ := finishGather_spec P b (stride n) b2 b18 eb.safe_end
  have t5 := (ti 5 (by decide) (by decide) (by decide) (by decide)).trans ((bi 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a5)
  have old : 7 ≤ slotBase n (g+1)+stride n-1 := by unfold slotBase tableBase stride;omega
  refine ⟨t,ea.seq (eb.seq et),t5,by simpa [b9] using t7,?_,?_,?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last =>
      have eq := (bd _ (by omega) (Or.inl pre)).trans (congrFun ad _)
      rw [b9,b21,eq] at got
      simpa only [t5, Fin.val_last, lt_irrefl, ite_false] using got
    | cast i =>
      have hi := i.isLt
      have x := (td (F+i.val) (by omega) (by rw [b9];omega)).trans
        ((bc i.val hi).trans (congrFun ad _))
      rw [offset] at x
      simpa only [t5, Fin.val_castSucc, hi, ite_true] using x
  · intro j h
    exact (ti j (by omega) (by omega) (by omega) (by omega)).trans
      ((bi j (by omega) (by omega) (by omega) (by omega) (by omega)).trans (ai j h))
  · intro j h6 hout
    change j < F ∨ F+g+1 ≤ j at hout
    exact (td j h6 (by rw [b9];omega)).trans ((bd j h6 (by omega)).trans (congrFun ad _))


theorem gatherMagnitudes_spec {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (J : Finset (NonzeroPairMinor D E)) (q : NonzeroPairMinor D E) (P : ℚ→Prop) (s : Memory ℚ)
    (st : Stored D E J.sort s) (cand : SlotAt D E q (slotBase n (J.card+1)) s)
    (h14 : s.index 14 = tableBase n) (h17 : s.index 17 = J.card) (h18 : s.index 18 = stride n)
    (h21 : s.index 21 = slotBase n (J.card+1)) (hs : ∀ j,P (s.data j)) :
    ∃t,Block.Eval (fun z => ∀ j,P (z.data j)) gatherMagnitudes s (gatherCost n J.card) t ∧
      MagnitudeTape D E J q t ∧ (∀ j,j = 1 ∨ j = 14 ∨ 17 ≤ j → t.index j = s.index j) ∧
      ∀ j,j ≠ 6 → (j < slotBase n (J.card+2) ∨ slotBase n (J.card+2)+J.card+1 ≤ j) → t.data j = s.data j := by
  obtain ⟨t, run, base, free, values, indices, data⟩ :=
    gatherMagnitudes_raw P s n J.card h14 h17 h18 h21 hs
  exact ⟨t, run, ⟨base, free, fun i => (values i).trans (requestMagnitude q st cand i)⟩, indices, data⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
