import OAI.Computability.BorderVNP.CubeISASingleTallyImage

/-! # Computing a complete ordered singleton row on the native team machine

The public row trial loop hands only accepted ordered pairs to the scalar
interval scanner. Its loop invariant gives the exact accumulated memory
image after every numeric trial, including empty intervals and skipped pairs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SingleTally

open Cube Cube.Physical Cube.Physical.Owned VPVNP.BurstRAM Finset

/-- Complete native cut tally for one orientation of a singleton symbol pair. -/
def row (n : ℕ) : Code := Owned.rowLoop (Owned.singleCandidate n) family

/-- The candidate overhead is paid once per compressed label pair, while the
bit loop is entered only for singleton pairs at the specified orientation. -/
def rowCost {n d : ℕ} (i : Fin (n+1)) (a b : Fin d) (bits : ℕ) : ℕ :=
  (∑ t : Fin (singlePairTrials n d), (6*n+20 +
    if singleTrialValid i a b t then 5+bits*(13*(n+1)+7) else 1)) + 1

/-- All memory words after the actual native ordered row pass, starting
from any row subtotals. Only the numeric bound on final sums is needed. -/
theorem row_run {n d w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (i : Fin (n+1)) (a b : Fin d) (base bits : ℕ)
    (start : Owned.singleReady i a b 0 (.ofWords r m))
    (r5 : (r 5).val = n) (r9 : (r 9).val = base) (r21 : (r 21).val = bits)
    (fit : singlePairTrials n d < 2^w) (labelFit : d^(n+1) ≤ 2^w) (dim : n+1 < 2^w)
    (room : base+(n+1) ≤ 2^w) (cap : ∀ j < n+1,
      prefixImage i a b base bits (readings m) (singlePairTrials n d) (base+j) < 2^w) :
    TestRun pub macros (row n) r m (rowCost i a b bits) True fun z =>
      z.mem = prefixImage i a b base bits (readings m) (singlePairTrials n d) ∧
      ∀ j : Reg, j.val < 24 → j ≠ 18 → j ≠ 20 → z.reg j = (r j).val := by
  let img := prefixImage i a b base bits (readings m)
  let I (k : ℕ) (z : NatState) : Prop := z.reg 18 = k ∧ z.mem = img k ∧
    ∀ j : Reg, j.val < 24 → j ≠ 18 → j ≠ 20 → z.reg j = (r j).val
  have stable : Owned.stableLow I := by
    intro k z y hz lo mem
    exact ⟨(lo 18 (by decide)).trans hz.1, mem.trans hz.2.1,
      fun j hj h18 h20 => (lo j hj).trans (hz.2.2 j hj h18 h20)⟩
  obtain ⟨sr0,sr1,sr10,sr11,sr12,sr14,sr15,sr18,sr19⟩ := start
  have regs (k : ℕ) (z : NatState) (hz : I k z) : Owned.singleReady i a b k z :=
    ⟨(hz.2.2 0 (by decide) (by decide) (by decide)).trans sr0,
     (hz.2.2 1 (by decide) (by decide) (by decide)).trans sr1,
     (hz.2.2 10 (by decide) (by decide) (by decide)).trans sr10,
     (hz.2.2 11 (by decide) (by decide) (by decide)).trans sr11,
     (hz.2.2 12 (by decide) (by decide) (by decide)).trans sr12,
     (hz.2.2 14 (by decide) (by decide) (by decide)).trans sr14,
     (hz.2.2 15 (by decide) (by decide) (by decide)).trans sr15,
     hz.1,(hz.2.2 19 (by decide) (by decide) (by decide)).trans sr19⟩
  have next (t : Fin (singlePairTrials n d)) (z : NatState) (cursor : z.reg 18 = t.val)
      (mem : z.mem = img (t.val+1))
      (low : ∀ j : Reg, j.val < 24 → j ≠ 18 → j ≠ 20 → z.reg j = (r j).val) :
      I (t.val+1) (Owned.increment 18 z) :=
    ⟨by simp [Owned.increment,cursor], mem,
      fun j hj h18 h20 => (Function.update_of_ne h18 ..).trans (low j hj h18 h20)⟩
  have visit (t : Fin (singlePairTrials n d)) (hv : singleTrialValid i a b t) (u : Bank w) (mm : Memory w)
      (ht : I t.val (.ofWords u mm)) (ha : Owned.singleAt i a b t (.ofWords u mm)) :
      TestRun pub macros family u mm (5+bits*(13*(n+1)+7)) True (Owned.nextAt I 18 t.val) := by
    have eqn := prefix_visit i a b base bits (readings m) t hv
    have hmem : readings mm = img t.val := ht.2.1
    let x := (labels i a b t).1
    let y := (labels i a b t).2
    have good (j : ℕ) (hj : j < n+1) : readings mm (base+j) + bits*Cube.RowAccum.unequalDigit d x y j < 2^w := by
      have hm := (prefix_le i a b base bits (readings m) t.isLt (base+j)).trans_lt (cap j hj)
      rw [eqn] at hm
      simpa only [hmem, img, familyImage,Nat.le_add_right,Nat.add_lt_add_iff_left,hj,and_self,ite_true,
        Nat.add_sub_cancel_left] using hm
    have h := family_run pub macros u mm base n d x y bits
      ((ht.2.2 0 (by decide) (by decide) (by decide)).trans sr0)
      ((ht.2.2 1 (by decide) (by decide) (by decide)).trans sr1)
      ((ht.2.2 9 (by decide) (by decide) (by decide)).trans r9)
      ((ht.2.2 5 (by decide) (by decide) (by decide)).trans r5)
      ((ht.2.2 10 (by decide) (by decide) (by decide)).trans sr10) ha.1 ha.2
      ((ht.2.2 21 (by decide) (by decide) (by decide)).trans r21) (Nat.zero_lt_of_lt a.isLt) dim room good
    exact h.mono le_rfl Iff.rfl fun z hz => by
      have h18 := (hz.2 18 (by decide) (by decide)).trans ht.1
      refine ⟨(hz.2 1 (by decide) (by decide)).trans ((ht.2.2 1 (by decide) (by decide) (by decide)).trans sr1),
        h18, next t z h18 ?_ fun j hj h18 h20 => (hz.2 j hj h20).trans (ht.2.2 j hj h18 h20)⟩
      rw [hz.1,hmem]
      exact eqn.symm
  have skip (t : Fin (singlePairTrials n d)) (hv : ¬singleTrialValid i a b t) (z : NatState) (hz : I t.val z) :=
    next t z hz.1 (hz.2.1.trans (prefix_skip i a b base bits (readings m) t hv).symm) hz.2.2
  have zero : I 0 (.ofWords r m) := ⟨sr18,by ext k; simp [img,prefixImage,NatState.ofWords],
    fun _ _ _ _ => rfl⟩
  exact (Owned.singleRow_run pub macros i a b family (fun _ => 5+bits*(13*(n+1)+7))
    (fun _ => True) I stable regs fit labelFit visit skip r m zero).mono le_rfl (by simp) fun _ h => h.2

end RoutingISA.SingleTally

end BorderVNP
end Computability
end OAI
