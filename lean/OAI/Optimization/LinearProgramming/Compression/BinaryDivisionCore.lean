import OAI.Optimization.LinearProgramming.RAM.Array
import Mathlib.Tactic

/-! Register-returning Euclidean long division on bounded integer-valued scalars. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Process one binary place, subtracting the current divisor when the residual permits it. -/
def nextRemainder (r w : ℕ) := if r < w then r else r-w
def nextQuotient (r w q : ℕ) := if r < w then 2*q else 2*q+1

theorem descend_division (a w : ℕ) (hw : 0 < w) :
    nextRemainder (a%(2*w)) w = a%w ∧
      nextQuotient (a%(2*w)) w (a/(2*w)) = a/w := by
  let r := a%(2*w)
  let q := a/(2*w)
  have hsum : r+(2*w)*q = a := Nat.mod_add_div a (2*w)
  have hr : r < 2*w := Nat.mod_lt a (by positivity)
  let r' := nextRemainder r w
  let q' := nextQuotient r w q
  have hnew : r' + w*q' = a ∧ r' < w := by
    dsimp [r',q',nextRemainder,nextQuotient]
    by_cases h : r < w
    · simp only [h, ite_true]; exact ⟨by nlinarith, True.intro⟩
    · simp only [h, ite_false]
      have he := Nat.sub_add_cancel (le_of_not_gt h)
      exact ⟨by nlinarith, by omega⟩
  have hq1 : q' ≤ a/w := (Nat.le_div_iff_mul_le hw).mpr (by nlinarith [hnew.1])
  have hq2 : a/w < q'+1 := (Nat.div_lt_iff_lt_mul hw).mpr (by nlinarith [hnew.1,hnew.2])
  have hq : q' = a/w := by omega
  refine ⟨?_, hq⟩
  have hh := Nat.mod_add_div a w
  change r' = _
  rw [← hq] at hh
  omega

/-- A long-division stage, using only exact field operations, comparison and control. -/
def divisionStage : Block := .seq (.op (.div 2 2 4)) <| .seq (.op (.add 3 3 3)) <|
  .branch (.scalarLT 0 2) .skip (.seq (.op (.sub 0 0 2)) (.op (.add 3 3 5)))

def quotientRemainderBlock : Block :=
  .seq (.op (.copy 2 1)) <| .seq (.op (.const 3 0)) <| .seq (.op (.const 4 2)) <|
  .seq (.op (.const 5 1)) <| .seq (.forRange 1 0 (.op (.add 2 2 2))) <|
  .forRange 1 0 divisionStage

def divisionFrame (base : Memory ℚ) (a b w q : ℕ) (j : ℕ) : Memory ℚ where
  data := fun
    | 0 => a | 1 => b | 2 => w | 3 => q | 4 => 2 | 5 => 1 | i+6 => base.data (i+6)
  index := Function.update base.index 1 j

private theorem mem_ext {s t : Memory ℚ} (hd : s.data=t.data) (hi : s.index=t.index) : s=t := by
  cases s; cases t; congr

theorem divisionFrame_index (m : Memory ℚ) (a b w q j : ℕ) (i : ℕ) :
    (divisionFrame m a b w q j).putIndex 1 i = divisionFrame m a b w q i := by
  exact mem_ext rfl (Function.update_idem ..)

private theorem divWrite0 (m : Memory ℚ) (a b w q j x : ℕ) :
    (divisionFrame m a b w q j).putData 0 (x : ℚ) = divisionFrame m x b w q j := by
  refine mem_ext (funext fun i => ?_) rfl
  match i with | 0 | 1 | 2 | 3 | 4 | 5 | _+6 => rfl

theorem divisionFrame_write2 (m : Memory ℚ) (a b w q j x : ℕ) :
    (divisionFrame m a b w q j).putData 2 (x : ℚ) = divisionFrame m a b x q j := by
  refine mem_ext (funext fun i => ?_) rfl
  match i with | 0 | 1 | 2 | 3 | 4 | 5 | _+6 => rfl

private theorem divWrite3 (m : Memory ℚ) (a b w q j x : ℕ) :
    (divisionFrame m a b w q j).putData 3 (x : ℚ) = divisionFrame m a b w x j := by
  refine mem_ext (funext fun i => ?_) rfl
  match i with | 0 | 1 | 2 | 3 | 4 | 5 | _+6 => rfl

theorem divisionFrame_safe {P : ℚ → Prop} {m : Memory ℚ} (hm : m.AllData P)
    {a b w q : ℕ} (ha : P a) (hb : P b) (hw : P w) (hq : P q) (h2 : P 2) (h1 : P 1) (j : ℕ) :
    (divisionFrame m a b w q j).AllData P := by
  intro i
  match i with
  | 0 => exact ha
  | 1 => exact hb
  | 2 => exact hw
  | 3 => exact hq
  | 4 => exact h2
  | 5 => exact h1
  | i+6 => exact hm (i+6)

/-- All physical transitions in one binary division stage have bounded cost and preserve
the memory predicate, including the transient doubled quotient and halved divisor. -/
theorem divisionStage_eval {P : ℚ → Prop} {m : Memory ℚ} (hm : m.AllData P)
    (r b w q j : ℕ) (hr : P r) (hb : P b) (h2w : P ((2*w : ℕ) : ℚ)) (hw : P w)
    (hq : P q) (h2q : P ((2*q : ℕ) : ℚ)) (h2q1 : P ((2*q+1 : ℕ) : ℚ)) (hrw : P ((r-w : ℕ) : ℚ))
    (h2 : P 2) (h1 : P 1) :
    ∃ cost ≤ 5, Block.Eval (Memory.AllData P) divisionStage
      (divisionFrame m r b (2*w) q j) cost (divisionFrame m (nextRemainder r w) b w (nextQuotient r w q) j) := by
  let F := divisionFrame m
  have hdiv : Block.Eval (Memory.AllData P) (.op (.div 2 2 4))
      (F r b (2*w) q j) 1 (F r b w q j) := by
    have he : (F r b (2*w) q j).data 2 / (F r b (2*w) q j).data 4 = (w : ℚ) := by
      change ((2*w : ℕ) : ℚ) / 2 = _; push_cast; ring
    have hop := Block.Eval.op_div (F r b (2*w) q j) 2 2 4 (by norm_num [F,divisionFrame])
      (divisionFrame_safe hm hr hb h2w hq h2 h1 j)
    rw [he, divisionFrame_write2] at hop
    exact hop (divisionFrame_safe hm hr hb hw hq h2 h1 j)
  have hadd : Block.Eval (Memory.AllData P) (.op (.add 3 3 3))
      (F r b w q j) 1 (F r b w (2*q) j) := by
    have he : (F r b w q j).data 3 + (F r b w q j).data 3 = ((2*q : ℕ) : ℚ) := by
      change (q : ℚ)+q = _; push_cast; ring
    have hop := Block.Eval.op_add (F r b w q j) 3 3 3 (divisionFrame_safe hm hr hb hw hq h2 h1 j)
    rw [he, divWrite3] at hop
    exact hop (divisionFrame_safe hm hr hb hw h2q h2 h1 j)
  by_cases h : r < w
  · have test : Cond.test (.scalarLT 0 2) (F r b w (2*q) j) = true := by
      exact decide_eq_true (by change (r : ℚ) < w; exact_mod_cast h)
    refine ⟨4, by decide, ?_⟩
    simp only [nextRemainder,nextQuotient,h,ite_true,divisionStage]
    exact hdiv.seq (hadd.seq (.branchTrue test (.skip (divisionFrame_safe hm hr hb hw h2q h2 h1 j))))
  · have test : Cond.test (.scalarLT 0 2) (F r b w (2*q) j) = false := by
      exact decide_eq_false (by change ¬(r : ℚ) < w; exact_mod_cast h)
    have hsub : Block.Eval (Memory.AllData P) (.op (.sub 0 0 2))
        (F r b w (2*q) j) 1 (F (r-w) b w (2*q) j) := by
      have he : (F r b w (2*q) j).data 0 - (F r b w (2*q) j).data 2 = ((r-w : ℕ) : ℚ) :=
        (Nat.cast_sub (le_of_not_gt h)).symm
      have hop := Block.Eval.op_sub (F r b w (2*q) j) 0 0 2 (divisionFrame_safe hm hr hb hw h2q h2 h1 j)
      rw [he, divWrite0] at hop
      exact hop (divisionFrame_safe hm hrw hb hw h2q h2 h1 j)
    have hone : Block.Eval (Memory.AllData P) (.op (.add 3 3 5))
        (F (r-w) b w (2*q) j) 1 (F (r-w) b w (2*q+1) j) := by
      have he : (F (r-w) b w (2*q) j).data 3 + (F (r-w) b w (2*q) j).data 5 = ((2*q+1 : ℕ) : ℚ) := by
        change ((2*q : ℕ) : ℚ)+1 = _; norm_cast
      have hop := Block.Eval.op_add (F (r-w) b w (2*q) j) 3 3 5 (divisionFrame_safe hm hrw hb hw h2q h2 h1 j)
      rw [he, divWrite3] at hop
      exact hop (divisionFrame_safe hm hrw hb hw h2q1 h2 h1 j)
    refine ⟨5, by decide, ?_⟩
    simp only [nextRemainder,nextQuotient,h,ite_false,divisionStage]
    exact hdiv.seq (hadd.seq (.branchFalse test (hsub.seq hone)))

end Compression
end LinearProgramming
end Optimization
end OAI
