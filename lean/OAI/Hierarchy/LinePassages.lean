import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI
/-! # Touched and untouched passages along one rail line -/

namespace Hierarchy.FactorAllocation

/-- A line consists of g cells with q ticks apiece. Under the per-tick mean
and error bounds of the diagonal schedule, at least B pairs pass any one
cell untouched, and the entire line uses at most 3B pairs. -/
theorem line_passages {ι : Type*} {g q : ℕ} (line cell : Finset ι) (load : ι → ℝ)
    (hg : 4≤g) (_hq : 0<q) (incl : cell⊆line)
    (lineCount : line.card=g*q) (cellCount : cell.card=q)
    (B mean error : ℝ) (nonneg : 0≤B) (balance : mean*(g*q:ℕ)=2*B)
    (small : error*(g*q:ℕ)≤B/16)
    (lo : ∀ i∈line,mean/(21/20)-error ≤ load i)
    (hi : ∀ i∈line,load i ≤ (21/20)*mean+(21/20)*error) :
    B≤∑ i∈line, load i ∧ (∑ i∈line, load i)≤3*B ∧
      B≤(∑ i∈line, load i)-(∑ i∈cell, load i) := by
  have low := Finset.sum_le_sum lo
  have high := Finset.sum_le_sum hi
  have touched := Finset.sum_le_sum (s:=cell) (fun i hi'=>hi i (incl hi'))
  simp only [Finset.sum_const,nsmul_eq_mul,lineCount,cellCount] at low high touched
  have realG : (4:ℝ) ≤ g := by exact_mod_cast hg
  push_cast at balance small low high
  have bottom : 7*B/4 ≤ ∑ i∈line, load i := by linarith only [low,balance,small,nonneg]
  have top : (g:ℝ)*((q:ℝ)*((21/20)*mean+(21/20)*error))≤9*B/4 := by
    linarith only [balance,small,nonneg]
  have gq := mul_le_mul_of_nonneg_left touched (show 0≤(g:ℝ) by positivity)
  have cut : (∑ i∈cell, load i) ≤ 3*B/4 := by
    by_contra! bad
    have pos : 0 ≤ ∑ i∈cell, load i := by linarith
    have scaled := mul_le_mul_of_nonneg_right realG pos
    linarith only [scaled,gq,top,bad,nonneg]
  exact ⟨by linarith,by linarith only [high,balance,small,nonneg],by linarith only [bottom,cut]⟩

end Hierarchy.FactorAllocation

end OAI
