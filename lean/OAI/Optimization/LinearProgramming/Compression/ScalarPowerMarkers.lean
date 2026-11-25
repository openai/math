import OAI.Optimization.LinearProgramming.Compression.PowerTapeEncoder
import OAI.Optimization.LinearProgramming.RAM.Array

/-! Sign normalization and literal marker emission for canonical exponent tapes. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open RAM

/-- Replace a signed integer scalar by its absolute value and keep the correct
closing token, including the nonnegative closing token for zero. -/
def prepareExponentSignBlock : Block :=
  .seq (.op (.const 41 0)) (.branch (.scalarLT 0 41)
    (.straight [.sub 0 41 0, .addrConst 37 4]) (.op (.addrConst 37 3)))

theorem prepareExponentSignBlock_spec (m : Memory ℚ) (x : ℤ) {P : ℚ → Prop}
    (hm : m.AllData P) (hx : m.data 0=(x:ℚ)) (hz : P 0) (habs : P (x.natAbs:ℚ)) :
    ∃ s k, k ≤ 5 ∧ Block.Eval (Memory.AllData P) prepareExponentSignBlock m k s ∧
      s.data 0=(x.natAbs:ℚ) ∧ s.index 37=(PowerToken.finish (decide (x<0))).code ∧
      (∀ i, i ≠ 0 → i ≠ 41 → s.data i=m.data i) ∧
      (∀ i, i ≠ 37 → s.index i=m.index i) := by
  let u := m.putData 41 0
  have hu : u.AllData P := hm.putData _ hz
  have init := Block.Eval.op_const m 41 0 hm hu
  by_cases h : x<0
  · have hq : (x:ℚ)<0 := by exact_mod_cast h
    have ha : (x.natAbs:ℚ) = -(x:ℚ) := by
      simpa only [Int.cast_natCast,Int.cast_neg] using
        congrArg (fun z : ℤ => (z:ℚ)) (Int.ofNat_natAbs_of_nonpos h.le)
    have hval : u.data 41-u.data 0=(x.natAbs:ℚ) := by simp [u,hx,ha]
    let t := u.putData 0 (u.data 41-u.data 0)
    let s := t.putIndex 37 4
    have ht : t.AllData P := hu.putData _ (hval ▸ habs)
    have hs : s.AllData P := ht
    have hc : (Cond.scalarLT 0 41).test u=true := by simp [Cond.test,u,hx,hq]
    have body := (Block.Eval.op_sub u 0 41 0 hu ht).seq ((Block.Eval.op_addrConst t 37 4 ht hs).seq (.skip hs))
    refine ⟨s,5,le_rfl,init.seq (Block.Eval.branchTrue (k:=2) hc body),
      by simpa [s,t] using hval,by simp [s,h,PowerToken.code],?_,?_⟩
    · intro i h₀ h41; simp [s,t,u,h₀,h41]
    · intro i h37; simp [s,t,u,h37]
  · have hq : ¬(x:ℚ)<0 := by exact_mod_cast h
    have ha : (x.natAbs:ℚ) = (x:ℚ) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun z : ℤ => (z:ℚ)) (Int.natAbs_of_nonneg (le_of_not_gt h))
    let s := u.putIndex 37 3
    have hs : s.AllData P := hu
    have hc : (Cond.scalarLT 0 41).test u=false := by simp [Cond.test,u,hx,hq]
    refine ⟨s,3,by decide,init.seq (Block.Eval.branchFalse (k:=1) hc (Block.Eval.op_addrConst u 37 3 hu hs)),
      by simp [s,u,ha,hx],by simp [s,h,PowerToken.code],?_,?_⟩
    · intro i _ h41; simp [s,u,h41]
    · intro i h37; simp [s,u,h37]

/-- Append one token from address register src at the cursor in address
register 34 and increment that cursor. -/
def appendPowerMarker (src : ℕ) : Block := .seq (.op (.addrStore 34 src)) (.op (.incr 34 34))

theorem appendPowerMarker_spec (m : Memory ℚ) (src : ℕ) {P : ℚ → Prop}
    (hm : m.AllData P) (hp : 34 < m.index 34) :
    ∃ s, Block.Eval (Memory.AllData P) (appendPowerMarker src) m 2 s ∧
      s.index 34=m.index 34+1 ∧ s.index (m.index 34)=m.index src ∧
      (∀ i, i ≠ 34 → i ≠ m.index 34 → s.index i=m.index i) ∧ s.data = m.data := by
  let t := m.putIndex (m.index 34) (m.index src)
  let s := t.putIndex 34 (t.index 34+1)
  have ht : t.AllData P := hm
  have hs : s.AllData P := ht
  refine ⟨s,(Block.Eval.op_addrStore m 34 src hm ht).seq (Block.Eval.op_incr t 34 34 ht hs),
    by simp [s,t,show 34 ≠ m.index 34 by omega],
    by simp [s,t,show m.index 34 ≠ 34 by omega],?_,rfl⟩
  intro i h34 hptr
  simp [s,t,h34,hptr]

end Compression
end LinearProgramming
end Optimization
end OAI
