import OAI.Optimization.LinearProgramming.RAM.RAMDatum
import Mathlib.Tactic.SplitIfs

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Block RAM.Tape

namespace JointRAM

/-- The fixed RAM interface stores `m,d,src,dst,row,col,rows,cols,cursor` in registers 0–8. -/
abbrev Env := Fin 9 → Nat

private def ifEq (x y : AddressTerm 9) (yes no : DatumTerm 9) : DatumTerm 9 :=
  .lt x y no (.lt y x no yes)

private theorem ifEq_value (x y : AddressTerm 9) (yes no : DatumTerm 9) (e : Env) :
    (ifEq x y yes no).value e = if x.value e = y.value e then yes.value e else no.value e := by
  simp only [ifEq, DatumTerm.value]
  split_ifs <;> first | rfl | omega

/-- A fixed finite branch tree, independent of either dimension or the input coefficients. -/
def entry : DatumTerm 9 :=
  let m : AddressTerm 9 := .reg 0
  let d : AddressTerm 9 := .reg 1
  let r : AddressTerm 9 := .reg 4
  let j : AddressTerm 9 := .reg 5
  .lt j (d+m)
    (.lt r m
      (.lt j d (.word (r*d+j) false) .zero)
      (.lt r (m+m)
        (ifEq j (d+(r-m)) .negOne .zero)
        (.lt r (m+m+d)
          (.lt j d .zero (.word ((j-d)*d+(r-(m+m))) false))
          (.lt r (m+m+d+d)
            (.lt j d .zero (.word ((j-d)*d+(r-(m+m+d))) true))
            (.lt j d (.word (m*d+m+j) true) (.word (m*d+(j-d)) false))))))
    (.lt r m (.word (m*d+r) false)
      (.lt r (m+m) .zero
        (.lt r (m+m+d) (.word (m*d+m+(r-(m+m))) false)
          (.lt r (m+m+d+d) (.word (m*d+m+(r-(m+m+d))) true) .zero))))

/-- The exact tagged source or literal selected by the address code. -/
theorem entry_value (e : Env) : entry.value e = jointDatum (e 0) (e 1) (e 4) (e 5) := by
  simp only [entry,DatumTerm.value,ifEq_value,AddressTerm.value,AddressOp.value,jointDatum]
  rfl

/-- Evaluate, store at the streaming output cursor, and advance the cursor. -/
def emit : Block := .seq (entry.code 2 12)
  (.seq (.op (.store 8 0)) (.op (.incr 8 8)))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

/-- Exact data/index frames of one coefficient write. All scalar registers including
scratch satisfy the scalar predicate under every instruction. -/
theorem emit_correct (m : Memory K) (hs : Good P m) (h0 : P 0) (h1 : P (-1))
    (hneg : ∀ q, P q → P (-q)) (hz : m.data 1 = 0) :
    ∃ k t, Eval (Good P) emit m k t ∧ k ≤ entry.cost (fun i : Fin 9 => m.index i) 2 + 2 ∧
      (∀ j, j ≠ 0 → j ≠ m.index 8 → t.data j = m.data j) ∧
      (∀ i < 12, i ≠ 8 → t.index i = m.index i) ∧ t.index 8 = m.index 8 + 1 ∧
      t.data (m.index 8) = (jointDatum (m.index 0) (m.index 1) (m.index 4) (m.index 5)).read
        (fun j => m.data (m.index 2 + j)) := by
  let env : Env := fun i => m.index i
  obtain ⟨k,s,he,hk,hds,hfs,hv⟩ := entry.correct 2 env 12 m (by decide) (fun _ => rfl) hs h0 h1 hneg hz
  have h8 : s.index 8 = m.index 8 := hfs 8 (by decide)
  let z := s.putData (s.index 8) (s.data 0)
  have gz : Good P z := by
    intro i
    by_cases hi : i = s.index 8
    · simpa [z, Memory.putData,hi] using he.safe_end 0
    · simpa [z, Memory.putData, hi] using he.safe_end i
  have st : Eval (Good P) (.op (.store 8 0)) s 1 z := .op he.safe_end gz (fun _ => rfl)
  refine ⟨_,_,.seq he (.seq st (eval_incr z gz 8 8)), (Nat.add_le_add_right hk 2), ?_, ?_, ?_, ?_⟩
  · intro i hne hcursor
    change Function.update s.data (s.index 8) (s.data 0) i = _
    rw [Function.update_of_ne (fun hi => hcursor (hi.trans h8)),hds i hne]
  · intro i hi hne
    exact (getPutDifferent z hne).trans (hfs i hi)
  · simpa [z, Memory.putIndex, Memory.putData] using h8
  · change Function.update s.data (s.index 8) (s.data 0) (m.index 8) = _
    rw [h8,Function.update_self,hv,entry_value]
    rfl

/-- All signed offsets selected by in-range matrix/RHS coordinates address an actual
input entry. This includes the last equality row and both transposed blocks. -/
theorem source_in_bounds {m d r j k : Nat} {neg : Bool} (hr : r < 2*m+2*d+1)
    (hj : j ≤ d+m) (h : jointDatum m d r j = .source k neg) : k < m*d+m+d := by
  have hA (i x : Nat) (hi : i < m) (hx : x < d) : i*d+x < m*d := by
    have hle := Nat.mul_le_mul_right d (show i+1 ≤ m by omega)
    rw [Nat.add_mul] at hle
    omega
  unfold jointDatum at h
  split_ifs at h with cj r1 j1 r2 je r3 j3 r4 j4 j5 r1 r2 r3 r4 <;>
    cases h <;> first | omega | (apply Nat.lt_of_lt_of_le (hA _ _ (by omega) (by omega)); omega)

end JointRAM
end PrimalDual
end LinearProgramming
end Optimization
end OAI
