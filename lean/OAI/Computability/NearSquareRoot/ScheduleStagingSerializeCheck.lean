import OAI.Computability.NearSquareRoot.ScheduleStagingSerializeRewind

/-! # Fixed-split eligibility and early rejection -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingSerialize

open IntegerMultiplication TM Code Bits CommonAlphabet
open CommonAlphabet.Expand (cfg pair)
open ChunkControl (Driver)

variable (d : Driver) (k : ℕ)

private theorem threshold_part (x y : Word) (j : ℕ) (hr : j ≤ 2^k) (hn : j ≤ x.length) :
    Trace (advance (rule d k)) (initial d k x y) j
      (cfg (checkAt k j) j 0 (content d (raw x y)) (content d [])) := by
  let F (i : ℕ) := cfg (checkAt k i) i 0 (content d (raw x y)) (content d [])
  have h := Expand.steps (rule d k) F j fun i hi => by
    have il : i < x.length := by omega
    have ir : i < 2^k := by omega
    have get : content d (raw x y) i = put d (.bit x[i]) := by
      simp [content_at,raw,List.getElem?_append_left (by simpa using il : i < (x.map Ltr.bit).length),
        List.getElem?_eq_getElem il]
    have hpc : checkAt k i = .check ⟨i,ir⟩ := dite_eq_left ir
    have one := Expand.move (rule d k) (checkAt k i) (checkAt k (i+1)) i 0
      (content d (raw x y)) (content d []) .right .stay (by simp [hpc,rule,pair,get])
    simpa only [F,Move.shift,Nat.cast_succ,add_zero] using one
  simpa only [F,initial,start,tapes,cfg,Nat.cast_zero,at_zero] using h

theorem check (x y : Word) (fits : 2^k ≤ x.length) :
    Trace (advance (rule d k)) (initial d k x y) (2*2^k+2) (cursor d (headerAt k 0) [] (raw x y) []) := by
  let s := raw x y
  have first := threshold_part d k x y (2^k) le_rfl fits
  have done : checkAt k (2^k) = .turn := dite_eq_right (lt_irrefl _)
  rw [done] at first
  have pivot := Expand.move (rule d k) .turn .back ((2^k:ℕ):ℤ) 0 (content d s) (content d [])
    .left .stay rfl
  have rewind := rewind_in d k true s [] 0 (2^k) (fits.trans (by simp [s,raw]))
  have back := (Trace.single (by simpa only [Move.shift,sub_eq_add_neg,add_zero] using pivot :
    advance (rule d k) _ = some (cfg .back (((2^k:ℕ):ℤ)-1) 0 (content d s) (content d [])))).trans rewind
  convert first.trans back using 1 <;> first | rfl | omega

def rejected (x y : Word) : Config (StagingProtection.Cell d) (Phase k) Bool :=
  cfg .rejected x.length 0 (content d (raw x y)) (content d [])

/-- Oversize exponents incur only a scan through the left operand and its
delimiter. The fresh output is still entirely blank at the rejecting halt. -/
theorem reject (x y : Word) (oversize : x.length < 2^k) :
    Trace (advance (rule d k)) (initial d k x y) (x.length+1) (rejected d k x y) ∧
      advance (rule d k) (rejected d k x y) = none := by
  have first := threshold_part d k x y x.length oversize.le le_rfl
  have hpc : checkAt k x.length = .check ⟨_,oversize⟩ := dite_eq_left oversize
  have get : content d (raw x y) x.length = put d .sep := by
    simpa only [raw,List.length_map] using content_next d (x.map Ltr.bit) (y.map Ltr.bit) .sep
  have last := Expand.move (rule d k) (checkAt k x.length) .rejected x.length 0
    (content d (raw x y)) (content d []) .stay .stay (by simp [hpc,rule,pair,get])
  exact ⟨first.trans (.single (by simpa only [rejected,Move.shift,add_zero] using last)),rfl⟩

end StagingSerialize

end NearSquareRoot
end Computability
end OAI
