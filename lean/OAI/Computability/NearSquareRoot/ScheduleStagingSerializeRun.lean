import OAI.Computability.NearSquareRoot.ScheduleStagingSerializeBody
import OAI.Computability.NearSquareRoot.ScheduleStagingSerializeCheck
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSpace

/-! # End-to-end bounds for installing a raw input pair -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingSerialize

open IntegerMultiplication TM Code Bits CommonAlphabet
open CommonAlphabet.Expand (cfg pair)
open ChunkControl (Driver)
open ChunkTask (Input)

variable (d : Driver)

/-- From raw input and a completely blank destination, produce exactly the
serialized controller register with both heads restored to the origin. -/
theorem run (p : Input) :
    ∃ t ≤ 64*(p.n+1), Trace (advance (rule d p.k)) (initial d p.k p.x p.y) t (ready d p) ∧
      advance (rule d p.k) (ready d p) = none := by
  let k := p.k
  let left := p.x.map Ltr.bit
  let right := p.y.map Ltr.bit
  let s := (left++[.sep])++right
  let h := header k
  let pre := ((h++pairs p.x)++[.bit false])++pairs p.y
  let output := pre++[.bit false]
  have source : s = raw p.x p.y := by simp [s,raw,left,right,List.append_assoc]
  have target : output = ChunkPhases.input p := by
    rw [input_shape]
    simp [output,pre,h,k,List.append_assoc,← pairs_term]
  have first := check d k p.x p.y p.fits
  have head := emit_header d k (raw p.x p.y)
  have xrun := word_trace d k p.x [] (.sep::right) h
  simp only [List.nil_append] at xrun
  have sep := sep_step d k left right (h++pairs p.x)
  have yrun := word_trace d k p.y (left++[.sep]) [] ((h++pairs p.x)++[.bit false])
  simp only [List.append_nil] at yrun
  have e := end_step d k s pre
  have forward := ((((first.trans head).trans xrun).trans (.single sep)).trans yrun).trans (.single e)
  have ri := rewind_in d k false s output pre.length s.length le_rfl
  have ro := rewind_out d k s output output.length le_rfl
  have pos : ((output.length : ℤ)-1) = ↑pre.length := by simp [output]
  rw [pos] at ro
  have all := (forward.trans ri).trans ro
  have last : cfg (.ready : Phase k) 0 0 (content d s) (content d output) = ready d p := by
    simp only [cfg,source,target,at_zero,ready,tapes]
  rw [last] at all
  refine ⟨_,?_,all,rfl⟩
  have hk : k ≤ p.n := (Nat.le_of_lt Nat.lt_two_pow_self).trans p.fits
  have hs : s.length = 2*p.n+1 := by simp [s,left,right,p.same,Input.n]; omega
  have ho : output.length ≤ 32*(p.n+1) := target ▸ ChunkPhases.input_length p
  have fit : 2^k ≤ p.n := p.fits
  simp only [header_length,p.same,Input.n] at *
  omega

/-- At every time cutoff the two heads occupy a common linear interval,
including attempts rejected for an oversize exponent before any writing. -/
theorem prefix_within (k : ℕ) (x y : Word) (same : y.length = x.length) {j : ℕ} {z}
    (pref : Trace (advance (rule d k)) (initial d k x y) j z) (i : Bool) :
    -((64*(x.length+1) : ℕ) : ℤ) ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ 64*(x.length+1) := by
  have time : j ≤ 64*(x.length+1) := by
    by_cases fits : 2^k ≤ x.length
    · let p : Input := ⟨x,y,k,same,fits⟩
      obtain ⟨t,ht,tr,halt⟩ := run d p
      exact (Uniform.before_halt tr halt pref).trans ht
    · obtain ⟨tr,halt⟩ := reject d k x y (by omega)
      exact (Uniform.before_halt tr halt pref).trans (by omega)
  have pos : ((initial d k x y).tape i).pos = 0 := by cases i <;> rfl
  obtain ⟨lo,hi⟩ := head_excursion pref i
  rw [pos] at lo hi
  omega

theorem visited (k n : ℕ) (x y : Word) (same : y.length = x.length) :
    VisitsAtMost (rule d k) (initial d k x y) n (258*(x.length+1)) := by
  have space := visitsAtMost_of_common_fence (m:=rule d k) (init:=initial d k x y) (steps:=n)
    (-((64*(x.length+1) : ℕ) : ℤ)) ((64*(x.length+1) : ℕ) : ℤ)
    (fun _ _ _ sub i => prefix_within d k x y same sub i)
  obtain ⟨cells,num,all⟩ := space
  refine ⟨cells,num.trans ?_,all⟩
  rw [Fintype.card_bool]
  omega

end StagingSerialize

end NearSquareRoot
end Computability
end OAI
